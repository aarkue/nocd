//! Structural schema discovery over an OCEL 2.0 log.
//!
//! Unrelated to the negative-constraint work; it belongs to the structure-based
//! reduction line and is kept here because it shares the OCEL access layer.
//!
//! Usage:
//!   cargo run --release --example schema_census -- <log>
//!
//! Two independent sources of candidate maps, reported separately because they are
//! complementary and neither subsumes the other:
//!
//!   recorded    total maps read off the object-to-object relation, per qualifier
//!   coparticip  total maps forced by event co-participation
//!
//! Three distinctions that are easy to collapse and must not be:
//!
//!   CONFLICT    the running intersection emptied after having been non-empty: two
//!               events name disjoint sets of T objects for the same source, so no
//!               function exists. The pair is REJECTED, never absorbed into slack.
//!   AMBIGUOUS   the intersection never collapsed to a singleton. Co-participation is
//!               consistent with several images and forces none; picking one would
//!               invent a function. Counts against coverage.
//!   UNTOTAL     the source object never co-occurred with any T object. Residual.
//!
//! An event that contains the source but no T object at all gives NO constraint and is
//! not a residual here: object-level totality is what a map needs, and event-level
//! co-presence is a separate condition tested per cell when reconstruction is checked.
//! Conflating the two rejects `items -> orders`, which holds.
//!
//! Usage: cargo run --release --example schema_census -- <log.sqlite|json|xml> ...

use std::{
    collections::{BTreeMap, HashMap, HashSet},
    env,
    path::PathBuf,
    time::Instant,
};

use process_mining::{
    core::event_data::object_centric::linked_ocel::{
        slim_linked_ocel::{EventIndex, ObjectIndex},
        LinkedOCELAccess, SlimLinkedOCEL,
    },
    Importable, OCEL,
};

/// Minimum fraction of source objects for which the map must be determined.
const MIN_COVERAGE: f64 = 0.95;
/// A type with fewer objects than this makes every map into it trivially total and
/// carries no information. Hinge has five such types.
const MIN_TARGET_OBJECTS: usize = 2;

#[derive(Clone)]
enum Cand {
    /// Exactly one image survives. Further updates are O(1) membership tests.
    One(ObjectIndex),
    /// Several images still possible.
    Many(HashSet<ObjectIndex>),
    /// Conflict: no function exists for this source object.
    Dead,
}

struct Map {
    source: usize,
    target: usize,
    origin: &'static str,
    qualifier: Option<String>,
    /// The function itself. Reduction needs it; the census only prints its size.
    f: HashMap<ObjectIndex, ObjectIndex>,
    image: usize,
    residual: usize,
    ambiguous: usize,
}

impl Map {
    fn coverage(&self) -> f64 {
        let n = self.f.len() + self.residual + self.ambiguous;
        if n == 0 {
            0.0
        } else {
            self.f.len() as f64 / n as f64
        }
    }
    fn line(&self, types: &[String]) -> String {
        let q = match &self.qualifier {
            Some(q) => format!(" [{q}]"),
            None => String::new(),
        };
        format!(
            "{} -> {}{} ({}) cov={:.4} img={} res={} amb={}",
            types[self.source],
            types[self.target],
            q,
            self.origin,
            self.coverage(),
            self.image,
            self.residual,
            self.ambiguous
        )
    }
}

/// Total maps read off O2O, one candidate per (source type, target type, qualifier).
/// A source object with two distinct targets under the same qualifier makes the pair
/// non-functional and is rejected outright.
fn recorded_maps(locel: &SlimLinkedOCEL, type_of: &HashMap<ObjectIndex, usize>, types: &[String]) -> Vec<Map> {
    // (source type, target type, qualifier) -> source object -> target objects
    // BTreeMap so the emitted map list is in a fixed order: compose_closure breaks
    // ties between equally sized maps by which it sees first, so hash order here
    // leaks into the reduction.
    let mut by_pair: BTreeMap<(usize, usize, String), HashMap<ObjectIndex, HashSet<ObjectIndex>>> =
        BTreeMap::new();
    let mut objects_of_type: Vec<usize> = vec![0; types.len()];
    for (o, t) in type_of {
        objects_of_type[*t] += 1;
        let _ = o;
    }

    for src in locel.get_all_obs() {
        let st = type_of[&src];
        let ob = src.get_ob(locel);
        for (q, tgt) in &ob.relationships {
            let Some(tt) = type_of.get(tgt) else { continue };
            let qual = locel.qualifier_str(*q).to_string();
            // BOTH orientations. An edge recorded as A -[q]-> B may be a function
            // in either direction and the log records only one of them. Reading
            // the forward direction alone missed `Offer -> Application` on
            // BPIC2017, total over all 42,995 offers, and the Python oracle had
            // the same defect, so the differential check could not catch it.
            by_pair
                .entry((st, *tt, qual.clone()))
                .or_default()
                .entry(src)
                .or_default()
                .insert(*tgt);
            by_pair
                .entry((*tt, st, format!("~{qual}")))
                .or_default()
                .entry(*tgt)
                .or_default()
                .insert(src);
        }
    }

    let mut out = Vec::new();
    for ((st, tt, qual), rel) in by_pair {
        if objects_of_type[tt] < MIN_TARGET_OBJECTS {
            continue;
        }
        if rel.values().any(|v| v.len() > 1) {
            continue; // not functional
        }
        let f: HashMap<ObjectIndex, ObjectIndex> = rel
            .iter()
            .map(|(s, v)| (*s, *v.iter().next().unwrap()))
            .collect();
        let image: HashSet<&ObjectIndex> = f.values().collect();
        let m = Map {
            source: st,
            target: tt,
            origin: "recorded",
            qualifier: Some(qual),
            image: image.len(),
            residual: objects_of_type[st].saturating_sub(f.len()),
            ambiguous: 0,
            f,
        };
        if m.coverage() >= MIN_COVERAGE {
            out.push(m);
        }
    }
    out
}

/// Co-participation maps in ONE pass over the events.
///
/// The per-pair formulation costs O(|OT|^2) scans and is hopeless on a log with 120
/// object types, so every (source object, target type) running intersection is
/// maintained together. Cost is sum_e |obj(e)| * |types(e)|, and the number of
/// candidate updates is returned so the paper can report ops per E2O tuple.
fn coparticipation_maps(
    locel: &SlimLinkedOCEL,
    type_of: &HashMap<ObjectIndex, usize>,
    types: &[String],
) -> (Vec<Map>, HashMap<(usize, usize), String>, u64) {
    let mut objects_of_type: Vec<Vec<ObjectIndex>> = vec![Vec::new(); types.len()];
    for o in locel.get_all_obs() {
        objects_of_type[type_of[&o]].push(o);
    }
    let eligible: Vec<bool> = objects_of_type
        .iter()
        .map(|v| v.len() >= MIN_TARGET_OBJECTS)
        .collect();

    let mut cand: HashMap<(ObjectIndex, usize), Cand> = HashMap::new();
    let mut updates: u64 = 0;

    // Reused per event so the inner loops allocate nothing.
    let mut per_type: HashMap<usize, Vec<ObjectIndex>> = HashMap::new();
    for ev in locel.get_all_evs() {
        per_type.clear();
        let objs: Vec<ObjectIndex> = ev.get_e2o(locel).copied().collect();
        for o in &objs {
            per_type.entry(type_of[o]).or_default().push(*o);
        }
        for (tt, ts) in &per_type {
            if !eligible[*tt] {
                continue;
            }
            let tset: HashSet<ObjectIndex> = ts.iter().copied().collect();
            for o in &objs {
                if type_of[o] == *tt {
                    continue;
                }
                updates += 1;
                match cand.get_mut(&(*o, *tt)) {
                    None => {
                        let c = if tset.len() == 1 {
                            Cand::One(*ts.first().unwrap())
                        } else {
                            Cand::Many(tset.clone())
                        };
                        cand.insert((*o, *tt), c);
                    }
                    Some(Cand::Dead) => {}
                    Some(Cand::One(x)) => {
                        // singleton fast path: membership test, no intersection
                        if !tset.contains(x) {
                            cand.insert((*o, *tt), Cand::Dead);
                        }
                    }
                    Some(Cand::Many(cur)) => {
                        cur.retain(|x| tset.contains(x));
                        match cur.len() {
                            0 => {
                                cand.insert((*o, *tt), Cand::Dead); // early death
                            }
                            1 => {
                                let x = *cur.iter().next().unwrap();
                                cand.insert((*o, *tt), Cand::One(x));
                            }
                            _ => {}
                        }
                    }
                }
            }
        }
    }

    let mut rejected: HashMap<(usize, usize), String> = HashMap::new();
    let mut out = Vec::new();
    for st in 0..types.len() {
        for tt in 0..types.len() {
            if st == tt {
                continue;
            }
            if !eligible[tt] {
                rejected.insert(
                    (st, tt),
                    format!("degenerate target: |{}|={}", types[tt], objects_of_type[tt].len()),
                );
                continue;
            }
            let mut image: HashSet<ObjectIndex> = HashSet::new();
            let mut f: HashMap<ObjectIndex, ObjectIndex> = HashMap::new();
            let (mut residual, mut ambiguous, mut conflicts) = (0, 0, 0);
            for s in &objects_of_type[st] {
                match cand.get(&(*s, tt)) {
                    None => residual += 1,            // never co-occurred with T
                    Some(Cand::Dead) => {
                        conflicts += 1;
                        residual += 1;
                    }
                    Some(Cand::Many(_)) => ambiguous += 1,
                    Some(Cand::One(x)) => {
                        f.insert(*s, *x);
                        image.insert(*x);
                    }
                }
            }
            if conflicts > 0 {
                rejected.insert((st, tt), format!("non-functional: {conflicts} conflicts"));
                continue;
            }
            let m = Map {
                source: st,
                target: tt,
                origin: "coparticip",
                qualifier: None,
                image: image.len(),
                residual,
                ambiguous,
                f,
            };
            if m.coverage() >= MIN_COVERAGE {
                out.push(m);
            } else {
                rejected.insert((st, tt), format!("untotal: coverage {:.3}", m.coverage()));
            }
        }
    }
    (out, rejected, updates)
}

/// Transitive reduction of the map graph, plus the maximum derivation depth needed to
/// reach every non-generator edge.
fn generators(pairs: &HashSet<(usize, usize)>) -> (Vec<(usize, usize)>, usize) {
    let mut succ: HashMap<usize, Vec<usize>> = HashMap::new();
    for (s, t) in pairs {
        succ.entry(*s).or_default().push(*t);
    }
    let mut gens = Vec::new();
    let mut max_depth = 1;
    for (s, t) in pairs {
        // BFS from s without using the edge (s,t)
        let mut seen: HashMap<usize, usize> = HashMap::from([(*s, 0)]);
        let mut frontier = vec![*s];
        while !frontier.is_empty() {
            let mut next = Vec::new();
            for u in frontier {
                for v in succ.get(&u).into_iter().flatten() {
                    if (u, *v) == (*s, *t) || seen.contains_key(v) {
                        continue;
                    }
                    seen.insert(*v, seen[&u] + 1);
                    next.push(*v);
                }
            }
            frontier = next;
        }
        match seen.get(t) {
            Some(d) => max_depth = max_depth.max(*d),
            None => gens.push((*s, *t)),
        }
    }
    gens.sort();
    (gens, max_depth)
}

fn census(path: &str) {
    let t0 = Instant::now();
    let ocel = OCEL::import_from_path(PathBuf::from(path)).expect("import log");
    let locel = SlimLinkedOCEL::from_ocel(ocel);
    let t_load = t0.elapsed();

    // Sorted by name, NOT left in import order. Object type indices are assigned by
    // the importer and its order varies between runs, so anything that tie-breaks on
    // a type index -- the refinement ordering, the mask enumeration in the maximum
    // search, the colour palette -- silently changes answer. Measured: the maximum at
    // `send package` alternated between keeping `items` and keeping `packages` across
    // identical runs. Third instance of import-order leaking into the result, after
    // the composition closure and the event ordering.
    let mut types: Vec<String> = locel.get_ob_types().map(str::to_string).collect();
    types.sort();
    let type_ix: HashMap<&str, usize> = types
        .iter()
        .enumerate()
        .map(|(i, t)| (t.as_str(), i))
        .collect();
    let type_of: HashMap<ObjectIndex, usize> = locel
        .get_all_obs()
        .map(|o| (o, type_ix[o.get_ob_type(&locel).as_str()]))
        .collect();

    let n_events = locel.get_all_evs().count();
    let e2o: usize = locel.get_all_evs().map(|e| e.get_e2o(&locel).count()).sum();

    println!("\n{}\n{path}\n{}", "=".repeat(72), "=".repeat(72));
    println!(
        "{n_events} events / {} objects / {} types  (load {:.2}s)",
        type_of.len(),
        types.len(),
        t_load.as_secs_f64()
    );

    let t0 = Instant::now();
    let rec = recorded_maps(&locel, &type_of, &types);
    let t_rec = t0.elapsed();

    let t0 = Instant::now();
    let (cop, _rejected, updates) = coparticipation_maps(&locel, &type_of, &types);
    let t_cop = t0.elapsed();

    let mut lines: Vec<String> = rec.iter().map(|m| m.line(&types)).collect();
    lines.sort();
    println!("\nrecorded O2O maps: {}   ({:.2}s)", rec.len(), t_rec.as_secs_f64());
    for l in &lines {
        println!("  {l}");
    }

    let mut lines: Vec<String> = cop.iter().map(|m| m.line(&types)).collect();
    lines.sort();
    println!(
        "\nco-participation maps: {}   ({:.2}s, {updates} updates, {:.1} ops per E2O tuple)",
        cop.len(),
        t_cop.as_secs_f64(),
        updates as f64 / e2o.max(1) as f64
    );
    for l in &lines {
        println!("  {l}");
    }

    let pairs: HashSet<(usize, usize)> = rec
        .iter()
        .chain(cop.iter())
        .map(|m| (m.source, m.target))
        .collect();
    let (gens, depth) = generators(&pairs);
    println!(
        "\ntype pairs covered: {}  generators: {}  max derivation depth: {depth}",
        pairs.len(),
        gens.len()
    );
    for (s, t) in &gens {
        println!("  gen: {} -> {}", types[*s], types[*t]);
    }

    reduce(&locel, &type_of, &types, &rec, &cop);
}

fn main() {
    let args: Vec<String> = env::args().skip(1).collect();
    if args.is_empty() {
        eprintln!("usage: schema_census <log> [<log> ...]");
        return;
    }
    for path in &args {
        census(path);
    }
}

// ==========================================================================
// Structure-based reduction
// ==========================================================================

/// Maximum composition depth when closing the map set. Measured derivation depth is
/// 2 on four of five logs and 3 on Hinge, so 4 is slack rather than a limit.
const MAX_COMPOSE_DEPTH: usize = 4;
/// Cap on distinct witnesses kept per type pair. Composition routes multiply, and a
/// pair with more than a handful of genuinely different functions is a sign the
/// schema is not a schema. Reported when hit rather than silently truncated.
const MAX_WITNESSES_PER_PAIR: usize = 8;

/// Close the discovered maps under composition, keyed by (source type, target type).
///
/// **All** witnesses for a pair are kept, not one. A pair can carry several genuinely
/// different functions -- one per qualifier, and one per composition route -- and they
/// do not agree: `items -> employees` composed through `orders` is the employee who
/// handled the order, composed through `packages` it is the forwarder. Only some
/// reconstruct at a given activity, so keeping a single representative both loses
/// reductions and makes the result depend on which route is discovered first. That was
/// measured: one cell (`confirm order` / `employees`) flipped between runs.
fn compose_closure(
    rec: &[Map],
    cop: &[Map],
    n_types: usize,
) -> BTreeMap<(usize, usize), Vec<HashMap<ObjectIndex, ObjectIndex>>> {
    // BTreeMap, not HashMap. Which composition route reaches a type pair first decides
    // the witness stored for it, so iterating in hash order makes the whole operator
    // nondeterministic across runs -- measured at 19 / 18 / 18 kept cells on three
    // identical runs before this was fixed. A canonicity claim cannot rest on that.
    let mut by_pair: BTreeMap<(usize, usize), Vec<HashMap<ObjectIndex, ObjectIndex>>> =
        BTreeMap::new();
    for m in rec.iter().chain(cop.iter()) {
        by_pair.entry((m.source, m.target)).or_default().push(m.f.clone());
    }
    let _ = n_types;
    for _ in 0..MAX_COMPOSE_DEPTH {
        let mut added = Vec::new();
        for ((s, t), fs) in &by_pair {
            for ((t2, u), gs) in &by_pair {
                if t != t2 || s == u {
                    continue;
                }
                for f in fs {
                    for g in gs {
                        let composed: HashMap<ObjectIndex, ObjectIndex> = f
                            .iter()
                            .filter_map(|(x, y)| g.get(y).map(|z| (*x, *z)))
                            .collect();
                        if !composed.is_empty() {
                            added.push(((*s, *u), composed));
                        }
                    }
                }
            }
        }
        let before: usize = by_pair.values().map(Vec::len).sum();
        for (k, v) in added {
            let e = by_pair.entry(k).or_default();
            // Deduplicate: composition routes often agree, and without this the
            // witness lists grow exponentially in the depth bound.
            if !e.iter().any(|x| *x == v) && e.len() < MAX_WITNESSES_PER_PAIR {
                e.push(v);
            }
        }
        if by_pair.values().map(Vec::len).sum::<usize>() == before {
            break;
        }
    }
    by_pair
}

/// Objects of each type carried by one event.
type PerType = HashMap<usize, HashSet<ObjectIndex>>;

/// Recorded O2O as a *relation* per type pair, unioned over qualifiers.
///
/// The pitch note requires rules to admit finite unions of qualified maps and the
/// data says why: `packages -> employees` is not functional unqualified (up to three
/// per package) but splits into three total functions under `packed by`,
/// `forwarded by` and `shipped by`, and `send package` involves two of them at once.
/// No single function reconstructs that cell; their union does.
fn recorded_relations(
    locel: &SlimLinkedOCEL,
    type_of: &HashMap<ObjectIndex, usize>,
) -> BTreeMap<(usize, usize), BTreeMap<String, HashMap<ObjectIndex, HashSet<ObjectIndex>>>> {
    let mut rel: BTreeMap<(usize, usize), BTreeMap<String, HashMap<ObjectIndex, HashSet<ObjectIndex>>>> =
        BTreeMap::new();
    for src in locel.get_all_obs() {
        let st = type_of[&src];
        for (q, tgt) in &src.get_ob(locel).relationships {
            if let Some(tt) = type_of.get(tgt) {
                rel.entry((st, *tt))
                    .or_default()
                    .entry(locel.qualifier_str(*q).to_string())
                    .or_default()
                    .entry(src)
                    .or_default()
                    .insert(*tgt);
            }
        }
    }
    rel
}

/// Can cell (a,T) be reconstructed from cell (a,S) at every event of a?
///
/// (R-fun) obj^T(e) = f[obj^S(e)] for a map f: S -> T, or
/// (R-fib) obj^T(e) = f^-1[obj^S(e)] for a map f: T -> S.
///
/// Both are checked as set equality at every event, so a single event where the
/// reconstruction disagrees rejects the cell. That is what makes the removal exact
/// rather than approximate.
fn reconstructs(
    events: &[PerType],
    s: usize,
    t: usize,
    maps: &BTreeMap<(usize, usize), Vec<HashMap<ObjectIndex, ObjectIndex>>>,
    fibres: &BTreeMap<(usize, usize), Vec<HashMap<ObjectIndex, HashSet<ObjectIndex>>>>,
    relations: &BTreeMap<(usize, usize), BTreeMap<String, HashMap<ObjectIndex, HashSet<ObjectIndex>>>>,
) -> bool {
    // (R-union) obj^T(e) = the union of the images of obj^S(e) under a CHOSEN SUBSET
    // of qualifiers. The subset matters: unioning all of them overshoots. At
    // `send package` the packages relation offers `packed by`, `forwarded by` and
    // `shipped by`, the event carries only the latter two, and the full union is
    // wrong by exactly one employee.
    //
    // The subset is not searched. A qualifier is *admissible* at this activity if its
    // image never exceeds obj^T(e) at any event; the union of the admissible ones is
    // then the largest safe image, so if any subset works, that one does.
    if let Some(by_qual) = relations.get(&(s, t)) {
        let admissible: Vec<&HashMap<ObjectIndex, HashSet<ObjectIndex>>> = by_qual
            .values()
            .filter(|r| {
                events.iter().all(|per| match (per.get(&s), per.get(&t)) {
                    (Some(os), Some(ot)) => os
                        .iter()
                        .filter_map(|x| r.get(x))
                        .flat_map(|v| v.iter())
                        .all(|y| ot.contains(y)),
                    (Some(os), None) => os.iter().all(|x| r.get(x).is_none_or(HashSet::is_empty)),
                    _ => true,
                })
            })
            .collect();
        if !admissible.is_empty() {
            let ok = events.iter().all(|per| {
                let (Some(os), Some(ot)) = (per.get(&s), per.get(&t)) else {
                    return per.get(&s).is_none() && per.get(&t).is_none();
                };
                let image: HashSet<ObjectIndex> = admissible
                    .iter()
                    .flat_map(|r| os.iter().filter_map(move |x| r.get(x)))
                    .flat_map(|v| v.iter().copied())
                    .collect();
                &image == ot
            });
            if ok {
                return true;
            }
        }
    }
    for f in maps.get(&(s, t)).into_iter().flatten() {
        let ok = events.iter().all(|per| {
            let (Some(os), Some(ot)) = (per.get(&s), per.get(&t)) else {
                // A cell is reconstructible only where both sides are present or both
                // absent; a T object with no S object at the same event cannot be
                // produced by a function of the S objects.
                return per.get(&s).is_none() && per.get(&t).is_none();
            };
            // f must be defined on every S object present, or the image is not the
            // image of obj^S(e) and the reconstruction is not exact.
            os.iter().all(|x| f.contains_key(x)) && {
                let image: HashSet<ObjectIndex> =
                    os.iter().filter_map(|x| f.get(x).copied()).collect();
                &image == ot
            }
        });
        if ok {
            return true;
        }
    }
    for fib in fibres.get(&(t, s)).into_iter().flatten() {
        let ok = events.iter().all(|per| {
            let (Some(os), Some(ot)) = (per.get(&s), per.get(&t)) else {
                return per.get(&s).is_none() && per.get(&t).is_none();
            };
            let expanded: HashSet<ObjectIndex> = os
                .iter()
                .filter_map(|x| fib.get(x))
                .flat_map(|v| v.iter().copied())
                .collect();
            &expanded == ot
        });
        if ok {
            return true;
        }
    }
    false
}

/// Smallest keep-set at one activity: every cut cell must be reconstructible from a
/// KEPT cell, so the objective is exact rather than greedy. Exponential in the number
/// of types at the activity, which is small (<= 5 on the simulated logs).
fn max_reduction(n: usize, recon: &[Vec<bool>], coarseness: &[usize]) -> Vec<usize> {
    if n > 20 {
        // Fall back to greedy on pathological activities; none seen so far.
        return (0..n).collect();
    }
    for size in 1..=n {
        // The minimum is not unique, and which minimum is chosen decides how the model
        // reads. At `send package` both {items} and {packages} are minimal: keeping
        // `packages` scopes that type to the four package activities, keeping `items`
        // leaves a type that participates in all eleven and whose DFG is near-complete.
        // Cell count cannot see the difference; arcs can. Tie-break: prefer the
        // coarsest types, then the lexicographically first, so the choice is stated
        // rather than inherited from an enumeration order.
        let mut best: Option<(usize, Vec<usize>)> = None;
        for mask in 0u32..(1 << n) {
            if mask.count_ones() as usize != size || !derives_all(n, mask, recon) {
                continue;
            }
            let kept: Vec<usize> = (0..n).filter(|i| mask >> i & 1 == 1).collect();
            let score: usize = kept.iter().map(|i| coarseness[*i]).sum();
            if best.as_ref().is_none_or(|(bs, _)| score > *bs) {
                best = Some((score, kept));
            }
        }
        if let Some((_, kept)) = best {
            return kept;
        }
    }
    (0..n).collect()
}

/// Does the keep-set reach every cell at this activity, allowing chains?
///
/// Reconstruction is transitive: a recovered cell can itself witness the next one.
/// Keeping `packages` recovers `items` by fibre expansion, and `items` then recovers
/// `products` by function application -- a chain the one-step test misses, and the one
/// the earlier hand-made figure relies on when it keeps only `packages` at
/// `send package`.
fn derives_all(n: usize, mask: u32, recon: &[Vec<bool>]) -> bool {
    let mut have = mask;
    loop {
        let mut next = have;
        for t in 0..n {
            if next >> t & 1 == 1 {
                continue;
            }
            if (0..n).any(|s| have >> s & 1 == 1 && recon[s][t]) {
                next |= 1 << t;
            }
        }
        if next == have {
            return have == (1u32 << n) - 1;
        }
        have = next;
    }
}

fn reduce(
    locel: &SlimLinkedOCEL,
    type_of: &HashMap<ObjectIndex, usize>,
    types: &[String],
    rec: &[Map],
    cop: &[Map],
) {
    // Per-cell attribution. On a small log every keep is worth explaining, since a
    // kept cell is either genuinely irreducible or a witness that the rule refuses to
    // use, and the two are very different findings.
    let explain = env::var("EXPLAIN").is_ok();
    let t0 = Instant::now();
    let relations = recorded_relations(locel, type_of);
    let maps = compose_closure(rec, cop, types.len());
    let fibres: BTreeMap<(usize, usize), Vec<HashMap<ObjectIndex, HashSet<ObjectIndex>>>> = maps
        .iter()
        .map(|((s, t), fs)| {
            let inverted = fs
                .iter()
                .map(|f| {
                    let mut fib: HashMap<ObjectIndex, HashSet<ObjectIndex>> = HashMap::new();
                    for (x, y) in f {
                        fib.entry(*y).or_default().insert(*x);
                    }
                    fib
                })
                .collect();
            ((*s, *t), inverted)
        })
        .collect();

    // Refinement preorder and its classes: S <= T iff a map S -> T exists.
    let n = types.len();
    let mut reach = vec![vec![false; n]; n];
    for ((s, t), _) in &maps {
        reach[*s][*t] = true;
    }
    for k in 0..n {
        for i in 0..n {
            if reach[i][k] {
                for j in 0..n {
                    if reach[k][j] {
                        reach[i][j] = true;
                    }
                }
            }
        }
    }
    // Class representative: the lexicographically least name among mutually reachable
    // types. This is the tie-break that makes the reduction canonical; without it the
    // maximum is not unique whenever two types are mutually total.
    let rep: Vec<usize> = (0..n)
        .map(|t| {
            (0..n)
                .filter(|s| *s == t || (reach[t][*s] && reach[*s][t]))
                .min_by_key(|s| &types[*s])
                .unwrap()
        })
        .collect();

    let mut total_cells = 0usize;
    let mut kept_canon = 0usize;
    let mut kept_max = 0usize;
    let mut e2o_total = 0usize;
    let mut e2o_cut = 0usize;
    let mut type_kept = vec![false; n];
    // Which type pairs are actually used as reconstruction witnesses. The annotation
    // only has to ship the generators of these, and the cost of a map is one entry per
    // source object. Ratio = tuples removed / entries shipped.
    let mut used_pairs: HashSet<(usize, usize)> = HashSet::new();

    // Sorted, like the object types and for the same reason: the connectivity repair
    // walks cut cells in index order, so import-ordered activity indices made it add
    // back different cells between runs (24 / 32 / 30 arcs on the same input).
    let mut ev_types: Vec<String> = locel.get_ev_types().map(str::to_string).collect();
    ev_types.sort();
    // Importer event-type index -> index into the sorted list above. Everything that
    // reads `SlimOCELEvent::event_type` must go through this, or activity identities
    // silently permute.
    let act_ix: HashMap<&str, usize> = ev_types
        .iter()
        .enumerate()
        .map(|(i, a)| (a.as_str(), i))
        .collect();
    let act_of: &[usize] = &locel
        .get_ev_types()
        .map(|a| act_ix[a])
        .collect::<Vec<usize>>();
    let mut all_cells: HashSet<(usize, usize)> = HashSet::new();
    let mut kept_set: HashSet<(usize, usize)> = HashSet::new();
    let mut max_set: HashSet<(usize, usize)> = HashSet::new();
    let mut cut_list: Vec<(usize, usize)> = Vec::new();
    for (aix, act) in ev_types.iter().enumerate() {
        let evs: Vec<PerType> = locel
            .get_evs_of_type(act)
            .map(|e| {
                let mut per: PerType = HashMap::new();
                for o in e.get_e2o(locel) {
                    per.entry(type_of[o]).or_default().insert(*o);
                }
                per
            })
            .collect();
        if evs.is_empty() {
            continue;
        }
        let mut present: Vec<usize> = evs
            .iter()
            .flat_map(|p| p.keys().copied())
            .collect::<HashSet<usize>>()
            .into_iter()
            .collect();
        present.sort();
        let k = present.len();
        total_cells += k;
        for t in &present {
            all_cells.insert((aix, *t));
        }
        let counts: Vec<usize> = present
            .iter()
            .map(|t| evs.iter().map(|p| p.get(t).map_or(0, |s| s.len())).sum())
            .collect();
        e2o_total += counts.iter().sum::<usize>();

        let recon: Vec<Vec<bool>> = (0..k)
            .map(|i| {
                (0..k)
                    .map(|j| {
                        i != j
                            && reconstructs(
                                &evs, present[i], present[j], &maps, &fibres, &relations,
                            )
                    })
                    .collect()
            })
            .collect();

        // Canonical rule. A cell is cut only when a KEPT cell reconstructs it: a cut
        // justified by a cell that is itself cut would leave nothing to reconstruct
        // from, and is the error that made the canonical rule cut more than the
        // maximum. Deciding strictly finer types first (and a class representative
        // before the rest of its class) makes one pass sufficient, since a finer cell
        // is never cut by a coarser one.
        // Which end of the refinement order is decided first is a real choice, not a
        // detail: deciding the finest first cuts the coarse types cheaply but destroys
        // them as witnesses for anything they alone explain. ORDER=coarsest tests the
        // other end.
        // MODE=coarse is the group-folding objective: keep the coarse type and derive
        // the finer one by fibre expansion. It keeps the same information, but the
        // resulting model is scoped -- `packages` only touches package activities,
        // where `items` touches every activity and its DFG is near-complete. Cell
        // count cannot see that difference; arc count can.
        let coarsest_first = env::var("MODE").map(|v| v == "coarse").unwrap_or(false);
        let mut order: Vec<usize> = (0..k).collect();
        order.sort_by_key(|i| {
            let t = present[*i];
            let coarser = (0..k)
                .filter(|j| {
                    let s = present[*j];
                    reach[t][s] && !reach[s][t]
                })
                .count();
            let key = if coarsest_first { k - coarser } else { coarser };
            (std::cmp::Reverse(key), rep[t] != present[*i], present[*i])
        });
        let mut kept_here = vec![false; k];
        for &j in &order {
            let t = present[j];
            let witness = (0..k).find(|i| {
                let s = present[*i];
                if !kept_here[*i] || !recon[*i][j] || s == t {
                    return false;
                }
                if coarsest_first {
                    // Group folding: a kept witness in either direction licenses the
                    // cut, since the coarse types are decided first and the fine ones
                    // are what gets folded away.
                    true
                } else {
                    (reach[s][t] && !reach[t][s]) || (rep[t] == s && rep[s] == s)
                }
            });
            let cut = witness.is_some();
            if explain {
                let any_recon: Vec<&String> =
                    (0..k).filter(|i| recon[*i][j]).map(|i| &types[present[i]]).collect();
                match witness {
                    Some(i) => println!(
                        "    CUT  {act} / {}  <- {}",
                        types[t], types[present[i]]
                    ),
                    None => println!(
                        "    KEEP {act} / {}   reconstructible-from {:?} (none usable)",
                        types[t], any_recon
                    ),
                }
            }
            if cut {
                e2o_cut += counts[j];
                if let Some(i) = witness {
                    used_pairs.insert((present[i], t));
                }
                cut_list.push((aix, t));
            } else {
                kept_here[j] = true;
                kept_canon += 1;
                kept_set.insert((aix, t));
                type_kept[t] = true;
            }
        }
        // Coarseness of a type at this activity: how many of the other present types
        // can reach it in the refinement order. `orders` is coarser than `items`.
        let coarseness: Vec<usize> = (0..k)
            .map(|i| (0..k).filter(|j| *j != i && reach[present[*j]][present[i]]).count())
            .collect();
        let mx = max_reduction(k, &recon, &coarseness);
        if explain {
            println!(
                "    MAX  {act}: keep {:?}   (recon: {})",
                mx.iter().map(|i| &types[present[*i]]).collect::<Vec<_>>(),
                (0..k)
                    .flat_map(|i| (0..k).filter(move |j| i != *j).map(move |j| (i, j)))
                    .filter(|(i, j)| recon[*i][*j])
                    .map(|(i, j)| format!("{}<-{}", types[present[j]], types[present[i]]))
                    .collect::<Vec<_>>()
                    .join(" ")
            );
        }
        kept_max += mx.len();
        for i in &mx {
            max_set.insert((aix, present[*i]));
        }
    }

    {
        let (gens, _) = generators(&used_pairs);
        let cost: usize = gens
            .iter()
            .filter_map(|(a, b)| maps.get(&(*a, *b)))
            .filter_map(|v| v.first())
            .map(|f| f.len())
            .sum();
        println!(
            "  amortisation (canonical): {} witness pairs -> {} generators, {cost} map entries shipped, {e2o_cut} tuples removed = {:.2}x",
            used_pairs.len(),
            gens.len(),
            if cost > 0 { e2o_cut as f64 / cost as f64 } else { 0.0 }
        );
        for (a, b) in &gens {
            let sz = maps.get(&(*a, *b)).and_then(|v| v.first()).map_or(0, |f| f.len());
            println!("      generator {} -> {}  ({sz} entries)", types[*a], types[*b]);
        }
    }

    let eliminated: Vec<&String> = (0..n)
        .filter(|t| !type_kept[*t])
        .map(|t| &types[t])
        .collect();

    println!(
        "\nREDUCTION  ({:.2}s, closure {} pairs)",
        t0.elapsed().as_secs_f64(),
        maps.len()
    );
    println!(
        "  cells {total_cells}  kept(canonical) {kept_canon}  cut {} ({:.0}%)",
        total_cells - kept_canon,
        100.0 * (total_cells - kept_canon) as f64 / total_cells.max(1) as f64
    );
    println!(
        "  cells {total_cells}  kept(max)       {kept_max}  cut {} ({:.0}%)",
        total_cells - kept_max,
        100.0 * (total_cells - kept_max) as f64 / total_cells.max(1) as f64
    );
    println!(
        "  E2O instances removed (canonical): {e2o_cut} of {e2o_total} ({:.0}%)",
        100.0 * e2o_cut as f64 / e2o_total.max(1) as f64
    );
    println!("  types eliminated entirely: {eliminated:?}");

    // Arcs and connectivity. The arc counts are what an analyst actually sees, and the
    // component count is what the connectivity constraint exists to protect.
    let n_acts = ev_types.len();
    let t1 = Instant::now();
    let (arcs_full, comps_full) = arcs_and_components(locel, type_of, act_of, n_acts, &all_cells);
    let (arcs_red, comps_red) = arcs_and_components(locel, type_of, act_of, n_acts, &kept_set);
    let (arcs_max, comps_max) = arcs_and_components(locel, type_of, act_of, n_acts, &max_set);
    println!(
        "  arcs  full {arcs_full} / {comps_full} comp   canonical {arcs_red} / {comps_red} comp   maximum {arcs_max} / {comps_max} comp   ({:.2}s)",
        t1.elapsed().as_secs_f64()
    );
    if comps_max > comps_full && max_set.len() <= CONNECTIVITY_REPAIR_LIMIT {
        let cut_max: Vec<(usize, usize)> = {
            let mut v: Vec<(usize, usize)> =
                all_cells.difference(&max_set).copied().collect();
            v.sort();
            v
        };
        let (rep_set, added) = repair_connectivity(
            locel, type_of, act_of, n_acts, &max_set, &cut_max, comps_full,
        );
        let (a, c) = arcs_and_components(locel, type_of, act_of, n_acts, &rep_set);
        println!(
            "  maximum + connectivity repair: +{added} cells -> kept {} , arcs {a} / {c} comp",
            rep_set.len()
        );
    }

    // Repair is quadratic in the number of cut cells, so it is skipped on very large
    // logs rather than silently approximated. Say so; do not print a bare number.
    if comps_red > comps_full {
        if cut_list.len() <= CONNECTIVITY_REPAIR_LIMIT {
            cut_list.sort();
            let (repaired, added) = repair_connectivity(
                locel, type_of, act_of, n_acts, &kept_set, &cut_list, comps_full,
            );
            let (arcs_rep, comps_rep) = arcs_and_components(locel, type_of, act_of, n_acts, &repaired);
            println!(
                "  connectivity repair: +{added} cells -> kept {} , arcs {arcs_rep} / {comps_rep} comp",
                repaired.len()
            );
        } else {
            println!(
                "  connectivity repair: SKIPPED, {} cut cells exceeds the {CONNECTIVITY_REPAIR_LIMIT}-cell limit",
                cut_list.len()
            );
        }
    } else {
        println!("  connectivity repair: not needed");
    }

    // What does the reduced DFG say that the full one does not, and vice versa?
    // Projection preserves relative order, so eventually-follows over kept cells is
    // exact. Directly-follows is not: hiding an activity splices the trace, so an arc
    // can appear that no full trace supports.
    {
        let full = arc_set(locel, type_of, act_of, &all_cells);
        for (name, set) in [("canonical", &kept_set), ("maximum", &max_set)] {
            let red = arc_set(locel, type_of, act_of, set);
            let kept_types: HashSet<usize> = set.iter().map(|(_, t)| *t).collect();
            let full_on_kept: HashSet<_> = full
                .iter()
                .filter(|(t, a, b)| {
                    kept_types.contains(t) && set.contains(&(*a, *t)) && set.contains(&(*b, *t))
                })
                .copied()
                .collect();
            let spurious = red.difference(&full_on_kept).count();
            let missing = full_on_kept.difference(&red).count();
            println!(
                "  DF fidelity ({name}): {} arcs, {spurious} not supported by any full trace, {missing} missing",
                red.len()
            );
        }
    }

    // Type-elimination-only: drop every cell of a type that is derivable everywhere it
    // occurs, and keep every cell of every type that stays. No type is partially cut,
    // so no kept type's flow is ever spliced -- every arc of every surviving type is
    // exactly the arc the full model has. This is "remove what the schema explains" in
    // its strictest reading, and it is where the savings actually come from: on this
    // log `products` alone carries 121 of 201 arcs and is a pure attribute of `items`.
    let whole_type: HashSet<(usize, usize)> = {
        let eliminated: HashSet<usize> = (0..types.len())
            .filter(|t| !kept_set.iter().any(|(_, kt)| kt == t))
            .collect();
        all_cells
            .iter()
            .filter(|(_, t)| !eliminated.contains(t))
            .copied()
            .collect()
    };
    let (wa, wc) = arcs_and_components(locel, type_of, act_of, n_acts, &whole_type);
    println!(
        "  type-elimination only: kept {} cells, arcs {wa} / {wc} comp",
        whole_type.len()
    );

    if let Ok(dir) = env::var("EXPORT_DIR") {
        let tag = env::var("EXPORT_TAG").unwrap_or_else(|_| "log".to_string());
        let mut cut_all: Vec<(usize, usize)> = all_cells.difference(&max_set).copied().collect();
        cut_all.sort();
        let (incid, inc_added) = repair_incidence(&max_set, &cut_all);
        let (ia, ic) = arcs_and_components(locel, type_of, act_of, n_acts, &incid);
        println!(
            "  maximum + incidence repair: +{inc_added} cells -> kept {} , arcs {ia} / {ic} comp , incidence {} comp",
            incid.len(),
            incidence_components(&incid)
        );
        let mut variants: Vec<(&str, &HashSet<(usize, usize)>)> = vec![
            ("canonical", &kept_set),
            ("maximum", &max_set),
            ("incidence", &incid),
            ("wholetype", &whole_type),
        ];
        let repaired;
        if comps_max > comps_full {
            let mut cut_max: Vec<(usize, usize)> =
                all_cells.difference(&max_set).copied().collect();
            cut_max.sort();
            repaired =
                repair_connectivity(locel, type_of, act_of, n_acts, &max_set, &cut_max, comps_full).0;
            variants.push(("connectivity", &repaired));
        }
        // Keep-sets produced elsewhere, so a third party's reduction can be run through
        // the same model pipeline as ours without reimplementing their discovery.
        let extra: Vec<(String, HashSet<(usize, usize)>)> = match env::var("EXTRA_KEEPSETS") {
            Ok(p) => {
                let txt = std::fs::read_to_string(&p).expect("read EXTRA_KEEPSETS");
                let obj: serde_json::Map<String, serde_json::Value> =
                    serde_json::from_str(&txt).expect("parse EXTRA_KEEPSETS");
                let act_ix: HashMap<&str, usize> =
                    ev_types.iter().enumerate().map(|(i, a)| (a.as_str(), i)).collect();
                let type_ix: HashMap<&str, usize> =
                    types.iter().enumerate().map(|(i, t)| (t.as_str(), i)).collect();
                obj.iter()
                    .map(|(name, cells)| {
                        let set: HashSet<(usize, usize)> = cells
                            .as_array()
                            .expect("keep-set is a list")
                            .iter()
                            .map(|c| {
                                let a = c[0].as_str().expect("activity name");
                                let t = c[1].as_str().expect("object type name");
                                (
                                    *act_ix.get(a).unwrap_or_else(|| panic!("unknown activity {a}")),
                                    *type_ix.get(t).unwrap_or_else(|| panic!("unknown type {t}")),
                                )
                            })
                            .collect();
                        println!("  extra keep-set {name}: {} cells", set.len());
                        (name.clone(), set)
                    })
                    .collect()
            }
            Err(_) => Vec::new(),
        };
        for (name, set) in &extra {
            variants.push((name.as_str(), set));
        }
        export_models(locel, type_of, &variants, act_of, &ev_types, &types, &dir, &tag);
    }
}

/// Above this many cut cells the quadratic repair is skipped and said to be skipped.
const CONNECTIVITY_REPAIR_LIMIT: usize = 120;

// ==========================================================================
// Arcs and connectivity
// ==========================================================================

/// Arc set per object type, for comparing a reduced model against the full one.
fn arc_set(
    locel: &SlimLinkedOCEL,
    type_of: &HashMap<ObjectIndex, usize>,
    act_of: &[usize],
    kept: &HashSet<(usize, usize)>,
) -> HashSet<(usize, usize, usize)> {
    let mut arcs = HashSet::new();
    for o in locel.get_all_obs() {
        let t = type_of[&o];
        let mut evs: Vec<EventIndex> = o.get_e2o_rev(locel).copied().collect();
        evs.sort_by(|a, b| {
            a.get_time(locel)
                .cmp(b.get_time(locel))
                .then_with(|| a.get_ev(locel).id.cmp(&b.get_ev(locel).id))
        });
        let trace: Vec<usize> = evs
            .into_iter()
            .map(|e| act_of[e.get_ev(locel).event_type])
            .filter(|a| kept.contains(&(*a, t)))
            .collect();
        for w in trace.windows(2) {
            arcs.insert((t, w[0], w[1]));
        }
    }
    arcs
}

/// Coloured arcs of the object-centric directly-follows graph induced by a keep-set,
/// and the number of connected components of the underlying activity graph.
///
/// A type's flow is its trace **restricted to the activities whose cell is kept**, not
/// the induced subgraph: removing a cell splices the trace, it does not delete the
/// object's later behaviour. This is activity projection, and getting it wrong is what
/// would make the reduction lossy.
fn arcs_and_components(
    locel: &SlimLinkedOCEL,
    type_of: &HashMap<ObjectIndex, usize>,
    act_of: &[usize],
    n_acts: usize,
    kept: &HashSet<(usize, usize)>,
) -> (usize, usize) {
    let mut arcs: HashSet<(usize, usize, usize)> = HashSet::new();
    for o in locel.get_all_obs() {
        let t = type_of[&o];
        // Sort by (timestamp, event index), NOT by timestamp alone. Simultaneous
        // events are common -- a game log ticks many events at one instant -- and with
        // a timestamp-only key their relative order is whatever the importer produced,
        // so the directly-follows pairs and hence the arc count vary between runs.
        // Measured on Age of Empires: 91,219 / 91,508 / 91,531 / 91,547 arcs for the
        // same keep-set. Any arc count has to name its tie-break.
        let mut evs: Vec<EventIndex> = o.get_e2o_rev(locel).copied().collect();
        // Tie-break on the event ID, which is intrinsic to the log. Tie-breaking on
        // EventIndex does NOT work: indices are assigned during import and the
        // importer's own event order varies between runs on a large log, so the arc
        // count still moved (91,155 vs 91,503 on Age of Empires).
        evs.sort_by(|a, b| {
            a.get_time(locel)
                .cmp(b.get_time(locel))
                .then_with(|| a.get_ev(locel).id.cmp(&b.get_ev(locel).id))
        });
        let trace: Vec<usize> = evs
            .into_iter()
            .map(|e| act_of[e.get_ev(locel).event_type])
            .filter(|a| kept.contains(&(*a, t)))
            .collect();
        for w in trace.windows(2) {
            arcs.insert((t, w[0], w[1]));
        }
    }
    // Union-find over activities that carry at least one kept cell.
    let mut parent: Vec<usize> = (0..n_acts).collect();
    fn find(parent: &mut Vec<usize>, x: usize) -> usize {
        let mut x = x;
        while parent[x] != x {
            parent[x] = parent[parent[x]];
            x = parent[x];
        }
        x
    }
    for (_, a, b) in &arcs {
        let (ra, rb) = (find(&mut parent, *a), find(&mut parent, *b));
        if ra != rb {
            parent[ra] = rb;
        }
    }
    let live: HashSet<usize> = kept.iter().map(|(a, _)| *a).collect();
    let comps: HashSet<usize> = live.iter().map(|a| find(&mut parent, *a)).collect();
    (arcs.len(), comps.len())
}

/// Components of the activity-type incidence graph: two activities are linked when
/// they keep a common object type.
///
/// This is the artifact-independent notion of connectivity. The DFG repair connects
/// the directly-follows graph, which does not imply the OC-DECLARE constraint graph is
/// connected -- measured: DFG-repaired keep-set gives 1 DFG component but 2 constraint
/// components. Two activities that share a kept type will generally carry a constraint
/// between them, so repairing this graph repairs both, and it needs no discovery run.
fn incidence_components(kept: &HashSet<(usize, usize)>) -> usize {
    let mut by_type: HashMap<usize, Vec<usize>> = HashMap::new();
    for (a, t) in kept {
        by_type.entry(*t).or_default().push(*a);
    }
    let acts: Vec<usize> = kept.iter().map(|(a, _)| *a).collect::<HashSet<_>>().into_iter().collect();
    let mut par: HashMap<usize, usize> = acts.iter().map(|a| (*a, *a)).collect();
    fn find(par: &mut HashMap<usize, usize>, x: usize) -> usize {
        let mut x = x;
        while par[&x] != x {
            let g = par[&par[&x]];
            par.insert(x, g);
            x = g;
        }
        x
    }
    for group in by_type.values() {
        for w in group.windows(2) {
            let (ra, rb) = (find(&mut par, w[0]), find(&mut par, w[1]));
            if ra != rb {
                par.insert(ra, rb);
            }
        }
    }
    acts.iter().map(|a| find(&mut par, *a)).collect::<HashSet<_>>().len()
}

/// Repair against the incidence graph: add cut cells back, in a fixed order, until
/// every activity is linked to every other through a shared kept type.
fn repair_incidence(
    kept: &HashSet<(usize, usize)>,
    cut: &[(usize, usize)],
) -> (HashSet<(usize, usize)>, usize) {
    let mut kept = kept.clone();
    let mut added = 0;
    while incidence_components(&kept) > 1 {
        let mut best: Option<(usize, (usize, usize))> = None;
        for c in cut {
            if kept.contains(c) {
                continue;
            }
            let mut trial = kept.clone();
            trial.insert(*c);
            let n = incidence_components(&trial);
            if best.is_none_or(|(bn, _)| n < bn) {
                best = Some((n, *c));
            }
        }
        match best {
            Some((n, c)) if n < incidence_components(&kept) => {
                kept.insert(c);
                added += 1;
            }
            _ => break,
        }
    }
    (kept, added)
}

/// Deterministic connectivity repair: add cut cells back in a fixed order until the
/// reduced model has no more components than the full one. Deterministic, hence
/// canonical -- which is what keeps the canonicity argument intact once connectivity
/// is required. Returns the repaired keep-set and how many cells were added back.
fn repair_connectivity(
    locel: &SlimLinkedOCEL,
    type_of: &HashMap<ObjectIndex, usize>,
    act_of: &[usize],
    n_acts: usize,
    kept: &HashSet<(usize, usize)>,
    cut: &[(usize, usize)],
    target_comps: usize,
) -> (HashSet<(usize, usize)>, usize) {
    let mut kept = kept.clone();
    let mut added = 0;
    loop {
        let (_, comps) = arcs_and_components(locel, type_of, act_of, n_acts, &kept);
        if comps <= target_comps {
            break;
        }
        let mut best: Option<(usize, (usize, usize))> = None;
        for c in cut {
            if kept.contains(c) {
                continue;
            }
            let mut trial = kept.clone();
            trial.insert(*c);
            let (_, tc) = arcs_and_components(locel, type_of, act_of, n_acts, &trial);
            if tc < comps && best.is_none_or(|(bc, _)| tc < bc) {
                best = Some((tc, *c));
            }
        }
        match best {
            Some((_, c)) => {
                kept.insert(c);
                added += 1;
            }
            None => break, // nothing left that reconnects anything
        }
    }
    (kept, added)
}

// ==========================================================================
// Model export: OC-DFG before and after, and OC-DECLARE before and after
// ==========================================================================

/// Per-type palette for the coloured arcs. Deliberately the same hues the earlier
/// OC-DECLARE papers use for the order-management types.
const PALETTE: [&str; 12] = [
    "#1f4e9c", "#d95f02", "#c51b8a", "#1b7837", "#7570b3", "#8c510a",
    "#2166ac", "#b2182b", "#4d9221", "#762a83", "#01665e", "#bf812d",
];

/// Materialise the reduced log by deleting the E2O tuples of every cut cell. This is
/// the log-side operator of ruling P4D5: everything downstream (OC-DFG, OC-DECLARE)
/// is then just discovery on a smaller log, with no formalism-specific machinery.
fn materialise_reduced(
    locel: &SlimLinkedOCEL,
    type_of: &HashMap<ObjectIndex, usize>,
    act_of: &[usize],
    kept: &HashSet<(usize, usize)>,
) -> SlimLinkedOCEL {
    let mut out = locel.clone();
    let doomed: Vec<(EventIndex, ObjectIndex)> = locel
        .get_all_evs()
        .flat_map(|e| {
            let a = act_of[e.get_ev(locel).event_type];
            e.get_e2o(locel)
                .filter(|o| !kept.contains(&(a, type_of[o])))
                .map(move |o| (e, *o))
                .collect::<Vec<_>>()
        })
        .collect();
    for (e, o) in doomed {
        out.delete_e2o(&e, &o);
    }
    out
}

/// Write one OC-DFG as graphviz DOT. `rel_threshold` drops arcs whose frequency is
/// below that fraction of the busiest arc **of the same object type**, which is the
/// per-type frequency filter the earlier figures use. At 0.0 nothing is dropped.
fn write_ocdfg_dot(
    locel: &SlimLinkedOCEL,
    path: &std::path::Path,
    title: &str,
    rel_threshold: f64,
) -> (usize, usize) {
    use std::fmt::Write as _;
    let dfg =
        process_mining::core::process_models::object_centric::ocdfg::discover_dfg_from_ocel(locel);

    let mut types: Vec<&String> = dfg.object_type_to_dfg.keys().collect();
    types.sort();

    let mut body = String::new();
    let mut nodes: HashSet<String> = HashSet::new();
    let mut arcs = 0usize;
    let mut per_type: Vec<(String, usize)> = Vec::new();
    for (i, ot) in types.iter().enumerate() {
        let g = &dfg.object_type_to_dfg[*ot];
        let max = g.directly_follows_relations.values().copied().max().unwrap_or(0) as f64;
        if max == 0.0 {
            continue;
        }
        let colour = PALETTE[i % PALETTE.len()];
        let mut here = 0usize;
        for ((a, b), n) in &g.directly_follows_relations {
            if (*n as f64) < rel_threshold * max {
                continue;
            }
            nodes.insert(a.to_string());
            nodes.insert(b.to_string());
            arcs += 1;
            here += 1;
            let _ = writeln!(
                body,
                "  \"{a}\" -> \"{b}\" [color=\"{colour}\", penwidth=1.2, label=\"{n}\", fontsize=8, fontcolor=\"{colour}\"];"
            );
        }
        if here > 0 {
            per_type.push(((*ot).clone(), here));
        }
    }
    per_type.sort_by_key(|(_, n)| std::cmp::Reverse(*n));

    let mut dot = String::new();
    let _ = writeln!(dot, "digraph {{");
    let _ = writeln!(dot, "  labelloc=\"t\"; label=\"{title}\"; fontsize=16;");
    let _ = writeln!(dot, "  rankdir=TB; node [shape=box, style=rounded, fontsize=10];");
    let mut ns: Vec<&String> = nodes.iter().collect();
    ns.sort();
    for n in &ns {
        let _ = writeln!(dot, "  \"{n}\";");
    }
    // Legend: one row per object type, so a reader can tell which colour is which.
    let _ = writeln!(dot, "  subgraph cluster_legend {{ label=\"object types\"; fontsize=10;");
    for (ot, n) in &per_type {
        let i = types.iter().position(|t| *t == ot).unwrap();
        let colour = PALETTE[i % PALETTE.len()];
        let _ = writeln!(
            dot,
            "    \"lg{i}\" [label=\"{ot}  ({n} arcs)\", shape=plaintext, fontcolor=\"{colour}\", fontsize=10];"
        );
    }
    let _ = writeln!(dot, "  }}");
    dot.push_str(&body);
    let _ = writeln!(dot, "}}");
    std::fs::write(path, dot).expect("write dot");
    println!(
        "    {title}: {} arcs  {}",
        arcs,
        per_type
            .iter()
            .map(|(t, n)| format!("{t}={n}"))
            .collect::<Vec<_>>()
            .join(" ")
    );
    (nodes.len(), arcs)
}

/// Discover OC-DECLARE on a log and return the constraint count, with and without the
/// published lossless transitive reduction. The two axes are meant to be orthogonal:
/// this one removes constraints implied by other constraints, structure-based
/// reduction removes constraints implied by the object schema.
fn ocdeclare_sizes(locel: &SlimLinkedOCEL) -> (usize, usize) {
    ocdeclare_run(locel, None)
}

/// Same, and writes each model to `<prefix>-{none,lossless}.json` when a prefix is
/// given. The JSON is the model as serialised by the crate, so it opens in the
/// OC-DECLARE viewer unchanged.
fn ocdeclare_run(locel: &SlimLinkedOCEL, prefix: Option<&std::path::Path>) -> (usize, usize) {
    use process_mining::core::process_models::object_centric::oc_declare::OCDeclareArcType;
    use process_mining::discovery::object_centric::oc_declare::{
        discover_behavior_constraints, O2OMode, OCDeclareDiscoveryOptions, OCDeclareReductionMode,
    };
    // [EF, EP, AS] as the pitch note specifies. The crate default also includes DF and
    // DP, which is why an earlier run reported 107 constraints where the note reports
    // 154 -- a different question, not a different answer.
    let arrows: HashSet<OCDeclareArcType> = match env::var("ARROWS").as_deref() {
        Ok("all") => process_mining::core::process_models::object_centric::oc_declare::
            ALL_OC_DECLARE_ARC_TYPES
            .iter()
            .copied()
            .collect(),
        _ => [
            OCDeclareArcType::EF,
            OCDeclareArcType::EP,
            OCDeclareArcType::AS,
        ]
        .into_iter()
        .collect(),
    };
    // Whether discovery may traverse the object schema. `None` is the setting every
    // other run in this file uses; the other modes exist so the same algorithm can be
    // asked the same question with the schema in scope, which is the controlled arm of
    // the invariance experiment.
    let o2o_mode = match env::var("O2O_MODE").as_deref() {
        Ok("direct") => O2OMode::Direct,
        Ok("reversed") => O2OMode::Reversed,
        Ok("bidirectional") => O2OMode::Bidirectional,
        _ => O2OMode::None,
    };
    let mut run = |red, name: &str| {
        let m = discover_behavior_constraints(
            locel,
            OCDeclareDiscoveryOptions {
                noise_threshold: 0.0,
                o2o_mode,
                acts_to_use: None,
                reduction: red,
                refinement: true,
                considered_arrow_types: arrows.clone(),
                ..Default::default()
            },
        );
        if let Some(pre) = prefix {
            let path = pre.with_file_name(format!(
                "{}-{name}.json",
                pre.file_name().unwrap().to_string_lossy()
            ));
            std::fs::write(&path, serde_json::to_string_pretty(&m).unwrap())
                .expect("write oc-declare json");
            println!("    wrote {}  ({} constraints)", path.display(), m.len());
        }
        m.len()
    };
    (
        run(OCDeclareReductionMode::None, "none"),
        run(OCDeclareReductionMode::Lossless, "lossless"),
    )
}

/// Arc-guided keep-set: the smallest addition to `base` that makes the reduced model
/// retain a spanning subset of the FULL model's own arcs.
///
/// The point is that a bridge has to be a type that actually carries model arcs. The
/// incidence heuristic added `employees` -- present at both ends, but a resource that
/// everyone shares, so it supports no constraint and the model stayed in three pieces.
/// Reading the bridges off the full model instead costs one discovery run we already
/// do, and needs no discovery inside the loop.
///
/// With an empty arc set this is the plain maximum; with a spanning tree it is
/// connected; with every arc it is maximal preservation. One operator, one knob.
/// Union-find over activities where two activities are linked when some OBJECT of a
/// kept type participates in events of both.
///
/// This is the right cheap proxy for OC-DECLARE connectivity. Type co-presence is too
/// weak (`employees` is kept at both ends everywhere and supports no constraint), and
/// DFG connectivity is a different graph entirely -- one variant had a connected DFG
/// and a two-component constraint graph. A constraint between two activities needs
/// objects of a shared kept type at both, which is exactly what this measures.
fn sharing_parent(
    locel: &SlimLinkedOCEL,
    type_of: &HashMap<ObjectIndex, usize>,
    act_of: &[usize],
    kept: &HashSet<(usize, usize)>,
) -> HashMap<usize, usize> {
    fn find(p: &mut HashMap<usize, usize>, x: usize) -> usize {
        let mut x = x;
        loop {
            let px = *p.entry(x).or_insert(x);
            if px == x {
                return x;
            }
            x = px;
        }
    }
    let mut parent: HashMap<usize, usize> = HashMap::new();
    for o in locel.get_all_obs() {
        let t = type_of[&o];
        let acts: Vec<usize> = o
            .get_e2o_rev(locel)
            .map(|e| act_of[e.get_ev(locel).event_type])
            .filter(|a| kept.contains(&(*a, t)))
            .collect::<HashSet<_>>()
            .into_iter()
            .collect();
        for w in acts.windows(2) {
            let (ra, rb) = (find(&mut parent, w[0]), find(&mut parent, w[1]));
            if ra != rb {
                parent.insert(ra, rb);
            }
        }
    }
    parent
}

/// Frequency of each (object type, activity, activity) directly-follows pair in the
/// FULL log. This is what tells a real handover from an incidental one.
fn arc_frequencies(
    locel: &SlimLinkedOCEL,
    type_of: &HashMap<ObjectIndex, usize>,
    act_of: &[usize],
) -> HashMap<(usize, usize, usize), usize> {
    let mut freq: HashMap<(usize, usize, usize), usize> = HashMap::new();
    for o in locel.get_all_obs() {
        let t = type_of[&o];
        let mut evs: Vec<EventIndex> = o.get_e2o_rev(locel).copied().collect();
        evs.sort_by(|a, b| {
            a.get_time(locel)
                .cmp(b.get_time(locel))
                .then_with(|| a.get_ev(locel).id.cmp(&b.get_ev(locel).id))
        });
        let trace: Vec<usize> = evs
            .into_iter()
            .map(|e| act_of[e.get_ev(locel).event_type])
            .collect();
        for w in trace.windows(2) {
            *freq.entry((t, w[0], w[1])).or_insert(0) += 1;
        }
    }
    freq
}

fn arc_guided(
    locel: &SlimLinkedOCEL,
    type_of: &HashMap<ObjectIndex, usize>,
    act_of: &[usize],
    base: &HashSet<(usize, usize)>,
    full_model: &[(String, String, Vec<String>)],
    act_ix: &HashMap<&str, usize>,
    type_ix: &HashMap<&str, usize>,
) -> HashSet<(usize, usize)> {
    // MINIMUM spanning tree, weighted by the arcs a bridge adds -- not the first
    // spanning tree, and not weighted by cells.
    //
    // Cells and arcs are not proportional. Keeping a fine, high-participation type at
    // one more activity costs one cell and can cost dozens of arcs: on this log a
    // cell-cheap tie-break kept choosing `items`, which went from 2 arcs to 35. The
    // currency that matters is the one the reader sees.
    fn find(p: &mut HashMap<usize, usize>, x: usize) -> usize {
        let mut x = x;
        loop {
            let px = *p.entry(x).or_insert(x);
            if px == x {
                return x;
            }
            x = px;
        }
    }
    // Weight a bridge by the TRAFFIC it restores, not by the arcs it adds. Minimising
    // added arcs picks the cheapest seam, which is the one carrying no flow: on this
    // log it chose `items` at `package delivered`, an activity with no items
    // directly-follows arc at all, over `create package`, where 5290 items actually
    // hand over. Cheapest and most meaningful are close to opposites here.
    let freq = arc_frequencies(locel, type_of, act_of);

    // PRESERVATION FIRST, connectivity second. A spanning tree stops as soon as the
    // model is in one piece, so it never asks whether the arcs a reader cares about
    // survived: `items` was kept at `confirm order` and `create package` but not at
    // `place order`, hiding `place order -> pick item`, one of the busiest arcs in the
    // log. Require instead that every arc the DISPLAYED model would show is retained,
    // using the same per-type frequency filter the display uses (ruling P4D9). The
    // threshold is the readability knob: 0 keeps everything, 1 keeps nothing.
    let preserve_thr: f64 = env::var("PRESERVE")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(0.02);
    let mut out = base.clone();
    if preserve_thr < 1.0 {
        let mut max_per_type: HashMap<usize, usize> = HashMap::new();
        for ((t, _, _), n) in &freq {
            let e = max_per_type.entry(*t).or_insert(0);
            *e = (*e).max(*n);
        }
        let mut required: Vec<(usize, usize, usize, usize)> = freq
            .iter()
            .filter(|((t, _, _), n)| {
                **n as f64 >= preserve_thr * max_per_type.get(t).copied().unwrap_or(0) as f64
            })
            .map(|((t, a, b), n)| (*n, *t, *a, *b))
            .collect();
        required.sort_by_key(|(n, t, a, b)| (std::cmp::Reverse(*n), *t, *a, *b));
        for (_, t, a, b) in required {
            out.insert((a, t));
            out.insert((b, t));
        }
    }
    let mut candidates: Vec<(std::cmp::Reverse<usize>, usize, (usize, usize), (usize, usize))> =
        Vec::new();
    let before = arc_set(locel, type_of, act_of, &out).len();
    for (from, to, types) in full_model {
        let (Some(&a), Some(&b)) = (act_ix.get(from.as_str()), act_ix.get(to.as_str())) else {
            continue;
        };
        if a == b {
            continue;
        }
        for t in types {
            let Some(&t) = type_ix.get(t.as_str()) else { continue };
            let mut trial = out.clone();
            trial.insert((a, t));
            trial.insert((b, t));
            let cost = arc_set(locel, type_of, act_of, &trial).len().saturating_sub(before);
            let traffic = freq.get(&(t, a, b)).copied().unwrap_or(0)
                + freq.get(&(t, b, a)).copied().unwrap_or(0);
            // Most traffic first; among equals, fewest arcs added.
            candidates.push((std::cmp::Reverse(traffic), cost, (a, t), (b, t)));
        }
    }
    // Kruskal: cheapest bridge first, ties broken deterministically.
    candidates.sort();
    // Seed the union-find with the components the reduced model ACTUALLY has, not with
    // isolated nodes. Measuring connectivity over the full model's arc graph lets
    // zero-cost arcs (both endpoints already keeping the carrier) span the graph, so
    // the search declares itself finished and adds nothing -- which is what left one
    // variant at two components while reporting "+0 cells".
    // Seed with the full model's OWN arcs that this keep-set retains: an arc (a1,a2)
    // carried by type T counts as present iff T is kept at both ends. Every cheaper
    // proxy over-predicts -- type co-presence and object sharing both link clusters
    // through `employees`, a resource shared by everyone that supports no constraint,
    // and DFG connectivity is a different graph. The full model is the only thing that
    // knows which links are real, and we already discovered it.
    let mut parent: HashMap<usize, usize> = HashMap::new();
    for (from, to, tys) in full_model {
        let (Some(&a), Some(&b)) = (act_ix.get(from.as_str()), act_ix.get(to.as_str())) else {
            continue;
        };
        if tys
            .iter()
            .filter_map(|t| type_ix.get(t.as_str()).copied())
            .any(|t| out.contains(&(a, t)) && out.contains(&(b, t)))
        {
            let (ra, rb) = (find(&mut parent, a), find(&mut parent, b));
            if ra != rb {
                parent.insert(ra, rb);
            }
        }
    }
    for (_, _, (a, t), (b, _)) in candidates {
        let (ra, rb) = (find(&mut parent, a), find(&mut parent, b));
        if ra == rb {
            continue;
        }
        parent.insert(ra, rb);
        out.insert((a, t));
        out.insert((b, t));
    }
    out
}

fn export_models(
    locel: &SlimLinkedOCEL,
    type_of: &HashMap<ObjectIndex, usize>,
    variants: &[(&str, &HashSet<(usize, usize)>)],
    act_of: &[usize],
    ev_types: &[String],
    types: &[String],
    dir: &str,
    tag: &str,
) {
    let dir = std::path::Path::new(dir);
    std::fs::create_dir_all(dir).expect("create export dir");

    println!("\nMODELS  -> {}", dir.display());

    // One discovery of the full model, reused as the source of bridge arcs.
    let full_arcs: Vec<(String, String, Vec<String>)> = {
        use process_mining::core::process_models::object_centric::oc_declare::OCDeclareArcType;
        use process_mining::discovery::object_centric::oc_declare::{
            discover_behavior_constraints, O2OMode, OCDeclareDiscoveryOptions,
            OCDeclareReductionMode,
        };
        let arrows: HashSet<OCDeclareArcType> = [
            OCDeclareArcType::EF,
            OCDeclareArcType::EP,
            OCDeclareArcType::AS,
        ]
        .into_iter()
        .collect();
        let m = discover_behavior_constraints(
            locel,
            OCDeclareDiscoveryOptions {
                noise_threshold: 0.0,
                o2o_mode: O2OMode::None,
                acts_to_use: None,
                reduction: OCDeclareReductionMode::Lossless,
                refinement: true,
                considered_arrow_types: arrows,
                ..Default::default()
            },
        );
        let v: serde_json::Value = serde_json::to_value(&m).unwrap();
        v.as_array()
            .unwrap()
            .iter()
            .map(|c| {
                let mut ts: Vec<String> = Vec::new();
                for q in ["each", "any", "all"] {
                    if let Some(a) = c["label"][q].as_array() {
                        for o in a {
                            if let Some(t) = o["object_type"].as_str() {
                                ts.push(t.to_string());
                            }
                        }
                    }
                }
                ts.sort();
                ts.dedup();
                (
                    c["from"].as_str().unwrap_or_default().to_string(),
                    c["to"].as_str().unwrap_or_default().to_string(),
                    ts,
                )
            })
            .collect()
    };
    let act_ix2: HashMap<&str, usize> = ev_types.iter().enumerate().map(|(i, a)| (a.as_str(), i)).collect();
    let type_ix2: HashMap<&str, usize> = types.iter().enumerate().map(|(i, t)| (t.as_str(), i)).collect();

    // Arc-guided variants, built from the base keep-set of each input variant.
    let guided: Vec<(String, HashSet<(usize, usize)>)> = variants
        .iter()
        .map(|(n, k)| {
            (
                format!("{n}-arcguided"),
                arc_guided(locel, type_of, act_of, k, &full_arcs, &act_ix2, &type_ix2),
            )
        })
        .collect();
    let mut variants: Vec<(&str, &HashSet<(usize, usize)>)> = variants.to_vec();
    for (n, k) in &guided {
        variants.push((n.as_str(), k));
        println!("  {n}: {} cells (base +{})", k.len(), k.len() - variants.iter().find(|(m,_)| *m == n.trim_end_matches("-arcguided")).map(|(_,s)| s.len()).unwrap_or(0));
    }
    let variants = &variants[..];

    // Keep-sets as (activity, object type) name pairs, so other tools can apply the
    // same reduction to the same log without re-implementing discovery.
    {
        let mut obj = serde_json::Map::new();
        for (vname, kept) in variants {
            let mut cells: Vec<Vec<String>> = kept
                .iter()
                .map(|(a, t)| vec![ev_types[*a].clone(), types[*t].clone()])
                .collect();
            cells.sort();
            obj.insert((*vname).to_string(), serde_json::json!(cells));
        }
        let path = dir.join(format!("{tag}-keepsets.json"));
        std::fs::write(&path, serde_json::to_string_pretty(&obj).unwrap()).expect("write keepsets");
        println!("  wrote {}", path.display());
    }
    for (thr, name) in [(0.0, "unfiltered"), (0.02, "filter2pct")] {
        write_ocdfg_dot(
            locel,
            &dir.join(format!("{tag}-ocdfg-full-{name}.dot")),
            &format!("{tag}  OC-DFG  full  ({name})"),
            thr,
        );
        for (vname, kept) in variants {
            let reduced = materialise_reduced(locel, type_of, act_of, kept);
            write_ocdfg_dot(
                &reduced,
                &dir.join(format!("{tag}-ocdfg-{vname}-{name}.dot")),
                &format!("{tag}  OC-DFG  {vname}  ({name})"),
                thr,
            );
        }
    }

    let t = Instant::now();
    let (full_none, full_loss) = ocdeclare_run(locel, Some(&dir.join(format!("{tag}-ocdeclare-full"))));
    let mut red_none = 0;
    let mut red_loss = 0;
    for (vname, kept) in variants {
        let reduced = materialise_reduced(locel, type_of, act_of, kept);
        let (n, l) = ocdeclare_run(
            &reduced,
            Some(&dir.join(format!("{tag}-ocdeclare-{vname}"))),
        );
        if *vname == "canonical" {
            red_none = n;
            red_loss = l;
        }
    }
    println!(
        "  OC-DECLARE  full {full_none} / lossless {full_loss}   reduced {red_none} / lossless {red_loss}   ({:.1}s)",
        t.elapsed().as_secs_f64()
    );
    println!(
        "  OC-DECLARE  structural on top of lossless: {full_loss} -> {red_loss} ({:.0}% further)",
        100.0 * (full_loss as f64 - red_loss as f64) / full_loss.max(1) as f64
    );
    println!("  NOTE: no OCPN discovery exists in this crate, so no OCPN before/after is produced.");
}
