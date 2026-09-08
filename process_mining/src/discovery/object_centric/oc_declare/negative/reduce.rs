//! Cardinality entailment, domination, existence reachability, composition, the unified
//! entailment digraph, rule B/B', and orientation dedup.
use std::collections::{HashMap, HashSet};

use crate::core::process_models::oc_declare::{
    ActivityObjectFacts, OCDeclareArc, OCDeclareArcLabel, OCDeclareArcType, ObjectInvolvementCounts,
};

use super::base_type_name;

/// Premise arrows admissible for source-anchored composition. `DF`/`DP` are included
/// because a `DF` fact is strictly stronger than an `EF` one, so admitting it as a premise
/// can only add sound derivations.
pub(crate) fn src_admissible(ar_f: OCDeclareArcType) -> HashSet<OCDeclareArcType> {
    use OCDeclareArcType::*;
    match ar_f {
        AS => [AS, EF, EP, DF, DP].into_iter().collect(),
        EF => [EP, DP].into_iter().collect(),
        EP => [EF, DF].into_iter().collect(),
        DF | DP => HashSet::new(),
    }
}

/// Premise arrows admissible for target-anchored composition.
pub(crate) fn tgt_admissible(ar_f: OCDeclareArcType) -> HashSet<OCDeclareArcType> {
    use OCDeclareArcType::*;
    match ar_f {
        AS => [AS, EF, EP, DF, DP].into_iter().collect(),
        EF => [EF, DF].into_iter().collect(),
        EP => [EP, DP].into_iter().collect(),
        DF | DP => HashSet::new(),
    }
}

/// `(from, to)` activity pairs reachable via a path of `existing` arcs, every edge's arrow in
/// `admissible` and carrying `ot` as `Each`/`All`. Also serves rule B's opposite-direction
/// path.
pub(crate) fn reachable_pairs(
    existing: &[OCDeclareArc],
    admissible: &HashSet<OCDeclareArcType>,
    ot: &str,
) -> HashSet<(String, String)> {
    reachable_pairs_at_level(existing, admissible, ot, false)
}

/// As [`reachable_pairs`], but with `require_all` every edge of the path must carry `ot` as
/// `All`.
///
/// Target-anchored composition needs this: for an `All`-involved type the proposition's proof
/// chains object-set *containments*, and only an `All` premise supplies one. An `Each` premise
/// merely pins a single shared object, so admitting it would let the rule derive constraints
/// that do not follow.
pub(crate) fn reachable_pairs_at_level(
    existing: &[OCDeclareArc],
    admissible: &HashSet<OCDeclareArcType>,
    ot: &str,
    require_all: bool,
) -> HashSet<(String, String)> {
    let mut adj: HashMap<&str, HashSet<&str>> = HashMap::new();
    for e in existing {
        if !admissible.contains(&e.arc_type) {
            continue;
        }
        let involved = e.label.all.iter().any(|a| base_type_name(a) == ot)
            || (!require_all && e.label.each.iter().any(|a| base_type_name(a) == ot));
        if !involved {
            continue;
        }
        adj.entry(e.from.as_str()).or_default().insert(e.to.as_str());
    }
    let mut pairs = HashSet::new();
    for &src in adj.keys() {
        let mut seen = HashSet::new();
        let mut stack = vec![src];
        seen.insert(src);
        while let Some(u) = stack.pop() {
            for &v in adj.get(u).into_iter().flatten() {
                if seen.insert(v) {
                    stack.push(v);
                }
            }
        }
        pairs.extend(
            seen.into_iter()
                .filter(|&v| v != src)
                .map(|v| (src.to_string(), v.to_string())),
        );
    }
    pairs
}

/// `(from, to)` pairs joined by a path whose EVERY edge carries EVERY type of `dom` at the
/// required level.
///
/// Computing reachability per type and intersecting the results is unsound: two types may then
/// be witnessed by two different arcs, producing two different intermediate events, neither of
/// which satisfies all of the forbidding constraint's filters. The proposition needs one
/// existence arc (or one path) carrying all of them together.
pub(crate) fn reachable_pairs_all_types(
    existing: &[OCDeclareArc],
    admissible: &HashSet<OCDeclareArcType>,
    dom: &[&str],
    require_all: &HashSet<&str>,
) -> HashSet<(String, String)> {
    let mut adj: HashMap<&str, HashSet<&str>> = HashMap::new();
    for e in existing {
        if !admissible.contains(&e.arc_type) {
            continue;
        }
        let carries_every = dom.iter().all(|ot| {
            e.label.all.iter().any(|a| base_type_name(a) == *ot)
                || (!require_all.contains(ot)
                    && e.label.each.iter().any(|a| base_type_name(a) == *ot))
        });
        if !carries_every {
            continue;
        }
        adj.entry(e.from.as_str()).or_default().insert(e.to.as_str());
    }
    let mut pairs = HashSet::new();
    for &src in adj.keys() {
        let mut seen = HashSet::new();
        let mut stack = vec![src];
        seen.insert(src);
        while let Some(u) = stack.pop() {
            for &v in adj.get(u).into_iter().flatten() {
                if seen.insert(v) {
                    stack.push(v);
                }
            }
        }
        pairs.extend(
            seen.into_iter()
                .filter(|&v| v != src)
                .map(|v| (src.to_string(), v.to_string())),
        );
    }
    pairs
}

/// Cardinality entailment: drop if `min |obj_ot(src)| > max |obj_ot(tgt)|`
/// for some `All`-involved `ot` — the target side can never carry enough objects for the
/// source's `All` set to be contained, so the negative constraint holds vacuously.
///
/// The minimum is taken over the source events that carry `ot` *at all*, so `carries(src, ot)`
/// has to be checked separately: at a source event with `obj_ot(e)` empty the containment is
/// vacuously true and the constraint can genuinely be violated there.
pub(crate) fn cardinality_entailed(
    c: &OCDeclareArc,
    act_ob_inv: &HashMap<String, HashMap<String, ObjectInvolvementCounts>>,
    facts: &HashMap<String, HashMap<String, ActivityObjectFacts>>,
) -> bool {
    c.label.all.iter().any(|ot| {
        let name = base_type_name(ot);
        if !facts
            .get(c.from.as_str())
            .and_then(|m| m.get(name))
            .is_some_and(|f| f.always_present)
        {
            return false;
        }
        let src_min = act_ob_inv
            .get(c.from.as_str())
            .and_then(|m| m.get(name))
            .map(|x| x.min)
            .unwrap_or(0);
        let tgt_max = act_ob_inv
            .get(c.to.as_str())
            .and_then(|m| m.get(name))
            .map(|x| x.max)
            .unwrap_or(0);
        src_min > tgt_max
    })
}

/// Domination within an activity pair, using the reversed order: for negative constraints
/// the *weak* side (fewer involvements, weaker arrow) being satisfied implies the *strong*
/// side is too, so the strong side is what gets dropped. Same
/// `is_dominated_by`/`is_dominated_by_or_eq` calls as existence reduction, opposite side
/// removed.
pub(crate) fn drop_dominated(candidates: Vec<OCDeclareArc>) -> Vec<OCDeclareArc> {
    candidates
        .iter()
        .filter(|c| {
            !candidates.iter().any(|c2| {
                *c2 != **c
                    && c2.from == c.from
                    && c2.to == c.to
                    && c2.arc_type.is_dominated_by_or_eq(&c.arc_type)
                    && c2.label.is_dominated_by(&c.label)
            })
        })
        .cloned()
        .collect()
}

/// Source-anchored composition, path variant. Edges `p -> c` where
/// `p = (ar_f, B, C, oi_f)` is already in `m1` and `c = (ar_f, A, C, oi_f)` is entailed by it
/// together with an existence path `A ~> B` (every edge admissible for `ar_f`, every edge
/// `Each`/`All`-involved on every type of `oi_f`) -- 1-hop is just a length-1 path, no separate
/// case needed. Never fires when `oi_f` has an `All`-involved type (forbidden on this side; see
/// rule C for that case) or when `A` does not provably carry every `dom(oi_f)` type on every
/// event: the carry condition is not optional.
pub(crate) fn source_anchored_edges(
    m1: &[OCDeclareArc],
    existing: &[OCDeclareArc],
    facts: &HashMap<String, HashMap<String, ActivityObjectFacts>>,
) -> HashMap<OCDeclareArc, HashSet<OCDeclareArc>> {
    let existing: Vec<OCDeclareArc> = existing
        .iter()
        .filter(|e| e.counts.0.unwrap_or(0) >= 1)
        .cloned()
        .collect();
    let mut edges: HashMap<OCDeclareArc, HashSet<OCDeclareArc>> = HashMap::new();
    for c in m1 {
        if !c.label.all.is_empty() {
            continue;
        }
        let a = c.from.as_str();
        let dom: Vec<&str> = c
            .label
            .each
            .iter()
            .chain(c.label.any.iter())
            .map(base_type_name)
            .collect();
        let a_carries_dom = dom
            .iter()
            .all(|ot| facts.get(a).and_then(|m| m.get(*ot)).is_some_and(|f| f.always_present));
        if !a_carries_dom {
            continue;
        }
        let admissible = src_admissible(c.arc_type);
        let reach = reachable_pairs_all_types(&existing, &admissible, &dom, &HashSet::new());
        for premise in m1 {
            if premise == c
                || premise.arc_type != c.arc_type
                || premise.to != c.to
                || premise.label != c.label
            {
                continue;
            }
            let b = premise.from.as_str();
            if b == a || b == c.to.as_str() {
                continue;
            }
            if reach.contains(&(a.to_string(), b.to_string())) {
                edges.entry(premise.clone()).or_default().insert(c.clone());
            }
        }
    }
    edges
}

/// Target-anchored composition, path variant. Edges `p -> c` where
/// `p = (ar_f, A, B, oi_f)` is already in `m1` and `c = (ar_f, A, C, oi_f)` is entailed by it
/// together with an existence path `C ~> B`. Unlike [`source_anchored_edges`], `All`
/// involvements are permitted on `oi_f` here; the source-side exclusion does not apply to
/// this rule.
pub fn target_anchored_edges(
    m1: &[OCDeclareArc],
    existing: &[OCDeclareArc],
) -> HashMap<OCDeclareArc, HashSet<OCDeclareArc>> {
    let existing: Vec<OCDeclareArc> = existing
        .iter()
        .filter(|e| e.counts.0.unwrap_or(0) >= 1)
        .cloned()
        .collect();
    let mut edges: HashMap<OCDeclareArc, HashSet<OCDeclareArc>> = HashMap::new();
    for c in m1 {
        let dom: Vec<&str> = c
            .label
            .each
            .iter()
            .chain(c.label.any.iter())
            .chain(c.label.all.iter())
            .map(base_type_name)
            .collect();
        let admissible = tgt_admissible(c.arc_type);
        let all_types: HashSet<&str> = c.label.all.iter().map(base_type_name).collect();
        let reach = reachable_pairs_all_types(&existing, &admissible, &dom, &all_types);
        for premise in m1 {
            if premise == c
                || premise.arc_type != c.arc_type
                || premise.from != c.from
                || premise.label != c.label
            {
                continue;
            }
            let b = premise.to.as_str();
            if b == c.from.as_str() || b == c.to.as_str() {
                continue;
            }
            // No carry condition on `B`: the proposition does not use one, `d_f` and `d_n`
            // sharing source activity and involvement. An earlier version required
            // `alwaysCarries(B, ot)`; `carry_check` showed every derivation it suppressed holds
            // at the discovery threshold, and dropping it removes 6 more arcs on container
            // logistics at rho = 0.
            if reach.contains(&(c.to.as_str().to_string(), b.to_string())) {
                edges.entry(premise.clone()).or_default().insert(c.clone());
            }
        }
    }
    edges
}

pub(crate) fn merge_edges(
    maps: Vec<HashMap<OCDeclareArc, HashSet<OCDeclareArc>>>,
) -> HashMap<OCDeclareArc, HashSet<OCDeclareArc>> {
    let mut merged: HashMap<OCDeclareArc, HashSet<OCDeclareArc>> = HashMap::new();
    for m in maps {
        for (k, v) in m {
            merged.entry(k).or_default().extend(v);
        }
    }
    merged
}

struct Tarjan<'a> {
    edges: &'a HashMap<OCDeclareArc, HashSet<OCDeclareArc>>,
    index: HashMap<OCDeclareArc, usize>,
    low: HashMap<OCDeclareArc, usize>,
    on_stack: HashSet<OCDeclareArc>,
    stack: Vec<OCDeclareArc>,
    counter: usize,
    comp: HashMap<OCDeclareArc, usize>,
    comp_counter: usize,
}

impl<'a> Tarjan<'a> {
    fn strongconnect(&mut self, v: &OCDeclareArc) {
        self.index.insert(v.clone(), self.counter);
        self.low.insert(v.clone(), self.counter);
        self.counter += 1;
        self.stack.push(v.clone());
        self.on_stack.insert(v.clone());

        let successors: Vec<OCDeclareArc> = self.edges.get(v).into_iter().flatten().cloned().collect();
        for w in &successors {
            if !self.index.contains_key(w) {
                self.strongconnect(w);
                let low_w = self.low[w];
                let low_v = self.low[v];
                *self.low.get_mut(v).unwrap() = low_v.min(low_w);
            } else if self.on_stack.contains(w) {
                let idx_w = self.index[w];
                let low_v = self.low[v];
                *self.low.get_mut(v).unwrap() = low_v.min(idx_w);
            }
        }

        if self.low[v] == self.index[v] {
            loop {
                let w = self.stack.pop().unwrap();
                self.on_stack.remove(&w);
                self.comp.insert(w.clone(), self.comp_counter);
                if w == *v {
                    break;
                }
            }
            self.comp_counter += 1;
        }
    }
}

/// Condense the entailment digraph's strongly connected components. Keeps one
/// arc (the `Ord`-smallest) per component with no incoming edge from a different component;
/// drops every component that does have one entirely, since it is already implied by whatever
/// entails it.
pub(crate) fn condense(
    m1: &[OCDeclareArc],
    edges: &HashMap<OCDeclareArc, HashSet<OCDeclareArc>>,
) -> Vec<OCDeclareArc> {
    let mut t = Tarjan {
        edges,
        index: HashMap::new(),
        low: HashMap::new(),
        on_stack: HashSet::new(),
        stack: Vec::new(),
        counter: 0,
        comp: HashMap::new(),
        comp_counter: 0,
    };
    for c in m1 {
        if !t.index.contains_key(c) {
            t.strongconnect(c);
        }
    }
    let mut incoming: HashMap<usize, HashSet<usize>> = HashMap::new();
    for (u, vs) in edges {
        let Some(&cu) = t.comp.get(u) else { continue };
        for v in vs {
            let Some(&cv) = t.comp.get(v) else { continue };
            if cu != cv {
                incoming.entry(cv).or_default().insert(cu);
            }
        }
    }
    let components: HashSet<usize> = m1.iter().filter_map(|c| t.comp.get(c).copied()).collect();
    let mut kept: Vec<OCDeclareArc> = Vec::new();
    for cid in components {
        if incoming.get(&cid).is_some_and(|s| !s.is_empty()) {
            continue;
        }
        if let Some(rep) = m1.iter().filter(|c| t.comp.get(*c) == Some(&cid)).min().cloned() {
            kept.push(rep);
        }
    }
    kept
}

/// Rule B/B': a negative constraint proven structurally true by uniqueness plus
/// an existence path, never by another negative constraint -- a plain filter, cannot cycle.
pub fn rule_b_removable(
    c: &OCDeclareArc,
    existing: &[OCDeclareArc],
    facts: &HashMap<String, HashMap<String, ActivityObjectFacts>>,
) -> bool {
    let opp = match c.arc_type {
        OCDeclareArcType::EF => OCDeclareArcType::EP,
        OCDeclareArcType::EP => OCDeclareArcType::EF,
        _ => return false,
    };
    let existing: Vec<OCDeclareArc> = existing
        .iter()
        .filter(|e| e.counts.0.unwrap_or(0) >= 1)
        .cloned()
        .collect();
    let s = c.from.as_str();
    let t = c.to.as_str();
    let unique = |act: &str, ot: &str| {
        facts
            .get(act)
            .and_then(|m| m.get(ot))
            .is_some_and(|f| f.always_present && f.at_most_one_event_per_object)
    };
    let always_present =
        |act: &str, ot: &str| facts.get(act).and_then(|m| m.get(ot)).is_some_and(|f| f.always_present);
    let dom: Vec<&str> = c
        .label
        .each
        .iter()
        .chain(c.label.any.iter())
        .chain(c.label.all.iter())
        .map(base_type_name)
        .collect();

    let opp_admissible = tgt_admissible(opp);
    for ot in &dom {
        if unique(t, ot)
            && always_present(s, ot)
            && reachable_pairs(&existing, &opp_admissible, ot).contains(&(s.to_string(), t.to_string()))
        {
            return true;
        }
    }
    let ar_admissible = tgt_admissible(c.arc_type);
    for ot in &dom {
        if unique(s, ot)
            && reachable_pairs(&existing, &ar_admissible, ot).contains(&(t.to_string(), s.to_string()))
        {
            return true;
        }
    }
    false
}

#[derive(PartialEq, Eq, Hash, Clone)]
enum DedupKey {
    Raw(OCDeclareArcType, String, String, OCDeclareArcLabel),
    Symmetric(String, String, OCDeclareArcLabel),
    Ordered(String, String, OCDeclareArcLabel),
}

/// The same statement read from the other end, when there is one.
///
/// `AS` is symmetric and `EF`/`EP` are transposes; `DF`/`DP` have no restatement. Only
/// meaningful for arcs [`is_unoriented`] accepts.
pub(crate) fn transpose(c: &OCDeclareArc) -> Option<OCDeclareArc> {
    let arc_type = match c.arc_type {
        OCDeclareArcType::AS => OCDeclareArcType::AS,
        OCDeclareArcType::EF => OCDeclareArcType::EP,
        OCDeclareArcType::EP => OCDeclareArcType::EF,
        OCDeclareArcType::DF | OCDeclareArcType::DP => return None,
    };
    Some(OCDeclareArc {
        from: c.to.clone(),
        to: c.from.clone(),
        arc_type,
        label: c.label.clone(),
        counts: c.counts,
    })
}

pub(crate) fn is_unoriented(c: &OCDeclareArc, facts: &HashMap<String, HashMap<String, ActivityObjectFacts>>) -> bool {
    if !c.label.all.is_empty() {
        return false;
    }
    let dom: Vec<&str> = c.label.each.iter().chain(c.label.any.iter()).map(base_type_name).collect();
    dom.iter().all(|ot| {
        facts.get(c.from.as_str()).and_then(|m| m.get(*ot)).is_some_and(|f| f.always_present)
            && facts.get(c.to.as_str()).and_then(|m| m.get(*ot)).is_some_and(|f| f.always_present)
    })
}

fn dedup_key(c: &OCDeclareArc, facts: &HashMap<String, HashMap<String, ActivityObjectFacts>>) -> DedupKey {
    if !is_unoriented(c, facts) {
        return DedupKey::Raw(
            c.arc_type,
            c.from.as_str().to_string(),
            c.to.as_str().to_string(),
            c.label.clone(),
        );
    }
    match c.arc_type {
        OCDeclareArcType::AS => {
            let (a, b) = if c.from.as_str() <= c.to.as_str() {
                (c.from.as_str().to_string(), c.to.as_str().to_string())
            } else {
                (c.to.as_str().to_string(), c.from.as_str().to_string())
            };
            DedupKey::Symmetric(a, b, c.label.clone())
        }
        OCDeclareArcType::EF => {
            DedupKey::Ordered(c.from.as_str().to_string(), c.to.as_str().to_string(), c.label.clone())
        }
        OCDeclareArcType::EP => {
            DedupKey::Ordered(c.to.as_str().to_string(), c.from.as_str().to_string(), c.label.clone())
        }
        _ => DedupKey::Raw(
            c.arc_type,
            c.from.as_str().to_string(),
            c.to.as_str().to_string(),
            c.label.clone(),
        ),
    }
}

/// Orientation dedup: drop an arc that restates another one from the other end.
/// Deletes only.
pub(crate) fn orientation_dedup(
    arcs: Vec<OCDeclareArc>,
    facts: &HashMap<String, HashMap<String, ActivityObjectFacts>>,
) -> Vec<OCDeclareArc> {
    let mut groups: HashMap<DedupKey, Vec<OCDeclareArc>> = HashMap::new();
    for c in arcs {
        groups.entry(dedup_key(&c, facts)).or_default().push(c);
    }
    let sym_pairs: HashSet<(String, String, OCDeclareArcLabel)> = groups
        .keys()
        .filter_map(|k| match k {
            DedupKey::Symmetric(a, b, l) => Some((a.clone(), b.clone(), l.clone())),
            _ => None,
        })
        .collect();
    let mut kept: Vec<OCDeclareArc> = Vec::new();
    for (key, mut group) in groups {
        if let DedupKey::Ordered(a, b, l) = &key {
            let (lo, hi) = if a <= b { (a.clone(), b.clone()) } else { (b.clone(), a.clone()) };
            if sym_pairs.contains(&(lo, hi, l.clone())) {
                continue;
            }
        }
        group.sort();
        kept.push(group.into_iter().next().unwrap());
    }
    kept
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::core::event_data::object_centric::linked_ocel::SlimLinkedOCEL;
    use crate::core::process_models::oc_declare::{
        OCDeclareArcLabel, OCDeclareArcType, OCDeclareNode, ObjectInvolvementCounts,
        ObjectTypeAssociation,
    };
    use std::collections::HashMap;

    fn arc(from: &str, to: &str, arc_type: OCDeclareArcType, label: OCDeclareArcLabel) -> OCDeclareArc {
        OCDeclareArc {
            from: OCDeclareNode::new(from),
            to: OCDeclareNode::new(to),
            arc_type,
            label,
            counts: (Some(0), Some(0)),
        }
    }

    fn any_label(ot: &str) -> OCDeclareArcLabel {
        OCDeclareArcLabel {
            each: Vec::new(),
            any: vec![ObjectTypeAssociation::new_simple(ot)],
            all: Vec::new(),
        }
    }
    fn all_label(ot: &str) -> OCDeclareArcLabel {
        OCDeclareArcLabel {
            each: Vec::new(),
            any: Vec::new(),
            all: vec![ObjectTypeAssociation::new_simple(ot)],
        }
    }

    #[test]
    fn cardinality_entailed_when_source_min_exceeds_target_max() {
        let mut inv: HashMap<String, HashMap<String, ObjectInvolvementCounts>> = HashMap::new();
        inv.entry("a".into())
            .or_default()
            .insert("items".into(), ObjectInvolvementCounts { min: 3, max: 5 });
        inv.entry("b".into())
            .or_default()
            .insert("items".into(), ObjectInvolvementCounts { min: 1, max: 2 });
        let c = arc("a", "b", OCDeclareArcType::AS, all_label("items"));
        assert!(cardinality_entailed(&c, &inv, &facts_always_present("a", "items")));
        // Same counts, but some `a`-event carries no item at all: there the containment is
        // vacuous and the constraint can be violated, so it must not be dropped.
        assert!(!cardinality_entailed(&c, &inv, &HashMap::new()));
    }

    #[test]
    fn cardinality_not_entailed_when_target_can_keep_up() {
        let mut inv: HashMap<String, HashMap<String, ObjectInvolvementCounts>> = HashMap::new();
        inv.entry("a".into())
            .or_default()
            .insert("items".into(), ObjectInvolvementCounts { min: 1, max: 5 });
        inv.entry("b".into())
            .or_default()
            .insert("items".into(), ObjectInvolvementCounts { min: 1, max: 5 });
        let c = arc("a", "b", OCDeclareArcType::AS, all_label("items"));
        assert!(!cardinality_entailed(&c, &inv, &facts_always_present("a", "items")));
    }

    #[test]
    fn domination_drops_the_strong_side_not_the_weak_side() {
        // AS -/-> Any(items), satisfied, dominates EF -/-> Any(items) same pair (AS <= EF in
        // arrow order) -- the EF one is redundant and must be dropped, not the AS one.
        let weak_arrow = arc("a", "b", OCDeclareArcType::AS, any_label("items"));
        let strong_arrow = arc("a", "b", OCDeclareArcType::EF, any_label("items"));
        let kept = drop_dominated(vec![weak_arrow.clone(), strong_arrow]);
        assert_eq!(kept, vec![weak_arrow]);

        // Any(items) dominates All(items) same activity pair+arrow (Any <= All in involvement
        // order) -- the All one is redundant.
        let weak_label = arc("a", "b", OCDeclareArcType::AS, any_label("items"));
        let strong_label = arc("a", "b", OCDeclareArcType::AS, all_label("items"));
        let kept = drop_dominated(vec![weak_label.clone(), strong_label]);
        assert_eq!(kept, vec![weak_label]);
    }

    fn each_label(ot: &str) -> OCDeclareArcLabel {
        OCDeclareArcLabel {
            each: vec![ObjectTypeAssociation::new_simple(ot)],
            any: Vec::new(),
            all: Vec::new(),
        }
    }

    #[test]
    fn reachable_pairs_transitively_closes_admissible_arrows_only() {
        use std::collections::HashSet;
        let existing = vec![
            arc("a", "b", OCDeclareArcType::EF, each_label("items")),
            arc("b", "c", OCDeclareArcType::DF, each_label("items")),
            arc("a", "z", OCDeclareArcType::AS, each_label("items")), // wrong arrow, must not connect
        ];
        let admissible: HashSet<_> = tgt_admissible(OCDeclareArcType::EF); // {EF, DF}
        let pairs = reachable_pairs(&existing, &admissible, "items");
        assert!(pairs.contains(&("a".to_string(), "b".to_string())));
        assert!(pairs.contains(&("b".to_string(), "c".to_string())));
        assert!(pairs.contains(&("a".to_string(), "c".to_string()))); // transitive
        assert!(!pairs.iter().any(|(_, t)| t == "z"));
    }

    #[test]
    fn admissible_tables_include_df_dp() {
        use OCDeclareArcType::*;
        let src_ef: std::collections::HashSet<_> = src_admissible(EF);
        assert_eq!(src_ef, [EP, DP].into_iter().collect());
        let tgt_ef: std::collections::HashSet<_> = tgt_admissible(EF);
        assert_eq!(tgt_ef, [EF, DF].into_iter().collect());
        assert!(src_admissible(DF).is_empty());
        assert!(tgt_admissible(DP).is_empty());
    }

    use crate::core::process_models::oc_declare::ActivityObjectFacts;

    fn requiring(from: &str, to: &str, arc_type: OCDeclareArcType, label: OCDeclareArcLabel) -> OCDeclareArc {
        OCDeclareArc {
            counts: (Some(1), None),
            ..arc(from, to, arc_type, label)
        }
    }

    fn facts_always_present(activity: &str, ot: &str) -> HashMap<String, HashMap<String, ActivityObjectFacts>> {
        let mut facts: HashMap<String, HashMap<String, ActivityObjectFacts>> = HashMap::new();
        facts.entry(activity.into()).or_default().insert(
            ot.into(),
            ActivityObjectFacts {
                always_present: true,
                at_most_one_event_per_object: false,
            },
        );
        facts
    }

    #[test]
    fn source_anchored_derives_when_source_carries_the_type() {
        // d_r = EP A -> B [items: Each], d_f = AS B -/-> C [items: Any]
        // => d_n = AS A -/-> C [items: Any].
        let d_r = requiring("A", "B", OCDeclareArcType::EP, each_label("items"));
        let d_f = arc("B", "C", OCDeclareArcType::AS, any_label("items"));
        let d_n = arc("A", "C", OCDeclareArcType::AS, any_label("items"));
        let m1 = vec![d_f.clone(), d_n.clone()];
        let facts = facts_always_present("A", "items");

        let edges = source_anchored_edges(&m1, &[d_r], &facts);
        assert_eq!(edges.get(&d_f), Some(&[d_n].into_iter().collect()));
    }

    #[test]
    fn source_anchored_does_not_derive_when_carry_condition_fails() {
        let d_r = requiring("A", "B", OCDeclareArcType::EP, each_label("items"));
        let d_f = arc("B", "C", OCDeclareArcType::AS, any_label("items"));
        let d_n = arc("A", "C", OCDeclareArcType::AS, any_label("items"));
        let m1 = vec![d_f.clone(), d_n];

        let edges = source_anchored_edges(&m1, &[d_r], &HashMap::new());
        assert!(edges.get(&d_f).map(|s| s.is_empty()).unwrap_or(true));
    }

    #[test]
    fn source_anchored_never_admits_all_on_the_forbidding_side() {
        let d_r = requiring("A", "B", OCDeclareArcType::EP, each_label("items"));
        let d_f = arc("B", "C", OCDeclareArcType::AS, all_label("items"));
        let d_n = arc("A", "C", OCDeclareArcType::AS, all_label("items"));
        let m1 = vec![d_f.clone(), d_n];
        let facts = facts_always_present("A", "items");

        let edges = source_anchored_edges(&m1, &[d_r], &facts);
        assert!(edges.get(&d_f).map(|s| s.is_empty()).unwrap_or(true));
    }

    #[test]
    fn source_anchored_derives_via_a_two_hop_path() {
        // EP A -> B [items: Each], EP B -> D [items: Each], d_f on D -/-> C
        let d_r1 = requiring("A", "B", OCDeclareArcType::EP, each_label("items"));
        let d_r2 = requiring("B", "D", OCDeclareArcType::EP, each_label("items"));
        let d_f = arc("D", "C", OCDeclareArcType::AS, any_label("items"));
        let d_n = arc("A", "C", OCDeclareArcType::AS, any_label("items"));
        let m1 = vec![d_f.clone(), d_n.clone()];
        let facts = facts_always_present("A", "items");

        let edges = source_anchored_edges(&m1, &[d_r1, d_r2], &facts);
        assert_eq!(edges.get(&d_f), Some(&[d_n].into_iter().collect()));
    }

    #[test]
    fn target_anchored_permits_all_unlike_source_anchored() {
        let d_r = requiring("C", "B", OCDeclareArcType::EF, all_label("items"));
        let premise = arc("A", "B", OCDeclareArcType::AS, all_label("items"));
        let derived = arc("A", "C", OCDeclareArcType::AS, all_label("items"));
        let m1 = vec![premise.clone(), derived.clone()];
        let facts = facts_always_present("B", "items");

        let edges = target_anchored_edges(&m1, &[d_r]);
        assert_eq!(edges.get(&premise), Some(&[derived].into_iter().collect()));
    }

    #[test]
    fn target_anchored_rejects_an_each_premise_for_an_all_involved_type() {
        // `Each` on the premise pins one shared object; the proof for an `All`-involved type
        // needs obj(e'') subseteq obj(e'''), which only an `All` premise gives.
        let d_r = requiring("C", "B", OCDeclareArcType::EF, each_label("items"));
        let premise = arc("A", "B", OCDeclareArcType::AS, all_label("items"));
        let derived = arc("A", "C", OCDeclareArcType::AS, all_label("items"));
        let m1 = vec![premise.clone(), derived];
        let facts = facts_always_present("B", "items");

        let edges = target_anchored_edges(&m1, &[d_r]);
        assert!(edges.get(&premise).map(|s| s.is_empty()).unwrap_or(true));
    }

    /// The proposition asks nothing of the shared target `B`, so the derivation fires with no
    /// log facts at all. Contrast `source_anchored_does_not_derive_when_carry_condition_fails`,
    /// where the two constraints have different sources and condition (iv) is load-bearing.
    #[test]
    fn target_anchored_needs_no_carry_condition_on_the_shared_target() {
        let d_r = requiring("C", "B", OCDeclareArcType::EF, all_label("items"));
        let premise = arc("A", "B", OCDeclareArcType::AS, all_label("items"));
        let derived = arc("A", "C", OCDeclareArcType::AS, all_label("items"));
        let m1 = vec![premise.clone(), derived.clone()];

        let edges = target_anchored_edges(&m1, &[d_r]);
        assert!(edges.get(&premise).is_some_and(|s| s.contains(&derived)));
    }

    #[test]
    fn mutual_entailment_survives_condensation_only_one_dropped() {
        // X and Y each require the other beforehand on `items` (EP both ways), so a negative
        // constraint on Y -/-> Z composes to X -/-> Z and vice versa -- a genuine 2-cycle.
        let existing = vec![
            requiring("X", "Y", OCDeclareArcType::EP, each_label("items")),
            requiring("Y", "X", OCDeclareArcType::EP, each_label("items")),
        ];
        let c1 = arc("X", "Z", OCDeclareArcType::AS, any_label("items"));
        let c2 = arc("Y", "Z", OCDeclareArcType::AS, any_label("items"));
        let m1 = vec![c1.clone(), c2.clone()];
        let facts = {
            let mut f = facts_always_present("X", "items");
            f.entry("Y".into()).or_default().insert(
                "items".into(),
                ActivityObjectFacts {
                    always_present: true,
                    at_most_one_event_per_object: false,
                },
            );
            f
        };

        let edges = source_anchored_edges(&m1, &existing, &facts);
        assert!(edges.get(&c1).is_some_and(|s| s.contains(&c2)));
        assert!(edges.get(&c2).is_some_and(|s| s.contains(&c1)));

        let kept = condense(&m1, &edges);
        assert_eq!(kept.len(), 1, "exactly one of the mutually-entailing pair must survive");
        assert!(kept[0] == c1 || kept[0] == c2);
    }

    #[test]
    fn a_component_with_an_incoming_edge_is_dropped_entirely() {
        // c1 entails c2 one-directionally (no edge back) -- c1 is a root component (kept),
        // c2's component has an incoming edge and is dropped entirely.
        let c1 = arc("A", "Z", OCDeclareArcType::AS, any_label("items"));
        let c2 = arc("B", "Z", OCDeclareArcType::AS, any_label("items"));
        let m1 = vec![c1.clone(), c2.clone()];
        let mut edges: HashMap<OCDeclareArc, HashSet<OCDeclareArc>> = HashMap::new();
        edges.entry(c1.clone()).or_default().insert(c2);

        let kept = condense(&m1, &edges);
        assert_eq!(kept, vec![c1]);
    }

    #[test]
    fn rule_b_removes_a_structurally_guaranteed_constraint() {
        let existing = vec![requiring("s", "t", OCDeclareArcType::EP, each_label("items"))];
        let mut facts: HashMap<String, HashMap<String, ActivityObjectFacts>> = HashMap::new();
        facts.entry("s".into()).or_default().insert(
            "items".into(),
            ActivityObjectFacts {
                always_present: true,
                at_most_one_event_per_object: false,
            },
        );
        facts.entry("t".into()).or_default().insert(
            "items".into(),
            ActivityObjectFacts {
                always_present: true,
                at_most_one_event_per_object: true,
            },
        );
        let c = arc("s", "t", OCDeclareArcType::EF, any_label("items"));
        assert!(rule_b_removable(&c, &existing, &facts));
    }

    #[test]
    fn rule_b_does_not_remove_without_the_opposite_direction_path() {
        let mut facts: HashMap<String, HashMap<String, ActivityObjectFacts>> = HashMap::new();
        facts.entry("s".into()).or_default().insert(
            "items".into(),
            ActivityObjectFacts {
                always_present: true,
                at_most_one_event_per_object: false,
            },
        );
        facts.entry("t".into()).or_default().insert(
            "items".into(),
            ActivityObjectFacts {
                always_present: true,
                at_most_one_event_per_object: true,
            },
        );
        let c = arc("s", "t", OCDeclareArcType::EF, any_label("items"));
        assert!(!rule_b_removable(&c, &[], &facts));
    }

    #[test]
    fn dedup_collapses_as_symmetric_restatement() {
        let mut facts = facts_always_present("s", "items");
        facts.entry("t".into()).or_default().insert(
            "items".into(),
            ActivityObjectFacts {
                always_present: true,
                at_most_one_event_per_object: false,
            },
        );
        let c1 = arc("s", "t", OCDeclareArcType::AS, any_label("items"));
        let c2 = arc("t", "s", OCDeclareArcType::AS, any_label("items"));
        let kept = orientation_dedup(vec![c1, c2], &facts);
        assert_eq!(kept.len(), 1);
    }

    #[test]
    fn dedup_collapses_ef_ep_restatement() {
        let mut facts = facts_always_present("s", "items");
        facts.entry("t".into()).or_default().insert(
            "items".into(),
            ActivityObjectFacts {
                always_present: true,
                at_most_one_event_per_object: false,
            },
        );
        let c1 = arc("s", "t", OCDeclareArcType::EF, any_label("items"));
        let c2 = arc("t", "s", OCDeclareArcType::EP, any_label("items"));
        let kept = orientation_dedup(vec![c1, c2], &facts);
        assert_eq!(kept.len(), 1);
    }

    #[test]
    fn dedup_never_collapses_all_involvement() {
        let mut facts = facts_always_present("s", "items");
        facts.entry("t".into()).or_default().insert(
            "items".into(),
            ActivityObjectFacts {
                always_present: true,
                at_most_one_event_per_object: false,
            },
        );
        let c1 = arc("s", "t", OCDeclareArcType::AS, all_label("items"));
        let c2 = arc("t", "s", OCDeclareArcType::AS, all_label("items"));
        let kept = orientation_dedup(vec![c1, c2], &facts);
        assert_eq!(kept.len(), 2);
    }

    /// Both `X` and `Y` carry `items` on every event, so the carry condition (Task 6/7) holds
    /// and source-anchored composition actually fires in both directions.
    fn two_cycle_locel() -> SlimLinkedOCEL {
        use crate::core::event_data::object_centric::{
            appendable::AppendableOCEL, OCELRelationship, OCELType,
        };
        use chrono::DateTime;
        let mut s = SlimLinkedOCEL::new();
        for et in ["X", "Y", "Z"] {
            s.declare_event_type(OCELType {
                name: et.into(),
                attributes: Vec::new(),
            })
            .unwrap();
        }
        s.declare_object_type(OCELType {
            name: "items".into(),
            attributes: Vec::new(),
        })
        .unwrap();
        s.append_object("i1".into(), "items", Vec::new(), Vec::new()).unwrap();
        let t = |i: u32| DateTime::parse_from_rfc3339(&format!("2024-01-0{i}T00:00:00Z")).unwrap();
        let rel = OCELRelationship {
            object_id: "i1".into(),
            qualifier: "q".into(),
        };
        s.append_event("x1".into(), "X", t(1), Vec::new(), vec![rel.clone()])
            .unwrap();
        s.append_event("y1".into(), "Y", t(2), Vec::new(), vec![rel])
            .unwrap();
        s.finalize().unwrap();
        s
    }

    #[test]
    fn reduce_negative_oc_declare_survives_the_2_cycle_end_to_end() {
        use crate::discovery::object_centric::oc_declare::negative::reduce_negative_oc_declare;

        let locel = two_cycle_locel();
        let existing = vec![
            requiring("X", "Y", OCDeclareArcType::EP, each_label("items")),
            requiring("Y", "X", OCDeclareArcType::EP, each_label("items")),
        ];
        let c1 = arc("X", "Z", OCDeclareArcType::AS, any_label("items"));
        let c2 = arc("Y", "Z", OCDeclareArcType::AS, any_label("items"));

        let result = reduce_negative_oc_declare(&locel, &existing, vec![c1.clone(), c2.clone()]);
        assert_eq!(result.len(), 1);
        assert!(result[0] == c1 || result[0] == c2);
    }
}
