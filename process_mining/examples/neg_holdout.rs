//! Held-out check of discovered and reduced negative OC-DECLARE models.
//!
//! The models are discovered (and the negative ones reduced) on the events before a time cut.
//! Every source event after the cut is then checked against the full log, so that targets
//! before the cut stay in scope. Reported per noise threshold:
//! - how many reduced constraints still hold on the held-out source events,
//! - the held-out source events flagged by the discovered and by the reduced model,
//! - flagged events that only the discovered model reports (lost by the reduction),
//! - how many existence premises and structural properties of the training part fail,
//! - the checking time of both models on the held-out source events.
//!
//! Usage:
//!   cargo run --release --example neg_holdout -- <log> [--train=0.7] [--taus=0,0.2]

use std::{
    collections::{HashMap, HashSet},
    env,
    path::PathBuf,
    time::Instant,
};

use process_mining::{
    conformance::object_centric::oc_declare::arc_violated_at,
    core::{
        event_data::object_centric::linked_ocel::{
            slim_linked_ocel::EventIndex, LinkedOCELAccess, SlimLinkedOCEL,
        },
        process_models::oc_declare::{EventOrSynthetic, OCDeclareArc, OCDeclareArcType},
    },
    discovery::object_centric::oc_declare::{
        discover_behavior_constraints,
        negative::{
            discover_negative_oc_declare, reduce_negative_oc_declare,
            NegativeOCDeclareDiscoveryOptions,
        },
        O2OMode, OCDeclareDiscoveryOptions, OCDeclareReductionMode,
    },
    Importable, OCEL,
};

type Facts = (HashMap<(String, String), (usize, usize)>, HashSet<(String, String)>);

/// Multiplicity ranges and uniqueness per (activity, object type).
fn structural(locel: &SlimLinkedOCEL) -> Facts {
    let ots: Vec<String> = locel.get_ob_types().map(|s| s.to_string()).collect();
    let mut mult = HashMap::new();
    let mut unique = HashSet::new();
    for et in locel.get_ev_types() {
        let mut seen: HashMap<String, HashSet<_>> = HashMap::new();
        let mut dup: HashSet<String> = HashSet::new();
        let mut range: HashMap<String, (usize, usize)> =
            ots.iter().map(|o| (o.clone(), (usize::MAX, 0))).collect();
        let mut any = false;
        for ev in locel.get_evs_of_type(et) {
            any = true;
            let mut c: HashMap<&str, HashSet<_>> = HashMap::new();
            for o in ev.get_e2o(locel) {
                c.entry(o.get_ob_type(locel)).or_default().insert(o);
            }
            for ot in &ots {
                let objs = c.get(ot.as_str());
                let n = objs.map(|s| s.len()).unwrap_or(0);
                let r = range.get_mut(ot).unwrap();
                r.0 = r.0.min(n);
                r.1 = r.1.max(n);
                for o in objs.into_iter().flatten() {
                    if !seen.entry(ot.clone()).or_default().insert(*o) {
                        dup.insert(ot.clone());
                    }
                }
            }
        }
        if !any {
            continue;
        }
        for ot in &ots {
            mult.insert((et.to_string(), ot.clone()), range[ot]);
            if seen.contains_key(ot) && !dup.contains(ot) {
                unique.insert((et.to_string(), ot.clone()));
            }
        }
    }
    (mult, unique)
}

fn violates(locel: &SlimLinkedOCEL, a: &OCDeclareArc, e: &EventIndex) -> bool {
    arc_violated_at(locel, a, &EventOrSynthetic::Event(*e))
}

/// Flagged held-out events of a model and the violations per arc.
fn check(
    locel: &SlimLinkedOCEL,
    model: &[OCDeclareArc],
    test: &HashMap<String, Vec<EventIndex>>,
) -> (HashSet<EventIndex>, Vec<usize>, f64) {
    let t = Instant::now();
    let mut flagged = HashSet::new();
    let mut per_arc = Vec::new();
    for a in model {
        let mut v = 0;
        for e in test.get(a.from.as_str()).into_iter().flatten() {
            if violates(locel, a, e) {
                v += 1;
                flagged.insert(*e);
            }
        }
        per_arc.push(v);
    }
    (flagged, per_arc, t.elapsed().as_secs_f64())
}

/// Of the given events, those that violate an arc of the model themselves.
fn explained(locel: &SlimLinkedOCEL, model: &[OCDeclareArc], evs: &HashSet<EventIndex>) -> usize {
    evs.iter()
        .filter(|e| {
            let et = EventOrSynthetic::Event(**e).get_as_event_type(locel);
            model.iter().any(|a| a.from.as_str() == et && violates(locel, a, e))
        })
        .count()
}

fn main() {
    let mut train_frac = 0.7;
    let mut taus = vec![0.0, 0.2];
    let mut log = None;
    for a in env::args().skip(1) {
        if let Some(v) = a.strip_prefix("--train=") {
            train_frac = v.parse().expect("bad --train");
        } else if let Some(v) = a.strip_prefix("--taus=") {
            taus = v.split(',').map(|s| s.parse().expect("bad tau")).collect();
        } else {
            log = Some(a);
        }
    }
    let log = log.expect("log");
    let ocel = OCEL::import_from_path(PathBuf::from(&log)).expect("import failed");
    let mut times: Vec<_> = ocel.events.iter().map(|e| e.time).collect();
    times.sort();
    let cut = times[(times.len() as f64 * train_frac) as usize];
    let mut train = ocel.clone();
    train.events.retain(|e| e.time < cut);
    println!("== {log}\ncut {cut}: {} training events of {}", train.events.len(), ocel.events.len());
    let full = SlimLinkedOCEL::from_ocel(ocel);
    let train = SlimLinkedOCEL::from_ocel(train);

    let mut test: HashMap<String, Vec<EventIndex>> = HashMap::new();
    let mut seen: HashMap<String, Vec<EventIndex>> = HashMap::new();
    for et in full.get_ev_types() {
        for e in full.get_evs_of_type(et) {
            let part = if EventOrSynthetic::Event(*e).get_timestamp(&full) >= cut {
                &mut test
            } else {
                &mut seen
            };
            part.entry(et.to_string()).or_default().push(*e);
        }
    }
    let n_test: usize = test.values().map(|v| v.len()).sum();
    let (tm, tu) = structural(&train);
    let (fm, fu) = structural(&full);
    let mult_broken = tm
        .iter()
        .filter(|(k, (lo, hi))| fm.get(*k).is_some_and(|(flo, fhi)| flo < lo || fhi > hi))
        .count();
    let uniq_broken = tu.iter().filter(|k| !fu.contains(*k)).count();
    println!(
        "held-out source events {n_test}; structural properties broken on full log: \
         {mult_broken} of {} multiplicities, {uniq_broken} of {} uniqueness",
        tm.len(),
        tu.len()
    );

    let holding = |model: &[OCDeclareArc], viol: &[usize], rho: f64| {
        model
            .iter()
            .zip(viol)
            .filter(|(a, &v)| {
                let n = test.get(a.from.as_str()).map(|x| x.len()).unwrap_or(0);
                n == 0 || (v as f64) <= rho * n as f64
            })
            .count()
    };

    let mut existence_at = HashMap::new();
    for rho in taus.iter().copied().chain([0.2]) {
        let key = format!("{rho}");
        if existence_at.contains_key(&key) {
            continue;
        }
        let ex = discover_behavior_constraints(
            &train,
            OCDeclareDiscoveryOptions {
                noise_threshold: rho,
                o2o_mode: O2OMode::None,
                counts_for_filter: (Some(1), None),
                reduction: OCDeclareReductionMode::None,
                considered_arrow_types: [
                    OCDeclareArcType::AS,
                    OCDeclareArcType::EF,
                    OCDeclareArcType::EP,
                ]
                .into_iter()
                .collect(),
                all_for_single_valued_types: true,
                ..Default::default()
            },
        );
        let (_, v, _) = check(&full, &ex, &test);
        println!(
            "existence rho={rho}: {} arcs, {} hold on held-out at rho",
            ex.len(),
            holding(&ex, &v, rho)
        );
        existence_at.insert(key, ex);
    }

    for tau in taus {
        let discovered = discover_negative_oc_declare(
            &train,
            NegativeOCDeclareDiscoveryOptions { noise_threshold: tau, ..Default::default() },
        );
        let (fd, _, td) = check(&full, &discovered, &test);
        let (fd_seen, _, _) = check(&full, &discovered, &seen);
        for (setting, ex_key) in [("fixed", "0.2".to_string()), ("matched", format!("{tau}"))] {
            if setting == "matched" && ex_key == "0.2" {
                continue;
            }
            let reduced = reduce_negative_oc_declare(&train, &existence_at[&ex_key], discovered.clone());
            let (fr, vr, tr) = check(&full, &reduced, &test);
            let (fr_seen, _, _) = check(&full, &reduced, &seen);
            let ex = &existence_at[&ex_key];
            let lost: HashSet<EventIndex> = fd.difference(&fr).copied().collect();
            let lost_seen: HashSet<EventIndex> = fd_seen.difference(&fr_seen).copied().collect();
            println!(
                "  lost events violating an existence premise themselves: held-out {} of {}, training {} of {}",
                explained(&full, ex, &lost),
                lost.len(),
                explained(&full, ex, &lost_seen),
                lost_seen.len()
            );
            println!(
                "tau={tau} {setting}: discovered {} -> reduced {}; reduced holding on held-out {} | \
                 held-out flagged discovered {} reduced {} lost {} | training flagged discovered {} \
                 lost {} | check time discovered {td:.2}s reduced {tr:.2}s",
                discovered.len(),
                reduced.len(),
                holding(&reduced, &vr, tau),
                fd.len(),
                fr.len(),
                fd.difference(&fr).count(),
                fd_seen.len(),
                fd_seen.difference(&fr_seen).count()
            );
            for (a, v) in reduced.iter().zip(&vr) {
                let n = test.get(a.from.as_str()).map(|x| x.len()).unwrap_or(0);
                println!(
                    "  ARC\t{setting}\t{tau}\t{}\t{}\t{}\t{}\t{n}\t{v}",
                    a.arc_type.get_name(),
                    a.from.as_str(),
                    a.to.as_str(),
                    a.label.as_template_string()
                );
            }
        }
    }
}
