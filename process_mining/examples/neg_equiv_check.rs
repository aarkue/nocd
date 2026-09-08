//! Do the derived object-set equivalences hold on the log, and are the rewritings noise-safe?
//!
//! Object-set equivalence (row 5) derives `A ~_S B` from two existence arcs and a unique witness,
//! and then rewrites a negative arc by swapping one endpoint for its partner. Two things have to
//! hold for that to be sound on the log it was derived from. The relation has to be total in both
//! directions event for event, every `A`-event having a `B`-event agreeing on every type in `S`
//! and conversely. And a rewriting must not change how much of the log violates the arc, or the
//! rule would trade a constraint for a weaker one under a noise threshold.
//!
//! This replaces the Python check that used to produce these numbers.
//!
//! Usage:
//!   cargo run --release --example neg_equiv_check -- <log> [--taus=0,0.1,0.2]

use std::{
    collections::{HashMap, HashSet},
    env,
    path::PathBuf,
};

use process_mining::{
    conformance::object_centric::oc_declare::oc_declare_conformance,
    core::{
        event_data::object_centric::linked_ocel::{
            slim_linked_ocel::{EventIndex, ObjectIndex},
            LinkedOCELAccess, SlimLinkedOCEL,
        },
        process_models::oc_declare::{get_activity_object_facts, OCDeclareArc, OCDeclareArcType},
    },
    discovery::object_centric::oc_declare::{
        discover_behavior_constraints,
        negative::{
            derived_equivalences, discover_negative_oc_declare, rule_c_rewritings,
            NegativeOCDeclareDiscoveryOptions,
        },
        O2OMode, OCDeclareDiscoveryOptions, OCDeclareReductionMode,
    },
    Importable, OCEL,
};

fn main() {
    let mut path = None;
    let mut taus = vec![0.0, 0.1, 0.2];
    let mut erho = 0.2f64;
    for arg in env::args().skip(1) {
        if let Some(v) = arg.strip_prefix("--taus=") {
            taus = v.split(',').map(|s| s.parse().expect("bad tau")).collect();
        } else if let Some(v) = arg.strip_prefix("--existence-rho=") {
            erho = v.parse().expect("bad rho");
        } else {
            path = Some(arg);
        }
    }
    let path = path.expect("provide one OCEL file path");
    let ocel = OCEL::import_from_path(PathBuf::from(&path)).expect("failed to import OCEL");
    let locel = SlimLinkedOCEL::from_ocel(ocel);
    println!("\n== {path} (existence rho={erho}) ==");

    let arrows = [
        OCDeclareArcType::AS,
        OCDeclareArcType::EF,
        OCDeclareArcType::EP,
    ];
    let existence = discover_behavior_constraints(
        &locel,
        OCDeclareDiscoveryOptions {
            noise_threshold: erho,
            o2o_mode: O2OMode::None,
            counts_for_filter: (Some(1), None),
            reduction: OCDeclareReductionMode::None,
            considered_arrow_types: arrows.into_iter().collect(),
            all_for_single_valued_types: true,
            ..Default::default()
        },
    );
    let facts = get_activity_object_facts(&locel);

    // Objects of each type carried by an event, as a sorted key, so two events are compared by
    // the object sets themselves and not by identity.
    let obj_key = |ev: &EventIndex, types: &[String]| -> Vec<HashSet<ObjectIndex>> {
        types
            .iter()
            .map(|ot| {
                ev.get_e2o(&locel)
                    .filter(|o| o.get_ob_type(&locel) == ot)
                    .copied()
                    .collect()
            })
            .collect()
    };

    let eqs = derived_equivalences(&existence, &facts);
    let mut paired = 0usize;
    let mut broken = 0usize;
    for (s, a, b) in &eqs {
        let types: Vec<String> = s.iter().cloned().collect();
        let keys_a: Vec<Vec<HashSet<ObjectIndex>>> = locel
            .get_evs_of_type(a)
            .map(|e| obj_key(e, &types))
            .collect();
        let keys_b: Vec<Vec<HashSet<ObjectIndex>>> = locel
            .get_evs_of_type(b)
            .map(|e| obj_key(e, &types))
            .collect();
        for k in &keys_a {
            if keys_b.contains(k) {
                paired += 1;
            } else {
                broken += 1;
            }
        }
        for k in &keys_b {
            if keys_a.contains(k) {
                paired += 1;
            } else {
                broken += 1;
            }
        }
    }
    println!(
        "{} derived object-set equivalences, {paired} paired events, {broken} unpaired",
        eqs.len()
    );

    for tau in taus {
        let negative = discover_negative_oc_declare(
            &locel,
            NegativeOCDeclareDiscoveryOptions {
                noise_threshold: tau,
                ..Default::default()
            },
        );
        let rewritings = rule_c_rewritings(&negative, &existence, &facts);
        let violating = |c: &OCDeclareArc| -> usize {
            let n = locel.get_evs_of_type(c.from.as_str()).count();
            ((1.0 - oc_declare_conformance(&locel, c)) * n as f64).round() as usize
        };
        let mut cache: HashMap<OCDeclareArc, usize> = HashMap::new();
        // AS transport makes the matching sets coincide, so the violating count must be
        // preserved. EF/EP transport only needs a scope inclusion, so it may differ.
        let (mut as_n, mut as_changed, mut ord_n, mut ord_changed) = (0usize, 0usize, 0usize, 0usize);
        for (p, c) in &rewritings {
            let vp = *cache.entry(p.clone()).or_insert_with(|| violating(p));
            let vc = *cache.entry(c.clone()).or_insert_with(|| violating(c));
            if p.arc_type == OCDeclareArcType::AS {
                as_n += 1;
                if vp != vc {
                    as_changed += 1;
                }
            } else {
                ord_n += 1;
                if vp != vc {
                    ord_changed += 1;
                }
            }
        }
        println!(
            "tau={tau}: {} rewritings, AS {as_n} ({as_changed} change violating count), EF/EP {ord_n} ({ord_changed} change)",
            rewritings.len()
        );
    }
}
