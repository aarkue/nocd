//! Per-stage removal counts for the negative OC-DECLARE reduction pipeline.
//!
//! Usage:
//!   cargo run --release --example neg_reduction_stages -- <log> \
//!       [--taus=0,0.1,0.2] [--arrows=AS,EF,EP]
//!
//! `--arrows` restricts the arrow types of the *existence* model. All five do not terminate in
//! reasonable time on the two large logs.

use std::{env, path::PathBuf};

use process_mining::{
    core::{
        event_data::object_centric::linked_ocel::SlimLinkedOCEL,
        process_models::oc_declare::{OCDeclareArcType, ALL_OC_DECLARE_ARC_TYPES},
    },
    discovery::object_centric::oc_declare::{
        discover_behavior_constraints,
        negative::{
            discover_negative_oc_declare, reduce_negative_oc_declare_traced,
            NegativeOCDeclareDiscoveryOptions, ReductionTrace,
        },
        O2OMode, OCDeclareDiscoveryOptions, OCDeclareReductionMode,
    },
    Importable, OCEL,
};

fn main() {
    let mut path = None;
    let mut all_single = true;
    let mut taus = vec![0.0, 0.1, 0.2];
    // Existence discovery over all five arrow types does not terminate in reasonable time on
    // the two large logs, so the arrow set is a flag rather than the default.
    let mut existence_arrows: Vec<OCDeclareArcType> = ALL_OC_DECLARE_ARC_TYPES.to_vec();
    for arg in env::args().skip(1) {
        if let Some(v) = arg.strip_prefix("--arrows=") {
            existence_arrows = v
                .split(',')
                .map(|a| OCDeclareArcType::parse_str(a.trim().to_uppercase())
                    .expect("bad arrow type"))
                .collect();
        } else if let Some(v) = arg.strip_prefix("--taus=") {
            taus = v.split(',').map(|s| s.parse().expect("bad tau")).collect();
        } else if arg == "--all-singleton" {
            all_single = true;
        } else if arg == "--no-all-singleton" {
            all_single = false;
        } else {
            path = Some(arg);
        }
    }
    let path = path.expect("provide one OCEL file path");

    let ocel = OCEL::import_from_path(PathBuf::from(&path)).expect("failed to import OCEL");
    let locel = SlimLinkedOCEL::from_ocel(ocel);
    let existing = discover_behavior_constraints(
        &locel,
        OCDeclareDiscoveryOptions {
            o2o_mode: O2OMode::None,
            counts_for_filter: (Some(1), None),
            reduction: OCDeclareReductionMode::None,
            considered_arrow_types: existence_arrows.iter().copied().collect(),
            all_for_single_valued_types: all_single,
            ..Default::default()
        },
    );

    println!("\n== {path} ==");
    println!(
        "existence model: {} arcs (arrows: {})",
        existing.len(),
        existence_arrows
            .iter()
            .map(|a| a.get_name())
            .collect::<Vec<_>>()
            .join(",")
    );

    for tau in taus {
        let negative = discover_negative_oc_declare(
            &locel,
            NegativeOCDeclareDiscoveryOptions {
                noise_threshold: tau,
                ..Default::default()
            },
        );
        let (_, t) = reduce_negative_oc_declare_traced(&locel, &existing, negative);
        report(tau, &t);
    }
}

fn report(tau: f64, t: &ReductionTrace) {
    let pct = |n: usize| 100.0 * n as f64 / t.input.max(1) as f64;
    println!("--- tau = {tau} ---");
    println!("{:>30} {:>8} {:>9}", "stage", "removed", "share");
    let rows: [(&str, usize); 6] = [
        ("1. cardinality entailment", t.cardinality_entailed),
        ("2. within-pair domination", t.dominated),
        ("3-6. condensation of 3,4,5", t.condensation),
        ("7. rule B / B'", t.rule_b),
        ("8. orientation dedup", t.orientation_dedup),
        ("total", t.input - t.output),
    ];
    for (name, n) in rows {
        println!("{name:>30} {n:>8} {:>8.1}%", pct(n));
    }
    println!(
        "{:>30} {} -> {}",
        "model size",
        t.input,
        t.output
    );
    println!("\n  derivation edges contributed and what each rule alone would condense away:");
    println!("{:>30} {:>8} {:>16}", "rule", "edges", "removed alone");
    println!(
        "{:>30} {:>8} {:>16}",
        "3. source-anchored", t.source_anchored_edges, t.condensation_source_alone
    );
    println!(
        "{:>30} {:>8} {:>16}",
        "4. target-anchored", t.target_anchored_edges, t.condensation_target_alone
    );
    println!(
        "{:>30} {:>8} {:>16}",
        "5. object-set equivalence", t.rule_c_edges, t.condensation_rule_c_alone
    );
    println!();
}
