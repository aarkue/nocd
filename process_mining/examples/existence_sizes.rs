//! Existence-model size as a function of the noise threshold, discovered and reduced.
//!
//! The negative side of the paper holds one existence model fixed as composition premises; this
//! reports how that model would move with its own threshold, and what the existing lossless and
//! lossy transitive reductions leave of it.
//!
//! Usage:
//!   cargo run --release --example existence_sizes -- <log> [--taus=0,0.1,0.2] [--arrows=AS,EF,EP]

use std::{env, path::PathBuf};

use process_mining::{
    core::{
        event_data::object_centric::linked_ocel::SlimLinkedOCEL,
        process_models::oc_declare::{OCDeclareArcType, ALL_OC_DECLARE_ARC_TYPES},
    },
    discovery::object_centric::oc_declare::{
        discover_behavior_constraints, O2OMode, OCDeclareDiscoveryOptions, OCDeclareReductionMode,
    },
    Importable, OCEL,
};

fn main() {
    let mut path = None;
    let mut taus = vec![0.0, 0.05, 0.1, 0.15, 0.2, 0.25, 0.3];
    let mut arrows: Vec<OCDeclareArcType> = ALL_OC_DECLARE_ARC_TYPES.to_vec();
    for arg in env::args().skip(1) {
        if let Some(v) = arg.strip_prefix("--arrows=") {
            arrows = v
                .split(',')
                .map(|a| {
                    OCDeclareArcType::parse_str(a.trim().to_uppercase()).expect("bad arrow type")
                })
                .collect();
        } else if let Some(v) = arg.strip_prefix("--taus=") {
            taus = v.split(',').map(|s| s.parse().expect("bad tau")).collect();
        } else {
            path = Some(arg);
        }
    }
    let path = path.expect("provide one OCEL file path");

    let ocel = OCEL::import_from_path(PathBuf::from(&path)).expect("failed to import OCEL");
    let locel = SlimLinkedOCEL::from_ocel(ocel);

    println!("\n== {path} ==");
    println!(
        "arrows: {}",
        arrows.iter().map(|a| a.get_name()).collect::<Vec<_>>().join(",")
    );
    println!(
        "{:>6} {:>12} {:>12} {:>10} {:>12} {:>10}",
        "rho", "discovered", "lossless", "kept %", "lossy", "kept %"
    );
    for tau in taus {
        let opts = |reduction| OCDeclareDiscoveryOptions {
            noise_threshold: tau,
            o2o_mode: O2OMode::None,
            counts_for_filter: (Some(1), None),
            reduction,
            considered_arrow_types: arrows.iter().copied().collect(),
            all_for_single_valued_types: true,
            ..Default::default()
        };
        let raw = discover_behavior_constraints(&locel, opts(OCDeclareReductionMode::None));
        let lossless =
            discover_behavior_constraints(&locel, opts(OCDeclareReductionMode::Lossless));
        let lossy = discover_behavior_constraints(&locel, opts(OCDeclareReductionMode::Lossy));
        let pct = |n: usize| 100.0 * n as f64 / raw.len().max(1) as f64;
        println!(
            "{tau:>6.2} {:>12} {:>12} {:>9.1}% {:>12} {:>9.1}%",
            raw.len(),
            lossless.len(),
            pct(lossless.len()),
            lossy.len(),
            pct(lossy.len())
        );
    }
}
