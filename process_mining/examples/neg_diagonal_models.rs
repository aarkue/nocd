//! Diagonal setting: existence and negative models discovered at the same threshold.
//! Writes `<stem>-diag-tau<TAU>-{existence,existence-reduced,negative-discovered,negative}.json`.
//!
//! Usage:
//!   cargo run --release --example neg_diagonal_models -- <log> [--taus=0.0,0.1,0.2]

use std::{collections::HashSet, env, fs::File, path::PathBuf, time::Instant};

use process_mining::{
    core::{
        event_data::object_centric::linked_ocel::SlimLinkedOCEL,
        process_models::oc_declare::OCDeclareArcType,
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

fn main() {
    let mut path = None;
    let mut taus = vec![0.0, 0.1, 0.2];
    for arg in env::args().skip(1) {
        if let Some(v) = arg.strip_prefix("--taus=") {
            taus = v.split(',').map(|s| s.parse::<f64>().unwrap()).collect();
        } else {
            path = Some(arg);
        }
    }
    let path = path.expect("provide an OCEL path");
    let stem = PathBuf::from(&path)
        .file_stem()
        .unwrap()
        .to_string_lossy()
        .to_string();
    let arrows: HashSet<OCDeclareArcType> =
        [OCDeclareArcType::AS, OCDeclareArcType::EF, OCDeclareArcType::EP].into_iter().collect();
    let ocel = OCEL::import_from_path(&path).expect("failed to import OCEL");
    let locel = SlimLinkedOCEL::from_ocel(ocel);
    let opts = |tau: f64, reduction: OCDeclareReductionMode| OCDeclareDiscoveryOptions {
        noise_threshold: tau,
        o2o_mode: O2OMode::None,
        counts_for_filter: (Some(1), None),
        reduction,
        considered_arrow_types: arrows.clone(),
        all_for_single_valued_types: true,
        ..Default::default()
    };
    println!("{:>5} {:>7} {:>9} {:>7} {:>6} {:>6}", "rho", "exist.", "exist.red", "disc.", "neg.red", "mixed");
    for &tau in &taus {
        let t = Instant::now();
        let existence = discover_behavior_constraints(&locel, opts(tau, OCDeclareReductionMode::None));
        let existence_reduced =
            discover_behavior_constraints(&locel, opts(tau, OCDeclareReductionMode::Lossless));
        let discovered = discover_negative_oc_declare(
            &locel,
            NegativeOCDeclareDiscoveryOptions { noise_threshold: tau, ..Default::default() },
        );
        let reduced = reduce_negative_oc_declare(&locel, &existence, discovered.clone());
        println!(
            "{:>5} {:>7} {:>9} {:>7} {:>6} {:>6}   ({:?})",
            tau,
            existence.len(),
            existence_reduced.len(),
            discovered.len(),
            reduced.len(),
            existence_reduced.len() + reduced.len(),
            t.elapsed()
        );
        write(&stem, tau, "existence", &existence);
        write(&stem, tau, "existence-reduced", &existence_reduced);
        write(&stem, tau, "negative-discovered", &discovered);
        write(&stem, tau, "negative", &reduced);
    }
}

fn write<T: serde::Serialize>(stem: &str, tau: f64, name: &str, v: &T) {
    let p = format!("{stem}-diag-tau{tau}-{name}.json");
    serde_json::to_writer_pretty(File::create(&p).unwrap(), v).unwrap();
}
