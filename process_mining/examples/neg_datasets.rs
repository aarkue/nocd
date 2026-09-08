//! Fixed-premise setting of the paper: negative OC-DECLARE discovery and mixed-model
//! reduction on one or more OCEL logs, reporting counts and timings and writing JSON for the
//! existence model and each threshold's discovered and reduced negative model.
//!
//! Usage:
//!   cargo run --release --example neg_datasets -- <log1> [log2 ...] \
//!       [--taus=0.0,0.1,0.2] [--out-dir=DIR]
//!
//! `<logN>` can be any format `OCEL::import_from_path` supports (xml, xml.gz, json, json.gz,
//! jsonocel, ...). `--out-dir` defaults to the current directory. Output files are named
//! `<log-stem>-existence.json` and `<log-stem>-negative-tau<TAU>.json`.
//!
//! Existence discovery deliberately excludes DF/DP (`considered_arrow_types` below): DF/DP
//! checking in `event_violates` does not use the index-seeded fast path (falls through to
//! `directly_adjacent_event`, an unindexed per-object scan), which is fine on small logs but
//! made existence discovery not finish in 7+ minutes on a 1.2M-event log. Excluding them
//! matches the known-fast config already used in `oc_declare_evaluation.rs`. Negative discovery
//! never searches DF/DP as the forbidding arrow regardless, so this only affects which
//! *existence* facts are available as composition/rule-C premises.

use std::{collections::HashSet, env, fs::File, path::PathBuf, time::Instant};

use process_mining::{
    core::{
        event_data::object_centric::linked_ocel::SlimLinkedOCEL,
        process_models::oc_declare::OCDeclareArcType,
    },
    discovery::object_centric::oc_declare::{
        discover_behavior_constraints,
        negative::{
            discover_negative_oc_declare, reduce_negative_oc_declare, NegativeOCDeclareDiscoveryOptions,
        },
        O2OMode, OCDeclareDiscoveryOptions, OCDeclareReductionMode,
    },
    Importable, OCEL,
};

fn main() {
    let mut paths = Vec::new();
    let mut taus = vec![0.0, 0.1, 0.2];
    let mut all_single = true;
    let mut out_dir = PathBuf::from(".");
    for arg in env::args().skip(1) {
        if let Some(v) = arg.strip_prefix("--taus=") {
            taus = v
                .split(',')
                .map(|s| s.parse::<f64>().expect("--taus must be a comma-separated list of numbers"))
                .collect();
        } else if let Some(v) = arg.strip_prefix("--out-dir=") {
            out_dir = PathBuf::from(v);
        } else if arg == "--all-singleton" {
            all_single = true;
        } else if arg == "--no-all-singleton" {
            all_single = false;
        } else {
            paths.push(arg);
        }
    }
    if paths.is_empty() {
        panic!("Provide one or more OCEL file paths as arguments (see the module doc comment for flags).");
    }

    let existence_arrow_types: HashSet<OCDeclareArcType> =
        [OCDeclareArcType::AS, OCDeclareArcType::EF, OCDeclareArcType::EP]
            .into_iter()
            .collect();

    for path in paths {
        println!("=== {path} ===");
        let stem = PathBuf::from(&path)
            .file_stem()
            .map(|s| s.to_string_lossy().into_owned())
            .unwrap_or_else(|| "log".to_string());

        let t0 = Instant::now();
        let ocel = OCEL::import_from_path(PathBuf::from(&path)).expect("failed to import OCEL");
        println!(
            "  loaded: {} events, {} objects ({:?})",
            ocel.events.len(),
            ocel.objects.len(),
            t0.elapsed()
        );
        let t1 = Instant::now();
        let locel = SlimLinkedOCEL::from_ocel(ocel);
        println!("  linked: {:?}", t1.elapsed());

        let t2 = Instant::now();
        let existing = discover_behavior_constraints(
            &locel,
            OCDeclareDiscoveryOptions {
                o2o_mode: O2OMode::None,
                counts_for_filter: (Some(1), None),
                reduction: OCDeclareReductionMode::None,
                considered_arrow_types: existence_arrow_types.clone(),
                all_for_single_valued_types: all_single,
                ..Default::default()
            },
        );
        println!("  existence: {} arcs ({:?})", existing.len(), t2.elapsed());
        let existing_path = out_dir.join(format!("{stem}-existence.json"));
        serde_json::to_writer_pretty(File::create(&existing_path).unwrap(), &existing).unwrap();
        println!("  wrote {}", existing_path.display());

        for tau in &taus {
            let tau = *tau;
            let t3 = Instant::now();
            let negative = discover_negative_oc_declare(
                &locel,
                NegativeOCDeclareDiscoveryOptions {
                    noise_threshold: tau,
                    ..Default::default()
                },
            );
            let discover_time = t3.elapsed();
            let raw_count = negative.len();
            // The reduction ratio is only checkable against the set that was reduced.
            let discovered_path = out_dir.join(format!("{stem}-negative-discovered-tau{tau}.json"));
            serde_json::to_writer_pretty(File::create(&discovered_path).unwrap(), &negative).unwrap();
            // Timed after the write, so the figure is reduction alone rather than reduction plus I/O.
            let t4 = Instant::now();
            let reduced = reduce_negative_oc_declare(&locel, &existing, negative);
            println!(
                "  tau={tau}: discovered {raw_count} -> reduced {} (discover {:?}, reduce {:?})",
                reduced.len(),
                discover_time,
                t4.elapsed()
            );
            let reduced_path = out_dir.join(format!("{stem}-negative-tau{tau}.json"));
            serde_json::to_writer_pretty(File::create(&reduced_path).unwrap(), &reduced).unwrap();
            println!("  wrote {}", reduced_path.display());
        }
        println!();
    }
}
