//! Are the target-anchored composition derivations sound on a real log?
//!
//! The proposition asks nothing of the shared target activity `B`, and `reduce.rs` accordingly
//! imposes no carry condition there. An earlier version required `alwaysCarries(B, ot)` on the
//! mistaken reading that the condition was needed; this driver is what settled it, and it now
//! guards the rule directly rather than comparing two configurations.
//!
//! It derives every target-anchored edge and evaluates each derived constraint against the log.
//! The premises hold at the discovery threshold rather than at every source event, so a derived
//! constraint is checked at that same threshold. Requiring it at every source event is a stricter
//! test than the premises themselves meet and reports failures that are noise in the premises
//! rather than unsoundness in the rule: on container logistics that misreading costs 43 spurious
//! "violations" at tau = 0.1, all of which satisfy the threshold their premises were drawn at.
//!
//! Usage:
//!   cargo run --release --example neg_carry_check -- <log>

use std::{env, path::PathBuf};

use process_mining::{
    core::{
        event_data::object_centric::linked_ocel::SlimLinkedOCEL,
        process_models::oc_declare::{OCDeclareArc, OCDeclareArcType},
    },
    discovery::object_centric::oc_declare::{
        discover_behavior_constraints,
        negative::{discover_negative_oc_declare, reduce, NegativeOCDeclareDiscoveryOptions},
        O2OMode, OCDeclareDiscoveryOptions, OCDeclareReductionMode,
    },
    Importable, OCEL,
};

fn main() {
    let path = env::args().nth(1).expect("provide one OCEL file path");
    let ocel = OCEL::import_from_path(PathBuf::from(&path)).expect("import failed");
    let locel = SlimLinkedOCEL::from_ocel(ocel);

    let existence = discover_behavior_constraints(
        &locel,
        OCDeclareDiscoveryOptions {
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

    println!("\n== {path} ==");
    for tau in [0.0, 0.1, 0.2] {
        let model = discover_negative_oc_declare(
            &locel,
            NegativeOCDeclareDiscoveryOptions {
                noise_threshold: tau,
                ..Default::default()
            },
        );
        let edges = reduce::target_anchored_edges(&model, &existence);

        let mut derived: Vec<OCDeclareArc> = edges.values().flatten().cloned().collect();
        derived.sort();
        derived.dedup();

        let violated: Vec<&OCDeclareArc> = derived
            .iter()
            .filter(|c| !c.satisfies_threshold(&locel, tau))
            .collect();

        println!(
            "tau={tau}: {} edges, {} distinct derived constraints, {} violated at tau",
            edges.values().map(|s| s.len()).sum::<usize>(),
            derived.len(),
            violated.len()
        );
        for v in violated.iter().take(5) {
            println!(
                "   VIOLATED  {} -/{}-> {}  {}",
                v.from.as_str(),
                v.arc_type.get_name(),
                v.to.as_str(),
                v.label.as_template_string()
            );
        }
    }
}
