//! Does the joint arrow/involvement search return an antichain?
//!
//! Usage:
//!   cargo run --release --example neg_antichain_check -- <log> [--taus=0,0.1,0.2]

use std::{collections::HashSet, env, path::PathBuf};

use process_mining::{
    core::{
        event_data::object_centric::linked_ocel::{LinkedOCELAccess, SlimLinkedOCEL},
        process_models::oc_declare::OCDeclareArcType,
    },
    discovery::object_centric::oc_declare::{
        negative::{discover_negative_oc_declare, NegativeOCDeclareDiscoveryOptions},
        O2OMode,
    },
    Importable, OCEL,
};

fn main() {
    let mut path = None;
    let mut taus = vec![0.0, 0.1, 0.2];
    for arg in env::args().skip(1) {
        if let Some(v) = arg.strip_prefix("--taus=") {
            taus = v.split(',').map(|s| s.parse().unwrap()).collect();
        } else {
            path = Some(arg);
        }
    }
    let path = path.expect("provide one OCEL file path");
    let ocel = OCEL::import_from_path(PathBuf::from(&path)).expect("import failed");
    let locel = SlimLinkedOCEL::from_ocel(ocel);
    println!(
        "== {path} == |E|={} |O|={} |ET|={}",
        locel.get_all_evs().count(),
        locel.get_all_obs().count(),
        locel.get_ev_types().count()
    );

    let arrows: HashSet<_> = [
        OCDeclareArcType::AS,
        OCDeclareArcType::EF,
        OCDeclareArcType::EP,
    ]
    .into_iter()
    .collect();

    for tau in taus {
        let n = discover_negative_oc_declare(
            &locel,
            NegativeOCDeclareDiscoveryOptions {
                noise_threshold: tau,
                o2o_mode: O2OMode::None,
                acts_to_use: None,
                considered_arrow_types: arrows.clone(),
            },
        );
        // Antichain: on a given activity pair no returned arc may dominate another.
        let mut comparable = 0usize;
        for a in &n {
            for b in &n {
                if std::ptr::eq(a, b) || a.from != b.from || a.to != b.to {
                    continue;
                }
                if b.arc_type.is_dominated_by_or_eq(&a.arc_type) && b.label.is_dominated_by(&a.label)
                {
                    comparable += 1;
                }
            }
        }
        println!("rho={tau:<5} |N|={:<6} comparable pairs={comparable}", n.len());
    }
}
