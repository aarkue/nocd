//! Per-arc evidence table for a reduced negative OC-DECLARE model.
//!
//! The paper reports `test(d)`, the share of a constraint's source events that are testable,
//! beside every retained arc. This emits that table: one row per arc of a reduced model, with
//! the source-event counts it is built from, so a reader can see which arcs rest on a few
//! events and which on all of them.
//!
//! `w` is the weighting of the precision definition, the testable source events at which the
//! constraint holds. `conf` is the discovery threshold's quantity, satisfying source events
//! over all of them, which counts the untestable ones as satisfied.
//!
//! Usage:
//!   cargo run --release --example retained_arc_table -- <log> <reduced-model.json> [--tsv=OUT]

use std::{collections::HashMap, env, io::Write, path::PathBuf};

use process_mining::{
    core::{
        event_data::object_centric::linked_ocel::SlimLinkedOCEL,
        process_models::oc_declare::{OCDeclareArc, OCDeclareArcType},
    },
    discovery::object_centric::oc_declare::{
        negative::{candidate_table, NegativeOCDeclareDiscoveryOptions},
        O2OMode,
    },
    Importable, OCEL,
};

fn key(from: &str, to: &str, ar: OCDeclareArcType, label: &str) -> String {
    format!("{from}|{to}|{}|{label}", ar.get_name())
}

fn main() {
    let (mut path, mut model_path, mut tsv) = (None, None, None);
    for a in env::args().skip(1) {
        if let Some(v) = a.strip_prefix("--tsv=") {
            tsv = Some(v.to_string());
        } else if path.is_none() {
            path = Some(a);
        } else {
            model_path = Some(a);
        }
    }
    let (path, model_path) = (path.expect("log"), model_path.expect("reduced model json"));

    let locel = SlimLinkedOCEL::from_ocel(
        OCEL::import_from_path(PathBuf::from(&path)).expect("import failed"),
    );
    let model: Vec<OCDeclareArc> =
        serde_json::from_reader(std::fs::File::open(&model_path).expect("open")).expect("parse");

    // The table is threshold-independent, so the noise threshold here selects nothing.
    let rows = candidate_table(
        &locel,
        &NegativeOCDeclareDiscoveryOptions {
            noise_threshold: 0.0,
            o2o_mode: O2OMode::None,
            acts_to_use: None,
            considered_arrow_types: [
                OCDeclareArcType::AS,
                OCDeclareArcType::EF,
                OCDeclareArcType::EP,
            ]
            .into_iter()
            .collect(),
        },
    );
    let by_key: HashMap<String, (usize, usize, usize)> = rows
        .iter()
        .filter(|r| r.is_negative())
        .map(|r| {
            (
                key(&r.from, &r.to, r.arc_type, &r.label.as_template_string()),
                (r.satisfying, r.testable, r.total),
            )
        })
        .collect();

    let mut out: Vec<(f64, String)> = Vec::new();
    let mut unmatched = Vec::new();
    for a in &model {
        let k = key(
            a.from.as_str(),
            a.to.as_str(),
            a.arc_type,
            &a.label.as_template_string(),
        );
        match by_key.get(&k) {
            Some(&(sat, testable, total)) if total > 0 => {
                let test = testable as f64 / total as f64;
                let conf = (sat + (total - testable)) as f64 / total as f64;
                out.push((
                    test,
                    format!(
                        "{}\t{}\t{}\t{}\t{total}\t{testable}\t{test:.4}\t{sat}\t{conf:.4}",
                        a.arc_type.get_name(),
                        a.from.as_str(),
                        a.to.as_str(),
                        a.label.as_template_string(),
                    ),
                ));
            }
            _ => unmatched.push(k),
        }
    }
    out.sort_by(|a, b| a.0.partial_cmp(&b.0).unwrap());

    let header = "arrow\tsource\ttarget\tinvolvement\tsources\ttestable\ttest\tw\tconf";
    println!("== {model_path} ==  {} arcs", model.len());
    println!("{header}");
    for (_, line) in &out {
        println!("{line}");
    }
    if !unmatched.is_empty() {
        println!("\n{} arcs absent from the candidate table:", unmatched.len());
        for k in &unmatched {
            println!("  {k}");
        }
    }
    if let Some(dest) = tsv {
        let mut f = std::fs::File::create(&dest).expect("create tsv");
        writeln!(f, "{header}").unwrap();
        for (_, line) in &out {
            writeln!(f, "{line}").unwrap();
        }
        println!("\nwrote {dest}");
    }
}
