//! Evidence of retained negative arcs: per immediate predecessor, the source events at which
//! the arc holds and object counts permit a violation of it, but the predecessor is violated.
//! The arc's evidence is the minimum over its predecessors.
//!
//! Writes one TSV row per arc, sorted by evidence.
//!
//! Usage:
//!   cargo run --release --example neg_predecessor_margin -- <log> <model.json>=<out.tsv> ...

use std::{env, io::Write, path::PathBuf};

use process_mining::{
    core::{
        event_data::object_centric::linked_ocel::{LinkedOCELAccess, SlimLinkedOCEL},
        process_models::oc_declare::OCDeclareArc,
    },
    discovery::object_centric::oc_declare::negative::predecessor_evidence,
    Importable, OCEL,
};

fn main() {
    let mut args = env::args().skip(1);
    let log = args.next().expect("log");
    let locel = SlimLinkedOCEL::from_ocel(
        OCEL::import_from_path(PathBuf::from(&log)).expect("import failed"),
    );
    for pair in args {
        let (model_path, out) = pair.split_once('=').expect("<model.json>=<out.tsv>");
        let model: Vec<OCDeclareArc> =
            serde_json::from_reader(std::fs::File::open(model_path).expect("open")).expect("parse");
        let ev = predecessor_evidence(&locel, &model);
        let mut rows: Vec<(usize, String)> = model
            .iter()
            .zip(&ev)
            .map(|(a, preds)| {
                let min = preds.iter().map(|(_, c)| *c).min().unwrap_or(0);
                let detail: Vec<String> = preds.iter().map(|(n, c)| format!("{n}: {c}")).collect();
                let n = locel.get_evs_of_type(a.from.as_str()).count();
                (
                    min,
                    format!(
                        "{}\t{}\t{}\t{}\t{n}\t{min}\t{}",
                        a.arc_type.get_name(),
                        a.from.as_str(),
                        a.to.as_str(),
                        a.label.as_template_string(),
                        detail.join("; ")
                    ),
                )
            })
            .collect();
        rows.sort_by(|a, b| b.0.cmp(&a.0));
        let mut f = std::fs::File::create(out).expect("create tsv");
        writeln!(f, "arrow\tsource\ttarget\tinvolvement\tsources\tevidence\tper_predecessor").unwrap();
        for (_, r) in &rows {
            writeln!(f, "{r}").unwrap();
        }
        println!("wrote {out} ({} arcs)", model.len());
    }
}
