//! Per-arc testability of negative OC-DECLARE models, in the format of `retained_arc_table`.
//!
//! Unlike `retained_arc_table`, this evaluates only the arcs of the given models, which is
//! feasible on logs with many object types.
//!
//! Usage:
//!   cargo run --release --example arc_evidence -- <log> <model.json>=<out.tsv> ...

use std::{env, io::Write, path::PathBuf};

use process_mining::{
    core::{
        event_data::object_centric::linked_ocel::SlimLinkedOCEL,
        process_models::oc_declare::OCDeclareArc,
    },
    discovery::object_centric::oc_declare::negative::arc_evidence,
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
        let rows = arc_evidence(&locel, &model);
        let mut f = std::fs::File::create(out).expect("create tsv");
        writeln!(f, "arrow\tsource\ttarget\tinvolvement\tsources\ttestable\ttest\tw\tconf").unwrap();
        for (a, &(sat, testable, total)) in model.iter().zip(&rows) {
            let test = testable as f64 / total.max(1) as f64;
            let conf = (sat + (total - testable)) as f64 / total.max(1) as f64;
            writeln!(
                f,
                "{}\t{}\t{}\t{}\t{total}\t{testable}\t{test:.4}\t{sat}\t{conf:.4}",
                a.arc_type.get_name(),
                a.from.as_str(),
                a.to.as_str(),
                a.label.as_template_string(),
            )
            .unwrap();
        }
        println!("wrote {out} ({} arcs)", model.len());
    }
}
