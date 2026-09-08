//! Conformance-checking time of a discovered versus a reduced negative OC-DECLARE model.
//!
//! Checks every arc of each model sequentially against the log and reports the median wall
//! time over `--runs` repetitions, after one warm-up pass.
//!
//! Usage:
//!   cargo run --release --example neg_conformance_time -- <log> <discovered.json> \
//!       <reduced.json> [--runs=3]

use std::{env, path::PathBuf, time::Instant};

use process_mining::{
    conformance::object_centric::oc_declare::oc_declare_conformance,
    core::{
        event_data::object_centric::linked_ocel::SlimLinkedOCEL,
        process_models::oc_declare::OCDeclareArc,
    },
    Importable, OCEL,
};

fn load(path: &str) -> Vec<OCDeclareArc> {
    serde_json::from_reader(std::fs::File::open(path).expect("open model")).expect("parse model")
}

/// Returns the median seconds and the lowest per-arc conformance.
fn time_model(locel: &SlimLinkedOCEL, model: &[OCDeclareArc], runs: usize) -> (f64, f64) {
    let check = || {
        model
            .iter()
            .map(|a| oc_declare_conformance(locel, a))
            .fold(1.0_f64, f64::min)
    };
    let min_conf = check();
    let mut times: Vec<f64> = (0..runs)
        .map(|_| {
            let t = Instant::now();
            std::hint::black_box(check());
            t.elapsed().as_secs_f64()
        })
        .collect();
    times.sort_by(|a, b| a.partial_cmp(b).unwrap());
    (times[times.len() / 2], min_conf)
}

fn main() {
    let mut runs = 3;
    let mut pos = Vec::new();
    for a in env::args().skip(1) {
        if let Some(v) = a.strip_prefix("--runs=") {
            runs = v.parse().expect("bad --runs");
        } else {
            pos.push(a);
        }
    }
    let [log, discovered, reduced] = <[String; 3]>::try_from(pos).expect("log, discovered, reduced");

    let locel = SlimLinkedOCEL::from_ocel(
        OCEL::import_from_path(PathBuf::from(&log)).expect("import failed"),
    );
    let (d, r) = (load(&discovered), load(&reduced));
    let (td, cd) = time_model(&locel, &d, runs);
    let (tr, cr) = time_model(&locel, &r, runs);
    println!("model\tarcs\tmedian_s\tmin_conf");
    println!("discovered\t{}\t{td:.4}\t{cd:.4}", d.len());
    println!("reduced\t{}\t{tr:.4}\t{cr:.4}", r.len());
}
