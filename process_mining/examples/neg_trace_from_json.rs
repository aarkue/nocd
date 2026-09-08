//! Per-stage removal counts for given existence and negative models, plus the activity pairs
//! on which cardinality entailment could apply to a returned `All` constraint, i.e.,
//! `mult_min(s, ot) > mult_max(t, ot) >= 2`.
//!
//! Usage:
//!   cargo run --release --example neg_trace_from_json -- <log> <existence.json> <negative.json>...

use std::{collections::HashMap, env, path::PathBuf};

use process_mining::{
    core::{
        event_data::object_centric::linked_ocel::{LinkedOCELAccess, SlimLinkedOCEL},
        process_models::oc_declare::OCDeclareArc,
    },
    discovery::object_centric::oc_declare::negative::reduce_negative_oc_declare_traced,
    Importable, OCEL,
};

fn load(p: &str) -> Vec<OCDeclareArc> {
    serde_json::from_reader(std::fs::File::open(p).expect("open")).expect("parse")
}

fn main() {
    let args: Vec<String> = env::args().skip(1).collect();
    let locel = SlimLinkedOCEL::from_ocel(
        OCEL::import_from_path(PathBuf::from(&args[0])).expect("import failed"),
    );

    let mut mult: HashMap<(String, String), (usize, usize)> = HashMap::new();
    let ots: Vec<String> = locel.get_ob_types().map(|s| s.to_string()).collect();
    for et in locel.get_ev_types() {
        for ot in &ots {
            mult.insert((et.to_string(), ot.clone()), (usize::MAX, 0));
        }
        for ev in locel.get_evs_of_type(et) {
            let mut c: HashMap<&str, std::collections::HashSet<_>> = HashMap::new();
            for o in ev.get_e2o(&locel) {
                c.entry(o.get_ob_type(&locel)).or_default().insert(o);
            }
            for ot in &ots {
                let n = c.get(ot.as_str()).map(|s| s.len()).unwrap_or(0);
                let m = mult.get_mut(&(et.to_string(), ot.clone())).unwrap();
                m.0 = m.0.min(n);
                m.1 = m.1.max(n);
            }
        }
    }
    let ets: Vec<String> = locel.get_ev_types().map(|s| s.to_string()).collect();
    let mut stage1 = 0;
    for s in &ets {
        for t in &ets {
            if s == t {
                continue;
            }
            for ot in &ots {
                let (smin, _) = mult[&(s.clone(), ot.clone())];
                let (_, tmax) = mult[&(t.clone(), ot.clone())];
                if tmax >= 2 && smin > tmax {
                    stage1 += 1;
                    println!("STAGE1-CANDIDATE {s} -> {t} [{ot}] min_s={smin} max_t={tmax}");
                }
            }
        }
    }
    println!("stage-1 applicable (s,t,ot) with max_t >= 2: {stage1}");

    let existing = load(&args[1]);
    for neg in &args[2..] {
        let (_, t) = reduce_negative_oc_declare_traced(&locel, &existing, load(neg));
        println!(
            "{neg}: input {} card {} dom {} cond {} uniq {} orient {} output {}",
            t.input,
            t.cardinality_entailed,
            t.dominated,
            t.condensation,
            t.rule_b,
            t.orientation_dedup,
            t.output
        );
    }
}
