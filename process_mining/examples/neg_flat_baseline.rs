//! What does a flat negative miner on per-type flattenings recover of the reduced model?
//!
//! The related work notes that MINERful's `NotCoExistence`, `NotSuccession` and
//! `NotPrecedence` coincide with the single-type `Any` fragment of OC-DECLARE. This makes that
//! precise and measures it: flatten the log once per object type (one case per object, its
//! events in time order), mine the three templates, and ask how much of the reduced negative
//! model the result contains.
//!
//! The correspondence, for an object type `ot` and its flattening:
//!   (AS, s, t, {ot -> Any}, 0, 0)  <->  NotCoExistence(s,t): no case holds both
//!   (EF, s, t, {ot -> Any}, 0, 0)  <->  NotSuccession(s,t):  no case has t after s
//!   (EP, s, t, {ot -> Any}, 0, 0)  <->  NotPrecedence(s,t):  no case has t before s
//! `Each` coincides with `Any` at bound zero, so it maps the same way. `All` and any
//! involvement of two or more types have no image: a case carries one object, so neither "all
//! of the source's objects" nor "shares an object of each of two types" can be stated.
//!
//! Usage:
//!   cargo run --release --example neg_flat_baseline -- <log> <reduced-model.json>
//!       [--rho=0.0] [--structural-only]
//!
//! Which arcs have no image is a property of the model alone. `--structural-only` reports that
//! share without mining the flattenings, which does not finish in reasonable time on the two
//! large logs; it reads no log and the path is then only a label.

use std::{
    collections::{HashMap, HashSet},
    env,
    path::PathBuf,
};

use process_mining::{
    core::{
        event_data::object_centric::linked_ocel::{LinkedOCELAccess, SlimLinkedOCEL},
        process_models::oc_declare::OCDeclareArc,
    },
    Importable, OCEL,
};

/// A flat negative template on one flattening.
#[derive(PartialEq, Eq, Hash, Clone, Debug)]
enum Flat {
    NotCoExistence(String, String),
    NotSuccession(String, String),
    NotPrecedence(String, String),
}

fn main() {
    let mut pos = Vec::new();
    let mut rho = 0.0f64;
    let mut structural_only = false;
    for a in env::args().skip(1) {
        if let Some(v) = a.strip_prefix("--rho=") {
            rho = v.parse().expect("--rho");
        } else if a == "--structural-only" {
            structural_only = true;
        } else {
            pos.push(a);
        }
    }
    let (log, model_path) = (pos[0].clone(), pos[1].clone());
    let locel = if structural_only {
        None
    } else {
        let ocel = OCEL::import_from_path(PathBuf::from(&log)).expect("import failed");
        Some(SlimLinkedOCEL::from_ocel(ocel))
    };

    let model: Vec<OCDeclareArc> =
        serde_json::from_reader(std::fs::File::open(&model_path).expect("open model"))
            .expect("parse model");

    // ---- flatten once per object type, then mine the three templates ------------------
    let ob_types: Vec<String> = locel
        .as_ref()
        .map(|l| l.get_ob_types().map(|t| t.to_string()).collect())
        .unwrap_or_default();
    let mut mined: HashMap<String, HashSet<Flat>> = HashMap::new();
    for ot in &ob_types {
        let locel = locel.as_ref().unwrap();
        let ot = ot.as_str();
        // one case per object: the activities of its events, in time order
        let mut cases: Vec<Vec<(i64, &str)>> = Vec::new();
        for ob in locel.get_obs_of_type(ot) {
            let mut evs: Vec<(i64, &str)> = locel
                .get_e2o_rev(ob)
                .map(|(_, e)| {
                    (
                        locel.get_ev_time(e).timestamp_micros(),
                        locel.get_ev_type_of(e),
                    )
                })
                .collect();
            if evs.len() < 2 {
                continue; // no pair to constrain
            }
            evs.sort();
            cases.push(evs);
        }

        // A template is discovered when no case violates it: the rho = 0 reading, which is
        // exactly the OC-DECLARE one, every source event satisfying the constraint.
        let mut co: HashMap<(String, String), usize> = HashMap::new();
        let mut succ: HashMap<(String, String), usize> = HashMap::new();
        let mut prec: HashMap<(String, String), usize> = HashMap::new();
        let n_cases = cases.len().max(1);
        let acts: HashSet<&str> = cases.iter().flatten().map(|(_, a)| *a).collect();
        for case in &cases {
            let present: HashSet<&str> = case.iter().map(|(_, a)| *a).collect();
            for a in &present {
                for b in &present {
                    if a != b {
                        *co.entry((a.to_string(), b.to_string())).or_default() += 1;
                    }
                }
            }
            let mut viol_succ: HashSet<(String, String)> = HashSet::new();
            let mut viol_prec: HashSet<(String, String)> = HashSet::new();
            for (ta, a) in case.iter() {
                for (tb, b) in case.iter() {
                    if a != b && tb > ta {
                        viol_succ.insert((a.to_string(), b.to_string()));
                        viol_prec.insert((b.to_string(), a.to_string()));
                    }
                }
            }
            for k in viol_succ {
                *succ.entry(k).or_default() += 1;
            }
            for k in viol_prec {
                *prec.entry(k).or_default() += 1;
            }
        }
        let ok = |m: &HashMap<(String, String), usize>, p: &(String, String)| {
            m.get(p).copied().unwrap_or(0) as f64 / n_cases as f64 <= rho
        };
        let mut set = HashSet::new();
        for a in &acts {
            for b in &acts {
                if a == b {
                    continue;
                }
                let p = (a.to_string(), b.to_string());
                if ok(&co, &p) {
                    set.insert(Flat::NotCoExistence(p.0.clone(), p.1.clone()));
                }
                if ok(&succ, &p) {
                    set.insert(Flat::NotSuccession(p.0.clone(), p.1.clone()));
                }
                if ok(&prec, &p) {
                    set.insert(Flat::NotPrecedence(p.0.clone(), p.1.clone()));
                }
            }
        }
        mined.insert(ot.to_string(), set);
    }

    // ---- classify each retained arc --------------------------------------------------
    let (mut no_image, mut recovered, mut missed) = (0usize, 0usize, 0usize);
    let mut missed_examples = Vec::new();
    for arc in &model {
        let l = &arc.label;
        let types: Vec<&str> = l
            .each
            .iter()
            .chain(l.any.iter())
            .chain(l.all.iter())
            .map(|t| match t {
                process_mining::core::process_models::oc_declare::ObjectTypeAssociation::Simple {
                    object_type,
                } => object_type.as_str(),
                process_mining::core::process_models::oc_declare::ObjectTypeAssociation::O2O {
                    second,
                    ..
                } => second.as_str(),
            })
            .collect();
        if types.len() != 1 || !l.all.is_empty() {
            no_image += 1; // multi-type, or All: not statable on any single flattening
            continue;
        }
        let ot = types[0];
        let (s, t) = (arc.from.as_str().to_string(), arc.to.as_str().to_string());
        let want = match &*arc.arc_type.get_name() {
            "AS" => Flat::NotCoExistence(s.clone(), t.clone()),
            "EF" => Flat::NotSuccession(s.clone(), t.clone()),
            "EP" => Flat::NotPrecedence(s.clone(), t.clone()),
            _ => {
                no_image += 1;
                continue;
            }
        };
        if mined.get(ot).is_some_and(|m| m.contains(&want)) {
            recovered += 1;
        } else {
            missed += 1;
            if missed_examples.len() < 3 {
                missed_examples.push(format!("{s} -/{}-> {t} on {ot}", arc.arc_type.get_name()));
            }
        }
    }

    println!("\n== {log} / {model_path} ==");
    println!("retained arcs                 : {}", model.len());
    println!("no image in any flattening    : {no_image}");
    if structural_only {
        return;
    }
    println!("in the fragment, and mined    : {recovered}");
    println!("in the fragment, but not mined: {missed}");
    for m in &missed_examples {
        println!("   e.g. {m}");
    }
    println!(
        "flat templates mined overall  : {}",
        mined.values().map(|s| s.len()).sum::<usize>()
    );
}
