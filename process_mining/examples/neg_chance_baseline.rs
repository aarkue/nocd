//! Observed versus chance-level violations of two-type `AS` negative arcs.
//!
//! For an arc forbidding a target event that shares an `anchor` object and a `role` object
//! with the source event, the chance level assumes that each target event's role objects are
//! drawn independently with their frequency among all target events. A violation count far
//! below chance indicates a real separation (e.g. of duties); one near or above chance does not.
//!
//! Usage:
//!   cargo run --release --example neg_chance_baseline -- <log> <model.json>...

use std::{
    collections::{HashMap, HashSet},
    env,
    path::PathBuf,
};

use process_mining::{
    core::{
        event_data::object_centric::linked_ocel::{
            slim_linked_ocel::{EventIndex, ObjectIndex},
            LinkedOCELAccess, SlimLinkedOCEL,
        },
        process_models::oc_declare::{OCDeclareArc, OCDeclareArcType, ObjectTypeAssociation},
    },
    Importable, OCEL,
};

fn objs(locel: &SlimLinkedOCEL, e: &EventIndex, ot: &str) -> HashSet<ObjectIndex> {
    e.get_e2o(locel)
        .filter(|o| o.get_ob_type(locel) == ot)
        .copied()
        .collect()
}

fn type_name(t: &ObjectTypeAssociation) -> String {
    match t {
        ObjectTypeAssociation::Simple { object_type } => object_type.clone(),
        other => format!("{other:?}"),
    }
}

/// `(observed, expected)` source events with a target sharing an anchor and a role object.
fn baseline(locel: &SlimLinkedOCEL, s: &str, t: &str, anchor: &str, role: &str) -> (usize, f64) {
    let targets: Vec<EventIndex> = locel.get_evs_of_type(t).copied().collect();
    let mut by_anchor: HashMap<ObjectIndex, Vec<usize>> = HashMap::new();
    let mut role_freq: HashMap<ObjectIndex, f64> = HashMap::new();
    let target_roles: Vec<HashSet<ObjectIndex>> = targets
        .iter()
        .enumerate()
        .map(|(i, e)| {
            for a in objs(locel, e, anchor) {
                by_anchor.entry(a).or_default().push(i);
            }
            let r = objs(locel, e, role);
            for o in &r {
                *role_freq.entry(*o).or_default() += 1.0 / targets.len() as f64;
            }
            r
        })
        .collect();
    let (mut observed, mut expected) = (0, 0.0);
    for e in locel.get_evs_of_type(s) {
        let roles = objs(locel, e, role);
        let scope: HashSet<usize> = objs(locel, e, anchor)
            .iter()
            .flat_map(|a| by_anchor.get(a).into_iter().flatten().copied())
            .collect();
        if scope.iter().any(|&i| !target_roles[i].is_disjoint(&roles)) {
            observed += 1;
        }
        let q: f64 = roles.iter().map(|r| role_freq.get(r).copied().unwrap_or(0.0)).sum::<f64>().min(1.0);
        expected += 1.0 - (1.0 - q).powi(scope.len() as i32);
    }
    (observed, expected)
}

fn main() {
    let mut args = env::args().skip(1);
    let log = args.next().expect("log");
    let locel = SlimLinkedOCEL::from_ocel(
        OCEL::import_from_path(PathBuf::from(&log)).expect("import failed"),
    );
    for model_path in args {
        let model: Vec<OCDeclareArc> =
            serde_json::from_reader(std::fs::File::open(&model_path).expect("open")).expect("parse");
        println!("== {model_path}");
        for a in &model {
            if a.arc_type != OCDeclareArcType::AS
                || a.label.any.len() != 2
                || !a.label.all.is_empty()
                || !a.label.each.is_empty()
            {
                continue;
            }
            let (x, y) = (type_name(&a.label.any[0]), type_name(&a.label.any[1]));
            let (s, t) = (a.from.as_str(), a.to.as_str());
            let n = locel.get_evs_of_type(s).count();
            for (anchor, role) in [(&x, &y), (&y, &x)] {
                let (obs, exp) = baseline(&locel, s, t, anchor, role);
                println!("{s} -> {t} | n={n} anchor={anchor} role={role} | observed {obs} expected {exp:.1}");
            }
        }
    }
}
