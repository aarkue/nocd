//! Report, per activity and object type, how many distinct objects the events carry.
//!
//! This is the precondition for the object-involvement dimension of OC-DECLARE to have any
//! content. Where no event of an activity carries two or more distinct objects of a type,
//! `All`, `Each` and `Any` impose the identical filter there, so whichever level a discovery
//! procedure reports at that pair is arbitrary and says nothing about the log. Any census of
//! reported involvement levels has to be restricted to the pairs this reports as
//! distinguishable.
//!
//! It also reports partial carrying (some events of the activity carry the type and some do
//! not), which is the deficiency that makes an involvement vacuous at the events that carry
//! nothing.
//!
//! Usage:
//!   cargo run --release --example object_multiplicity -- <log1> [log2 ...] [--full]
//!
//! Without `--full` only the pairs where the levels are distinguishable are listed, plus the
//! per-log summary.

use std::{env, path::PathBuf, time::Instant};

use process_mining::{
    core::{
        event_data::object_centric::linked_ocel::SlimLinkedOCEL,
        process_models::oc_declare::{
            all_object_type_associations, get_activity_association_multiplicity,
            get_activity_object_multiplicity,
        },
    },
    Importable, OCEL,
};

fn main() {
    let mut paths = Vec::new();
    let mut full = false;
    let mut o2o = false;
    for arg in env::args().skip(1) {
        if arg == "--full" {
            full = true;
        } else if arg == "--o2o" {
            o2o = true;
        } else {
            paths.push(arg);
        }
    }
    if paths.is_empty() {
        panic!("Provide one or more OCEL file paths (see the module doc comment).");
    }

    for path in paths {
        let started = Instant::now();
        let ocel = OCEL::import_from_path(PathBuf::from(&path)).expect("failed to import OCEL");
        let locel = SlimLinkedOCEL::from_ocel(ocel);
        let mult = if o2o {
            // The involvement dimension ranges over transitive types too, so a
            // direct-type-only measurement understates it on any log where the
            // one-to-many structure sits in O2O rather than in E2O.
            get_activity_association_multiplicity(&locel, &all_object_type_associations(&locel))
        } else {
            get_activity_object_multiplicity(&locel)
        };
        let elapsed = started.elapsed();

        let mut rows: Vec<_> = mult
            .iter()
            .flat_map(|(act, per)| per.iter().map(move |(ot, m)| (act.clone(), ot.clone(), m)))
            .collect();
        rows.sort_by(|a, b| a.0.cmp(&b.0).then(a.1.cmp(&b.1)));

        let carried = rows.len();
        let distinguishable = rows.iter().filter(|(_, _, m)| m.levels_distinguishable()).count();
        let partial = rows.iter().filter(|(_, _, m)| m.partially_carried()).count();

        println!("\n== {path} ==");
        println!(
            "{:<34} {:<26} {:>8} {:>8} {:>9} {:>5}",
            "activity", "association", "events", "carry%", "2+ objs%", "max"
        );
        for (act, ot, m) in &rows {
            if !full && !m.levels_distinguishable() {
                continue;
            }
            println!(
                "{:<34} {:<26} {:>8} {:>7.1}% {:>8.1}% {:>5}",
                truncate(act, 34),
                truncate(ot, 26),
                m.events,
                100.0 * m.carrying as f64 / m.events.max(1) as f64,
                100.0 * m.converging as f64 / m.events.max(1) as f64,
                m.max
            );
        }
        println!(
            "\n  (activity, object type) pairs carried at all: {carried}\n  \
             levels distinguishable (some event carries 2+): {distinguishable}\n  \
             levels provably identical (max 1 everywhere):   {}\n  \
             partially carried (deficiency):                 {partial}\n  \
             loaded and measured in {:.1?}",
            carried - distinguishable,
            elapsed
        );
    }
}

fn truncate(s: &str, n: usize) -> String {
    if s.chars().count() <= n {
        s.to_string()
    } else {
        s.chars().take(n - 1).chain(std::iter::once('~')).collect()
    }
}
