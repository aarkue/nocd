//! Concrete instances of rule B: negative constraints derived from existence arcs and log
//! facts, with no negative premise.
//!
//! Usage: cargo run --release --example neg_rule_b_witnesses -- <log> [--limit=10]

use std::env;
use std::path::PathBuf;

use process_mining::{
    core::{
        event_data::object_centric::linked_ocel::SlimLinkedOCEL,
        process_models::oc_declare::{
            get_activity_object_facts, OCDeclareArc, OCDeclareArcLabel, OCDeclareArcType,
            OCDeclareNode, ObjectTypeAssociation,
        },
    },
    discovery::object_centric::oc_declare::{
        discover_behavior_constraints,
        negative::{candidate_table, reduce::rule_b_removable, NegativeOCDeclareDiscoveryOptions},
        O2OMode, OCDeclareDiscoveryOptions, OCDeclareReductionMode,
    },
    Importable, OCEL,
};

fn fmt_label(l: &OCDeclareArcLabel) -> String {
    let name = |t: &ObjectTypeAssociation| match t {
        ObjectTypeAssociation::Simple { object_type } => object_type.clone(),
        ObjectTypeAssociation::O2O { second, .. } => second.clone(),
    };
    let mut parts = Vec::new();
    for t in &l.all {
        parts.push(format!("All({})", name(t)));
    }
    for t in &l.each {
        parts.push(format!("Each({})", name(t)));
    }
    for t in &l.any {
        parts.push(format!("Any({})", name(t)));
    }
    if parts.is_empty() {
        "-".into()
    } else {
        parts.join(", ")
    }
}

fn main() {
    let mut path = None;
    let mut limit = 10usize;
    for arg in env::args().skip(1) {
        if let Some(v) = arg.strip_prefix("--limit=") {
            limit = v.parse().expect("bad limit");
        } else {
            path = Some(arg);
        }
    }
    let path = path.expect("provide one OCEL file path");
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
    let facts = get_activity_object_facts(&locel);
    let rows = candidate_table(&locel, &NegativeOCDeclareDiscoveryOptions::default());

    println!("\n== {path} ==");
    println!("existence model: {} arcs, candidates: {}", existence.len(), rows.len());
    println!("\nnegative constraints rule B derives with no negative premise:\n");

    let mut shown = 0usize;
    for row in &rows {
        let arc = OCDeclareArc {
            from: OCDeclareNode::new(row.from.clone()),
            to: OCDeclareNode::new(row.to.clone()),
            arc_type: row.arc_type,
            label: row.label.clone(),
            counts: (Some(0), Some(0)),
        };
        if !rule_b_removable(&arc, &existence, &facts) {
            continue;
        }
        // Find the witness type and the existence arc that supplies the path.
        let dom: Vec<String> = row
            .label
            .each
            .iter()
            .chain(row.label.any.iter())
            .chain(row.label.all.iter())
            .map(|t| match t {
                ObjectTypeAssociation::Simple { object_type } => object_type.clone(),
                ObjectTypeAssociation::O2O { second, .. } => second.clone(),
            })
            .collect();
        let witness = dom.iter().find(|ot| {
            facts
                .get(&row.to)
                .and_then(|m| m.get(*ot))
                .is_some_and(|f| f.always_present && f.at_most_one_event_per_object)
        });
        let Some(w) = witness else { continue };
        let premise = existence.iter().find(|e| {
            e.from.as_str() == row.from
                && e.to.as_str() == row.to
                && e.counts.0.unwrap_or(0) >= 1
                && e.label
                    .each
                    .iter()
                    .chain(e.label.all.iter())
                    .any(|t| match t {
                        ObjectTypeAssociation::Simple { object_type } => object_type == w,
                        ObjectTypeAssociation::O2O { second, .. } => second == w,
                    })
        });
        println!(
            "  {} -/{}-> {}   [{}]",
            row.from,
            row.arc_type.get_name(),
            row.to,
            fmt_label(&row.label)
        );
        println!(
            "      witness {w}: every {} carries one, and no {w} object appears in two {} events",
            row.from, row.to
        );
        if let Some(p) = premise {
            println!(
                "      premise  {} -{}-> {} [{}] (n_min >= 1)",
                p.from.as_str(),
                p.arc_type.get_name(),
                p.to.as_str(),
                fmt_label(&p.label)
            );
        }
        println!(
            "      so the one {} event holding that object precedes every {} event, and none can follow",
            row.to, row.from
        );
        println!();
        shown += 1;
        if shown >= limit {
            break;
        }
    }
    println!("(showing {shown})");
}
