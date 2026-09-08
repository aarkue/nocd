//! Is the set of candidates clearing the threshold upward closed under the involvement order?
//!
//! Everything downstream assumes it is: the frontier search reports minimal satisfied
//! constraints and prunes above them, and the precision reference assumes its generators
//! generate it. Plain support makes it true by construction, since the denominator is fixed.
//! Conditional support moves the denominator as well, so this checks it directly.
//!
//! Usage: cargo run --release --example neg_upclosure_check -- <log> [--acts=A,B,C]

use std::{collections::HashSet, env, path::PathBuf};

use process_mining::{
    core::{
        event_data::object_centric::linked_ocel::SlimLinkedOCEL,
        process_models::oc_declare::OCDeclareArcType,
    },
    discovery::object_centric::oc_declare::{
        negative::{candidate_table, CandidateRow, NegativeOCDeclareDiscoveryOptions},
        O2OMode,
    },
    Importable, OCEL,
};

/// `a` is dominated by `b` in the involvement order (`a` weaker or equal).
fn dominated(a: &CandidateRow, b: &CandidateRow) -> bool {
    a.label.is_dominated_by(&b.label)
}

fn main() {
    let mut path = None;
    let mut acts: Option<Vec<String>> = None;
    for arg in env::args().skip(1) {
        if let Some(v) = arg.strip_prefix("--acts=") {
            acts = Some(v.split(',').map(|s| s.to_string()).collect());
        } else {
            path = Some(arg);
        }
    }
    let path = path.expect("provide one OCEL file path");
    let ocel = OCEL::import_from_path(PathBuf::from(&path)).expect("import failed");
    let locel = SlimLinkedOCEL::from_ocel(ocel);
    let opts = NegativeOCDeclareDiscoveryOptions {
        noise_threshold: 0.0,
        o2o_mode: O2OMode::None,
        acts_to_use: acts,
        considered_arrow_types: [
            OCDeclareArcType::AS,
            OCDeclareArcType::EF,
            OCDeclareArcType::EP,
        ]
        .into_iter()
        .collect(),
    };
    let rows = candidate_table(&locel, &opts);
    println!("\n== {path} ==");
    println!("candidates: {}\n", rows.len());

    // group by unit
    let mut units: std::collections::HashMap<(String, String, OCDeclareArcType), Vec<&CandidateRow>> =
        Default::default();
    for r in &rows {
        units
            .entry((r.from.clone(), r.to.clone(), r.arc_type))
            .or_default()
            .push(r);
    }

    println!(
        "{:>6} {:>10} {:>12} {:>12} {:>14}",
        "rho", "clearing", "violations", "affected", "worst drop"
    );
    for rho in [0.0, 0.05, 0.1, 0.15, 0.2, 0.25, 0.3] {
        let mut clearing = 0usize;
        let mut breaks = 0usize;
        let mut affected: HashSet<(String, String, OCDeclareArcType)> = HashSet::new();
        let mut worst = 0.0f64;
        let mut example: Option<String> = None;
        for (key, rs) in &units {
            let cleared: Vec<&&CandidateRow> = rs
                .iter()
                .filter(|r| r.testable > 0 && r.discovered_at(rho))
                .collect();
            clearing += cleared.len();
            // up-closure: everything above something that clears must also clear
            for lo in &cleared {
                for hi in rs {
                    if std::ptr::eq(**lo, *hi) {
                        continue;
                    }
                    if dominated(lo, hi) && !(hi.testable > 0 && hi.discovered_at(rho)) {
                        breaks += 1;
                        affected.insert(key.clone());
                        let drop = lo.conditional_support()
                            - if hi.testable > 0 {
                                hi.conditional_support()
                            } else {
                                0.0
                            };
                        if drop > worst {
                            worst = drop;
                            example = Some(format!(
                                "{} -/{}-> {}: {} (cs {:.3}, {}/{}) is below {} (cs {:.3}, {}/{})",
                                lo.from,
                                lo.arc_type.get_name(),
                                lo.to,
                                lo.label.as_template_string(),
                                lo.conditional_support(),
                                lo.satisfying,
                                lo.testable,
                                hi.label.as_template_string(),
                                if hi.testable > 0 { hi.conditional_support() } else { f64::NAN },
                                hi.satisfying,
                                hi.testable
                            ));
                        }
                    }
                }
            }
        }
        println!(
            "{rho:>6.2} {clearing:>10} {breaks:>12} {:>12} {worst:>14.3}",
            affected.len()
        );
        if let Some(e) = example {
            println!("        e.g. {e}");
        }
    }
}
