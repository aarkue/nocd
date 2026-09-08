//! Evaluate the whole negative candidate space and report the distribution.
//!
//! This is the reference side of any quality measure for negative OC-DECLARE models: for every
//! candidate in the gated lattice it records how many source events satisfy it, how many could
//! ever have violated it, and how many there are. Precision against a model is then an
//! aggregation over this table intersected with what the model entails, and every weighting
//! choice -- binary or support-graded, rate or absolute evidence count, macro or micro -- is a
//! different aggregation over the same rows.
//!
//! Usage:
//!   cargo run --release --example negative_candidate_table -- <log> [--acts=A,B,C] [--json=OUT]
//!
//! `--acts` restricts the activity set, which matters: cost is quadratic in activities and
//! exponential in the gated type count per pair.

use std::{collections::HashSet, env, fs::File, path::PathBuf, time::Instant};

use process_mining::{
    core::{
        event_data::object_centric::linked_ocel::SlimLinkedOCEL,
        process_models::oc_declare::{OCDeclareArc, OCDeclareArcType, OCDeclareNode},
    },
    discovery::object_centric::oc_declare::{
        negative::{
            candidate_table, closure, covered_rows, discover_negative_oc_declare,
            minimal_satisfied_rows, precision_from_coverage, reduce_negative_oc_declare,
            NegativeOCDeclareDiscoveryOptions, Weighting,
        },
        discover_behavior_constraints, O2OMode, OCDeclareDiscoveryOptions,
        OCDeclareReductionMode,
    },
    Importable, OCEL,
};

fn main() {
    let mut path = None;
    let mut acts: Option<Vec<String>> = None;
    let mut json_out: Option<PathBuf> = None;
    for arg in env::args().skip(1) {
        if let Some(v) = arg.strip_prefix("--acts=") {
            acts = Some(v.split(',').map(|s| s.to_string()).collect());
        } else if let Some(v) = arg.strip_prefix("--json=") {
            json_out = Some(PathBuf::from(v));
        } else {
            path = Some(arg);
        }
    }
    let path = path.expect("provide one OCEL file path");

    let ocel = OCEL::import_from_path(PathBuf::from(&path)).expect("failed to import OCEL");
    let locel = SlimLinkedOCEL::from_ocel(ocel);

    let options = NegativeOCDeclareDiscoveryOptions {
        noise_threshold: 0.0, // ignored by candidate_table; the table is threshold-independent
        o2o_mode: O2OMode::None,
        acts_to_use: acts,
        considered_arrow_types: [
            OCDeclareArcType::AS,
            OCDeclareArcType::EF,
            OCDeclareArcType::EP,
        ]
        .into_iter()
        .collect::<HashSet<_>>(),
    };

    let started = Instant::now();
    let rows = candidate_table(&locel, &options);
    let elapsed = started.elapsed();

    let units: HashSet<_> = rows
        .iter()
        .map(|r| (r.from.clone(), r.to.clone(), r.arc_type))
        .collect();

    println!("\n== {path} ==");
    println!("candidates evaluated: {}", rows.len());
    println!("(activity pair, arrow) units: {}", units.len());
    println!("computed in {elapsed:.1?}\n");

    println!("{:>6} {:>12} {:>12} {:>14}", "tau", "discovered", "share", "of which testable");
    for tau in [0.0, 0.05, 0.1, 0.2, 0.3] {
        let d = rows.iter().filter(|r| r.discovered_at(tau)).count();
        let t = rows.iter().filter(|r| r.discovered_at(tau) && r.testable > 0).count();
        println!(
            "{tau:>6.2} {d:>12} {:>11.1}% {t:>14}",
            100.0 * d as f64 / rows.len() as f64
        );
    }

    // Support distribution over candidates that are testable at all: the shape that decides
    // whether a support-weighted measure differs meaningfully from a binary one.
    let testable: Vec<f64> = rows
        .iter()
        .filter(|r| r.testable > 0)
        .map(|r| r.conditional_support())
        .collect();
    println!("\ntestable candidates: {}", testable.len());
    println!("{:>12} {:>10}", "cond. supp", "count");
    for (lo, hi) in [(0.0, 0.001), (0.001, 0.5), (0.5, 0.9), (0.9, 0.999), (0.999, 1.001)] {
        let n = testable.iter().filter(|&&s| s >= lo && s < hi).count();
        println!("{:>5.2}-{:<6.2} {n:>10}", lo, hi.min(1.0));
    }

    let never = rows.iter().filter(|r| r.testable == 0).count();
    println!(
        "\nuntestable candidates (could never have been violated): {never} \
         ({:.1}% of all)",
        100.0 * never as f64 / rows.len() as f64
    );

    // Precision against a FIXED reference: the constraints the log supports at
    // reference_tau. Sweeping the model's threshold against it shows what tightening the
    // threshold costs in coverage. Passing the model's own tau as the reference would make
    // the reference be the model, and every score 1.
    // Must match the existence model the reduction experiments use: unbounded upper count and
    // no reduction, so that no composition premise is filtered away. `Default::default()` caps
    // n_max at 20 and yields a different model, hence different reduced sizes.
    let existence = discover_behavior_constraints(
        &locel,
        OCDeclareDiscoveryOptions {
            o2o_mode: O2OMode::None,
            counts_for_filter: (Some(1), None),
            reduction: OCDeclareReductionMode::None,
            all_for_single_valued_types: true,
            ..Default::default()
        },
    );
    println!("existence model: {} arcs", existence.len());
    // Entailment must be the inverse of the reduction, iterated: every stage run forward to a
    // fixpoint. The one-step removability test cannot see a derivation that ran through an arc
    // the reduction deleted, and domination alone sees only one of the eight stages -- both
    // score a reduced model far below what it entails.
    const MODEL_TAUS: [f64; 7] = [0.0, 0.05, 0.1, 0.15, 0.2, 0.25, 0.3];
    const REFERENCE_TAUS: [f64; 10] = [0.0, 0.1, 0.2, 0.3, 0.4, 0.5, 0.6, 0.7, 0.8, 0.9];

    // The closure is bounded by its universe, so the universe has to hold everything any model
    // in the sweep might entail: every reference antichain and every discovered model.
    let mut universe: Vec<OCDeclareArc> = Vec::new();
    for reference_tau in REFERENCE_TAUS {
        universe.extend(minimal_satisfied_rows(&rows, reference_tau).into_iter().map(|r| {
            OCDeclareArc {
                from: OCDeclareNode::new(r.from.clone()),
                to: OCDeclareNode::new(r.to.clone()),
                arc_type: r.arc_type,
                label: r.label.clone(),
                counts: (Some(0), Some(0)),
            }
        }));
    }
    let mut models: Vec<(f64, Vec<OCDeclareArc>, Vec<OCDeclareArc>)> = Vec::new();
    for tau in MODEL_TAUS {
        let model = discover_negative_oc_declare(
            &locel,
            NegativeOCDeclareDiscoveryOptions {
                noise_threshold: tau,
                ..options.clone()
            },
        );
        let reduced = reduce_negative_oc_declare(&locel, &existence, model.clone());
        universe.extend(model.iter().cloned());
        models.push((tau, model, reduced));
    }

    // Does the reduced model expand back to the model it came from? This is the losslessness
    // claim, stated as sets rather than as a score.
    println!("\nreduction and its inverse");
    println!(
        "{:>6} {:>8} {:>10} {:>12} {:>14} {:>10}",
        "tau", "|N|", "|N reduc|", "|closure N|", "|closure N re|", "identical"
    );
    let mut closures: Vec<(f64, Vec<OCDeclareArc>, Vec<OCDeclareArc>)> = Vec::new();
    for (tau, model, reduced) in &models {
        let cm = closure(model, &universe, &existence, &locel);
        let cr = closure(reduced, &universe, &existence, &locel);
        let sm: HashSet<&OCDeclareArc> = cm.iter().collect();
        let sr: HashSet<&OCDeclareArc> = cr.iter().collect();
        println!(
            "{tau:>6.2} {:>8} {:>10} {:>12} {:>14} {:>10}",
            model.len(),
            reduced.len(),
            cm.len(),
            cr.len(),
            if sm == sr {
                "yes".to_string()
            } else {
                format!("no ({} lost)", sm.difference(&sr).count())
            }
        );
        closures.push((*tau, cm, cr));
    }

    // Where does the empty-model floor come from? Rule B needs a path among the *existence*
    // arcs, so it is free of negative premises only; cardinality entailment needs no arcs at
    // all. Splitting the two shows whether the floor measures the existence model or the log.
    {
        let floor_full = closure(&[], &universe, &existence, &locel);
        let floor_no_existence = closure(&[], &universe, &[], &locel);
        println!(
            "\nempty-model floor: |closure| = {} with the existence model, {} without it",
            floor_full.len(),
            floor_no_existence.len()
        );
        for (label, cl) in [("with existence", &floor_full), ("no existence", &floor_no_existence)] {
            let cov = covered_rows(&rows, cl);
            let v: Vec<f64> = REFERENCE_TAUS
                .iter()
                .map(|&r| precision_from_coverage(&rows, &cov, r, Weighting::Evidence).value)
                .collect();
            println!(
                "  {label:>15}: mean {:.3}  (per reference {:?})",
                v.iter().sum::<f64>() / v.len() as f64,
                v.iter().map(|x| (x * 1000.0).round() / 1000.0).collect::<Vec<_>>()
            );
        }
    }
    let empty_closure = closure(&[], &universe, &existence, &locel);

    // Aggregate over the reference threshold instead of fixing one: any single rho is
    // arbitrary, so the score is averaged over the grid.
    println!("\nprecision by reference tau, and aggregated over the grid");
    print!("{:>11} {:>7} {:>7}", "model tau", "|N|", "|N red|");
    for r in REFERENCE_TAUS {
        print!(" {:>7}", format!("r={r}"));
    }
    println!(" {:>8} {:>8}", "mean", "mean_red");

    let empty_closure = closure(&[], &universe, &existence, &locel);
    // Entailment does not depend on the reference threshold, so it is computed once.
    let score_all = |closed: &[OCDeclareArc], w: Weighting| -> Vec<f64> {
        let cov = covered_rows(&rows, closed);
        REFERENCE_TAUS
            .iter()
            .map(|&r| precision_from_coverage(&rows, &cov, r, w).value)
            .collect()
    };
    let mean = |v: &[f64]| v.iter().sum::<f64>() / v.len() as f64;

    let e = score_all(&empty_closure, Weighting::Evidence);
    print!("{:>11} {:>7} {:>7}", "(empty)", 0, 0);
    for v in &e {
        print!(" {v:>7.3}");
    }
    println!(" {:>8.3} {:>8.3}", mean(&e), mean(&e));

    for ((tau, cm, cr), (_, model, reduced)) in closures.iter().zip(models.iter()) {
        let m = score_all(cm, Weighting::Evidence);
        let r = score_all(cr, Weighting::Evidence);
        print!("{tau:>11.2} {:>7} {:>7}", model.len(), reduced.len());
        for v in &m {
            print!(" {v:>7.3}");
        }
        println!(" {:>8.3} {:>8.3}", mean(&m), mean(&r));
    }

    println!("\naggregate under each weighting");
    println!(
        "{:>11} {:>7} {:>10} {:>12} {:>10} {:>12}",
        "model tau", "|N red|", "count", "conf", "evidence", "evid x conf"
    );
    for (w_empty, label) in [(&empty_closure, "(empty)")] {
        let c = mean(&score_all(w_empty, Weighting::Binary));
        let s_ = mean(&score_all(w_empty, Weighting::Support));
        let e_ = mean(&score_all(w_empty, Weighting::Evidence));
        let ec = mean(&score_all(w_empty, Weighting::EvidenceConf));
        println!("{label:>11} {:>7} {c:>10.3} {s_:>12.3} {e_:>10.3} {ec:>12.3}", 0);
    }
    for ((tau, cm, _), (_, _, reduced)) in closures.iter().zip(models.iter()) {
        let c = mean(&score_all(cm, Weighting::Binary));
        let s_ = mean(&score_all(cm, Weighting::Support));
        let e_ = mean(&score_all(cm, Weighting::Evidence));
        let ec = mean(&score_all(cm, Weighting::EvidenceConf));
        println!(
            "{tau:>11.2} {:>7} {c:>10.3} {s_:>12.3} {e_:>10.3} {ec:>12.3}",
            reduced.len()
        );
    }

    if let Some(out) = json_out {
        serde_json::to_writer(File::create(&out).expect("cannot create output"), &rows)
            .expect("cannot write");
        println!("wrote {} rows to {}", rows.len(), out.display());
    }
}
