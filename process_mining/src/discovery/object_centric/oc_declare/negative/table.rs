//! Exhaustive evaluation of the negative candidate space.
//!
//! [`minimal_satisfied`](super::search::minimal_satisfied) reports only the frontier, which is
//! what discovery needs. Quality measures need more: for every candidate in the gated lattice,
//! how many source events satisfy it, how many could ever have violated it, and how many there
//! are. Every weighting one might choose -- binary or support-graded, rate or absolute evidence
//! count, macro or micro aggregation -- is an aggregation over this one table, so it is built
//! once and the choice is made afterwards.
//!
//! Cost is `|pairs| x |arrows| x 3^n` evaluations with `n` the gated type count, so it is
//! affordable only because the gate keeps `n` small. Restrict `acts_to_use` on large logs.

use itertools::Itertools;
use rayon::prelude::*;

use crate::core::{
    event_data::object_centric::linked_ocel::{
        e2o_rev_type_index::E2ORevByTypeIndex, LinkedOCELAccess, SlimLinkedOCEL,
    },
    process_models::oc_declare::{
        get_activity_object_involvements, get_object_to_object_involvements,
        get_rev_object_to_object_involvements, OCDeclareArcLabel, OCDeclareArcType,
        ObjectTypeAssociation,
    },
};
use crate::discovery::object_centric::oc_declare::get_direct_or_indirect_object_involvements;

use super::support::{evaluate, TestabilityIndex};
use super::NegativeOCDeclareDiscoveryOptions;

/// One candidate constraint, with the counts every quality measure aggregates over.
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct CandidateRow {
    /// Source activity.
    pub from: String,
    /// Target activity.
    pub to: String,
    /// Arrow type.
    pub arc_type: OCDeclareArcType,
    /// Object involvement.
    pub label: OCDeclareArcLabel,
    /// Source events at which the constraint holds.
    pub satisfying: usize,
    /// Source events at which it could have been violated.
    pub testable: usize,
    /// Source events of the activity.
    pub total: usize,
    /// Count bounds, so that existence and negative candidates can share one table.
    /// `(Some(0), Some(0))` is negative, `(Some(1), None)` existence.
    pub counts: (Option<usize>, Option<usize>),
}

impl CandidateRow {
    /// Whether this is a negative candidate (`n_max = 0`).
    pub fn is_negative(&self) -> bool {
        self.counts.1 == Some(0)
    }

    /// Fraction of source events satisfying the constraint. The quantity the noise
    /// threshold is compared against.
    pub fn support(&self) -> f64 {
        if self.total == 0 {
            f64::NAN
        } else {
            self.satisfying as f64 / self.total as f64
        }
    }
    /// Fraction of *testable* source events satisfying it.
    pub fn conditional_support(&self) -> f64 {
        if self.testable == 0 {
            f64::NAN
        } else {
            self.satisfying as f64 / self.testable as f64
        }
    }
    /// Whether the constraint would be discovered at this noise threshold: plain support over
    /// all source events, plus at least one testable event.
    ///
    /// Plain support keeps the denominator fixed, so this set is upward closed in the
    /// involvement order. Thresholding on conditional support instead is not monotone, since
    /// strengthening an involvement shrinks the testable set as well.
    pub fn discovered_at(&self, noise_threshold: f64) -> bool {
        self.testable >= 1
            && self.satisfying_all() as f64 >= (1.0 - noise_threshold) * self.total as f64
    }

    /// Source events satisfying the constraint, testable or not.
    ///
    /// An untestable source event has an empty matching set and therefore satisfies, so this is
    /// exactly `satisfying + (total - testable)`.
    pub fn satisfying_all(&self) -> usize {
        self.satisfying + (self.total - self.testable)
    }
}

/// Enumerate `{omitted, Any, All}^n` over the gated types. `Each` is omitted: it collapses
/// onto `Any` at `n_max = 0`, so enumerating it would double-count.
fn lattice(types: &[ObjectTypeAssociation]) -> Vec<OCDeclareArcLabel> {
    (0..types.len())
        .map(|_| 0u8..3)
        .multi_cartesian_product()
        .map(|v| {
            let mut any = Vec::new();
            let mut all = Vec::new();
            for (i, level) in v.iter().enumerate() {
                match level {
                    1 => any.push(types[i].clone()),
                    2 => all.push(types[i].clone()),
                    _ => {}
                }
            }
            any.sort();
            all.sort();
            OCDeclareArcLabel {
                each: Vec::new(),
                any,
                all,
            }
        })
        .collect()
}

/// Evaluate every candidate in the gated lattice, for every activity pair and arrow.
///
/// `options.noise_threshold` is ignored -- the table is threshold-independent by design, so
/// that the threshold selects only which model was discovered and not what it is measured
/// against.
pub fn candidate_table(
    locel: &SlimLinkedOCEL,
    options: &NegativeOCDeclareDiscoveryOptions,
) -> Vec<CandidateRow> {
    let act_ob_inv = get_activity_object_involvements(locel);
    let ob_ob_inv = get_object_to_object_involvements(locel);
    let ob_ob_rev_inv = get_rev_object_to_object_involvements(locel);
    let index = E2ORevByTypeIndex::build(locel);
    let acts_to_use: Vec<String> = options
        .acts_to_use
        .clone()
        .unwrap_or_else(|| locel.get_ev_types().map(|et| et.to_string()).collect());
    let types_universe: Vec<String> = locel.get_ob_types().map(|ot| ot.to_string()).collect();
    let testability = TestabilityIndex::build(locel, &acts_to_use, &types_universe);
    let arrows = [
        OCDeclareArcType::AS,
        OCDeclareArcType::EF,
        OCDeclareArcType::EP,
    ];

    acts_to_use
        .iter()
        .cartesian_product(acts_to_use.iter())
        .filter(|(a, b)| a != b)
        .par_bridge()
        .flat_map(|(act1, act2)| {
            let types: Vec<ObjectTypeAssociation> = get_direct_or_indirect_object_involvements(
                act1,
                act2,
                &act_ob_inv,
                &ob_ob_inv,
                &ob_ob_rev_inv,
                options.o2o_mode,
            )
            .into_iter()
            .map(|(ot, _)| ot)
            .collect();
            if types.is_empty() {
                return Vec::new();
            }
            let labels = lattice(&types);
            let mut rows = Vec::with_capacity(labels.len() * arrows.len());
            for ar in arrows {
                if !options.considered_arrow_types.contains(&ar) {
                    continue;
                }
                for label in &labels {
                    let (satisfying, testable, total) =
                        evaluate(act1, act2, label, ar, locel, &index, &testability);
                    rows.push(CandidateRow {
                        from: act1.clone(),
                        to: act2.clone(),
                        arc_type: ar,
                        label: label.clone(),
                        satisfying,
                        testable,
                        total,
                        counts: (Some(0), Some(0)),
                    });
                }
            }
            rows
        })
        .collect()
}
