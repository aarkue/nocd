//! Negative OC-DECLARE (`n_min = n_max = 0`) discovery and mixed-model reduction.
pub(crate) mod equiv;
pub use equiv::{derived_equivalences, rule_c_rewritings};
mod mixed;
mod quality;
pub mod reduce;
mod search;
mod support;
mod table;

pub use quality::{
    closure, entailed_by_rules, entailed_by_rules_with_base, entailed_by_weakening,
    covered_rows, minimal_satisfied_rows, precision, precision_from_coverage,
    precision_of_closed, Entailment, Precision,
    Weighting,
};
pub use mixed::{entailed_existence, existence_candidate_table};
pub use table::{candidate_table, CandidateRow};

use std::collections::HashSet;

use itertools::Itertools;
use macros_process_mining::register_binding;
use rayon::prelude::*;
use schemars::JsonSchema;
use serde::{Deserialize, Serialize};

use crate::core::{
    event_data::object_centric::linked_ocel::{
        e2o_rev_type_index::E2ORevByTypeIndex, LinkedOCELAccess, SlimLinkedOCEL,
    },
    process_models::oc_declare::{
        get_activity_object_facts, get_activity_object_involvements,
        get_object_to_object_involvements, get_rev_object_to_object_involvements, OCDeclareArc,
        OCDeclareArcType, OCDeclareNode, ObjectTypeAssociation,
    },
};
use crate::discovery::object_centric::oc_declare::{get_direct_or_indirect_object_involvements, O2OMode};

use search::minimal_satisfied_joint;
use support::{clears_threshold, TestabilityIndex};

pub(crate) fn base_type_name(ot: &ObjectTypeAssociation) -> &str {
    match ot {
        ObjectTypeAssociation::Simple { object_type } => object_type,
        ObjectTypeAssociation::O2O { second, .. } => second,
    }
}

/// Options for negative OC-DECLARE discovery.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize, JsonSchema)]
pub struct NegativeOCDeclareDiscoveryOptions {
    /// Noise threshold (i.e., what fraction of source events are allowed to still match)
    pub noise_threshold: f64,
    /// Determines if/how object-to-object relationships are considered
    pub o2o_mode: O2OMode,
    /// Activities to use for the discovery. If this is `None`, all activities of the OCEL are used
    pub acts_to_use: Option<Vec<String>>,
    /// Only `AS`/`EF`/`EP` have any effect; `DF`/`DP` are never searched as the forbidding arrow.
    pub considered_arrow_types: HashSet<OCDeclareArcType>,
}

impl Default for NegativeOCDeclareDiscoveryOptions {
    fn default() -> Self {
        Self {
            noise_threshold: 0.2,
            o2o_mode: O2OMode::None,
            acts_to_use: None,
            considered_arrow_types: [
                OCDeclareArcType::AS,
                OCDeclareArcType::EF,
                OCDeclareArcType::EP,
            ]
            .into_iter()
            .collect(),
        }
    }
}

/// Discover negative OC-DECLARE constraints: frontier search then conditional-support
/// prune. Reduction against an existence model is a
/// separate step, [`reduce_negative_oc_declare`].
#[register_binding(name = "discover_negative_oc_declare")]
pub fn discover_negative_oc_declare(
    locel: &SlimLinkedOCEL,
    #[bind(default = Default::default())] options: NegativeOCDeclareDiscoveryOptions,
) -> Vec<OCDeclareArc> {
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
    let raw: Vec<OCDeclareArc> = acts_to_use
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
            minimal_satisfied_joint(
                act1,
                act2,
                &options.considered_arrow_types,
                &types,
                options.noise_threshold,
                locel,
                &index,
                &testability,
            )
            .into_iter()
            .map(|(ar, label)| OCDeclareArc {
                from: OCDeclareNode::new(act1.clone()),
                to: OCDeclareNode::new(act2.clone()),
                arc_type: ar,
                label,
                counts: (Some(0), Some(0)),
            })
            .collect::<Vec<_>>()
        })
        .collect();

    // Testability is a filter, not part of the threshold: a constraint no source event could
    // ever have violated says nothing, and letting it into the model would let it serve as a
    // composition premise and delete an informative constraint.
    raw.into_iter()
        .filter(|arc| {
            let (clears, any_testable) = clears_threshold(
                arc.from.as_str(),
                arc.to.as_str(),
                &arc.label,
                arc.arc_type,
                options.noise_threshold,
                locel,
                &index,
                &testability,
            );
            clears && any_testable
        })
        .collect()
}

/// Reduce a mixed model: `negative` constraints against a caller-supplied `existing` (existence)
/// model. Always applies the full sound pipeline -- no lossy mode, unlike existence
/// reduction.
#[register_binding(name = "reduce_negative_oc_declare")]
pub fn reduce_negative_oc_declare(
    locel: &SlimLinkedOCEL,
    existing: &[OCDeclareArc],
    negative: Vec<OCDeclareArc>,
) -> Vec<OCDeclareArc> {
    reduce_negative_oc_declare_traced(locel, existing, negative).0
}

/// How many constraints each stage of the reduction pipeline removed.
///
/// The three composition rules do not remove anything on their own -- they contribute edges to
/// one shared derivation digraph, and the condensation of that digraph is what deletes. The
/// `*_alone` fields are therefore counterfactuals: what condensation would have removed had only
/// that rule contributed edges. They overlap with each other and generally sum to more than
/// `condensation`.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize, JsonSchema)]
pub struct ReductionTrace {
    /// Constraints handed to the reduction.
    pub input: usize,
    /// Stage 1 removals: vacuously satisfied by an `All` cardinality mismatch.
    pub cardinality_entailed: usize,
    /// Stage 2 removals: dominated by another arc on the same activity pair.
    pub dominated: usize,
    /// Derivation edges contributed by source-anchored composition.
    pub source_anchored_edges: usize,
    /// Derivation edges contributed by target-anchored composition.
    pub target_anchored_edges: usize,
    /// Derivation edges contributed by rule C (object-set equivalence).
    pub rule_c_edges: usize,
    /// Removals by condensing the digraph of all three rules' edges.
    pub condensation: usize,
    /// Counterfactual: condensation with only the source-anchored edges.
    pub condensation_source_alone: usize,
    /// Counterfactual: condensation with only the target-anchored edges.
    pub condensation_target_alone: usize,
    /// Counterfactual: condensation with only rule C's edges.
    pub condensation_rule_c_alone: usize,
    /// Removals by rule B/B'.
    pub rule_b: usize,
    /// Removals by orientation dedup.
    pub orientation_dedup: usize,
    /// Constraints surviving the whole pipeline.
    pub output: usize,
}

/// [`reduce_negative_oc_declare`] plus a per-stage removal count.
pub fn reduce_negative_oc_declare_traced(
    locel: &SlimLinkedOCEL,
    existing: &[OCDeclareArc],
    negative: Vec<OCDeclareArc>,
) -> (Vec<OCDeclareArc>, ReductionTrace) {
    let act_ob_inv = get_activity_object_involvements(locel);
    let facts = get_activity_object_facts(locel);
    reduce_with_facts(&act_ob_inv, &facts, existing, negative)
}

/// [`reduce_negative_oc_declare_traced`] against a caller-supplied fact table.
///
/// Exposed so a caller can falsify one log fact and re-run, which is how the
/// load-bearing subset of the invoked conditions is measured.
pub fn reduce_with_facts(
    act_ob_inv: &std::collections::HashMap<
        String,
        std::collections::HashMap<String, crate::core::process_models::oc_declare::ObjectInvolvementCounts>,
    >,
    facts: &std::collections::HashMap<
        String,
        std::collections::HashMap<
            String,
            crate::core::process_models::oc_declare::ActivityObjectFacts,
        >,
    >,
    existing: &[OCDeclareArc],
    negative: Vec<OCDeclareArc>,
) -> (Vec<OCDeclareArc>, ReductionTrace) {
    let mut trace = ReductionTrace {
        input: negative.len(),
        ..Default::default()
    };

    let after_cardinality: Vec<OCDeclareArc> = negative
        .into_iter()
        .filter(|c| !reduce::cardinality_entailed(c, act_ob_inv, facts))
        .collect();
    trace.cardinality_entailed = trace.input - after_cardinality.len();

    let n_before_domination = after_cardinality.len();
    let m1 = reduce::drop_dominated(after_cardinality);
    trace.dominated = n_before_domination - m1.len();

    let source_edges = reduce::source_anchored_edges(&m1, existing, facts);
    let target_edges = reduce::target_anchored_edges(&m1, existing);
    let rule_c = equiv::rule_c_edges(&m1, existing, facts);
    let count_edges = |m: &std::collections::HashMap<OCDeclareArc, HashSet<OCDeclareArc>>| {
        m.values().map(|s| s.len()).sum::<usize>()
    };
    trace.source_anchored_edges = count_edges(&source_edges);
    trace.target_anchored_edges = count_edges(&target_edges);
    trace.rule_c_edges = count_edges(&rule_c);
    trace.condensation_source_alone = m1.len() - reduce::condense(&m1, &source_edges).len();
    trace.condensation_target_alone = m1.len() - reduce::condense(&m1, &target_edges).len();
    trace.condensation_rule_c_alone = m1.len() - reduce::condense(&m1, &rule_c).len();

    let edges = reduce::merge_edges(vec![source_edges, target_edges, rule_c]);
    let condensed = reduce::condense(&m1, &edges);
    trace.condensation = m1.len() - condensed.len();

    let n_before_rule_b = condensed.len();
    let after_rule_b: Vec<OCDeclareArc> = condensed
        .into_iter()
        .filter(|c| !reduce::rule_b_removable(c, existing, facts))
        .collect();
    trace.rule_b = n_before_rule_b - after_rule_b.len();

    let n_before_dedup = after_rule_b.len();
    let out = reduce::orientation_dedup(after_rule_b, facts);
    trace.orientation_dedup = n_before_dedup - out.len();
    trace.output = out.len();
    (out, trace)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::core::event_data::object_centric::ocel_xml::import_ocel_xml_path;
    use crate::discovery::object_centric::oc_declare::{
        discover_behavior_constraints, OCDeclareDiscoveryOptions, OCDeclareReductionMode,
    };
    use crate::test_utils::get_test_data_path;

    fn order_management_locel() -> SlimLinkedOCEL {
        let path = get_test_data_path().join("ocel").join("order-management.xml");
        let ocel = import_ocel_xml_path(path).unwrap();
        SlimLinkedOCEL::from_ocel(ocel)
    }

    /// Pins the reduced model size on the bundled Order Management log, against an existence
    /// model this crate discovers itself.
    #[test]
    fn full_pipeline_matches_the_reference_counts_on_order_management() {
        let locel = order_management_locel();
        let existence_options = OCDeclareDiscoveryOptions {
            o2o_mode: O2OMode::None,
            counts_for_filter: (Some(1), None),
            reduction: OCDeclareReductionMode::None,
            ..Default::default()
        };
        let existing = discover_behavior_constraints(&locel, existence_options);

        // The tau > 0 counts depend on the threshold being on plain support with testability
        // applied as a filter afterwards; at tau = 0 the two notions coincide.
        for (tau, expected) in [(0.0, 12), (0.1, 47), (0.2, 61)] {
            let negative_options = NegativeOCDeclareDiscoveryOptions {
                noise_threshold: tau,
                ..Default::default()
            };
            let negative = discover_negative_oc_declare(&locel, negative_options);
            let reduced = reduce_negative_oc_declare(&locel, &existing, negative);
            assert_eq!(
                reduced.len(),
                expected,
                "tau={tau}: got {} arcs, expected {expected}",
                reduced.len()
            );
        }
    }

    /// Losslessness, checked rather than argued: everything the discovered model entails, the
    /// reduced model still entails. This is the property the reduction exists for, and it is
    /// what makes precision the right quality measure -- the score must not move when the
    /// model shrinks.
    #[test]
    fn reduction_preserves_the_closure_on_order_management() {
        use std::collections::HashSet;

        let locel = order_management_locel();
        let existing = discover_behavior_constraints(
            &locel,
            OCDeclareDiscoveryOptions {
                o2o_mode: O2OMode::None,
                counts_for_filter: (Some(1), None),
                reduction: OCDeclareReductionMode::None,
                ..Default::default()
            },
        );
        let model = discover_negative_oc_declare(
            &locel,
            NegativeOCDeclareDiscoveryOptions {
                noise_threshold: 0.0,
                ..Default::default()
            },
        );
        let reduced = reduce_negative_oc_declare(&locel, &existing, model.clone());
        assert!(
            reduced.len() < model.len(),
            "check is vacuous unless the reduction actually removed something"
        );

        let from_model: HashSet<_> = closure(&model, &model, &existing, &locel).into_iter().collect();
        let from_reduced: HashSet<_> =
            closure(&reduced, &model, &existing, &locel).into_iter().collect();
        let lost: Vec<_> = from_model.difference(&from_reduced).collect();
        assert!(
            lost.is_empty(),
            "reduction lost {} of {} entailed arcs, e.g. {:?}",
            lost.len(),
            from_model.len(),
            lost.first()
        );
    }

    /// Pins the per-stage attribution reported in the paper, and so uses the same existence
    /// model: arrows AS/EF/EP, `All` for single-valued types. Cardinality entailment firing
    /// zero times here is a real property of the log, not a broken stage: no activity pair has
    /// an `All`-involved type whose source minimum exceeds the target maximum. Domination
    /// firing zero times likewise: the search traverses arrow types and involvements jointly,
    /// so it never reports a dominated arc in the first place.
    #[test]
    fn stage_attribution_on_order_management_at_tau_zero() {
        let locel = order_management_locel();
        let existing = discover_behavior_constraints(
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
        assert_eq!(existing.len(), 220);
        let negative = discover_negative_oc_declare(
            &locel,
            NegativeOCDeclareDiscoveryOptions {
                noise_threshold: 0.0,
                ..Default::default()
            },
        );
        let (out, t) = reduce_negative_oc_declare_traced(&locel, &existing, negative);

        assert_eq!(t.input, 140);
        assert_eq!(t.cardinality_entailed, 0);
        assert_eq!(t.dominated, 0);
        assert_eq!(t.condensation, 84);
        assert_eq!(t.rule_b, 45);
        assert_eq!(t.orientation_dedup, 2);
        assert_eq!(t.output, 9);
        assert_eq!(out.len(), 9);
        assert_eq!(
            t.input - t.cardinality_entailed - t.dominated - t.condensation - t.rule_b
                - t.orientation_dedup,
            t.output,
            "the stage removals must partition the input"
        );
        // Each composition rule pulls its weight; none is subsumed by the others.
        assert!(t.condensation_source_alone > 0);
        assert!(t.condensation_target_alone > 0);
        assert!(t.condensation_rule_c_alone > 0);
    }
}
