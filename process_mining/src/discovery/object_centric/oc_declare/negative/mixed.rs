//! The existence half of the candidate space, so that precision can be measured over a mixed
//! model rather than over its negative half alone.
//!
//! Everything here mirrors [`table`](super::table) and the entailment used for negative
//! candidates, with three differences forced by the polarity:
//!
//! * Up to four involvement levels per object type, not three. `Each` and `Any` coincide at
//!   `n_max = 0`, and all three coincide for a type the source activity never carries more
//!   than one object of, whatever the count bounds.
//! * Plain support, not conditional support. Vacuity for an existence constraint is a source
//!   event carrying no object of an involved type, which makes the constraint *easier* to
//!   satisfy rather than impossible to violate, so `conf_L` of the OC-DECLARE paper applies
//!   unchanged.
//! * Entailment runs the other way and along paths: a model entails a candidate when some
//!   *stronger* arc dominates it, or when a path of arcs each dominating it connects its
//!   endpoints. That is the `Trans` relation of the transitive-reduction paper, used forwards.

use std::collections::{HashMap, HashSet};

use itertools::Itertools;
use rayon::prelude::*;

use crate::conformance::object_centric::oc_declare::violation_fraction;
use crate::core::{
    event_data::object_centric::linked_ocel::{
        e2o_rev_type_index::E2ORevByTypeIndex, LinkedOCELAccess, SlimLinkedOCEL,
    },
    process_models::oc_declare::{
        get_activity_object_involvements, get_object_to_object_involvements,
        get_rev_object_to_object_involvements, OCDeclareArc, OCDeclareArcLabel, OCDeclareArcType,
        ObjectTypeAssociation,
    },
};
use crate::discovery::object_centric::oc_declare::get_direct_or_indirect_object_involvements;

use super::table::CandidateRow;
use super::NegativeOCDeclareDiscoveryOptions;

/// `{omitted, Any, Each, All}^n` over the gated types, minus the levels that coincide.
///
/// Where the *source* activity carries at most one object of a type, `Any`, `Each` and `All`
/// denote the same predicate on that type, as~\[OC-DECLARE\] notes. Enumerating all three
/// would put three copies of one constraint into the reference, and since `is_dominated_by` is
/// syntactic a model that spells it one way would be charged for the other two. `singleton`
/// marks those types, and they contribute only `omitted` and `Each`.
fn lattice(types: &[ObjectTypeAssociation], singleton: &[bool]) -> Vec<OCDeclareArcLabel> {
    (0..types.len())
        .map(|i| if singleton[i] { vec![0u8, 2] } else { vec![0, 1, 2, 3] })
        .multi_cartesian_product()
        .map(|v| {
            let (mut any, mut each, mut all) = (Vec::new(), Vec::new(), Vec::new());
            for (i, level) in v.iter().enumerate() {
                match level {
                    1 => any.push(types[i].clone()),
                    2 => each.push(types[i].clone()),
                    3 => all.push(types[i].clone()),
                    _ => {}
                }
            }
            any.sort();
            each.sort();
            all.sort();
            OCDeclareArcLabel { each, any, all }
        })
        .collect()
}

/// Every existence candidate in the gated lattice, with the source events satisfying it.
///
/// Cost is `|pairs| x |arrows| x 4^n`, a third more per type than the negative table.
pub fn existence_candidate_table(
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
    let counts = (Some(1usize), None);

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
            let total = locel.get_evs_of_type(act1).count();
            if total == 0 {
                return Vec::new();
            }
            // A type whose source activity never carries more than one object collapses.
            let singleton: Vec<bool> = types
                .iter()
                .map(|t| {
                    act_ob_inv
                        .get(act1.as_str())
                        .and_then(|m| m.get(super::base_type_name(t)))
                        .is_none_or(|c| c.max <= 1)
                })
                .collect();
            let labels = lattice(&types, &singleton);
            let mut rows = Vec::new();
            for ar in [
                OCDeclareArcType::AS,
                OCDeclareArcType::EF,
                OCDeclareArcType::EP,
            ] {
                if !options.considered_arrow_types.contains(&ar) {
                    continue;
                }
                for label in &labels {
                    let frac =
                        violation_fraction(act1, act2, label, &ar, &counts, locel, Some(&index));
                    let satisfying = ((1.0 - frac) * total as f64).round() as usize;
                    rows.push(CandidateRow {
                        from: act1.clone(),
                        to: act2.clone(),
                        arc_type: ar,
                        label: label.clone(),
                        satisfying,
                        // An existence constraint can fail at any source event, so every one of
                        // them is testable and conditional support coincides with `conf_L`.
                        testable: total,
                        total,
                        counts,
                    });
                }
            }
            rows
        })
        .collect()
}

/// Whether `model` entails the existence candidate `row`.
///
/// Two ways, both from~\[transitive reduction\]: a single arc of the model dominates the
/// candidate, or a path of arcs does, every edge dominating it. The second is `Trans` read
/// forwards, and it is a reachability query rather than a fixpoint, since the premises are
/// arcs of the model and not derived constraints.
///
/// `lossless` applies the guard that an `Any`-involvement shared with an edge beyond the first
/// hop does not chain.
pub fn entailed_existence(row: &CandidateRow, model: &[OCDeclareArc], lossless: bool) -> bool {
    let dominates = |e: &OCDeclareArc| {
        row.arc_type.is_dominated_by_or_eq(&e.arc_type)
            && row.label.is_dominated_by(&e.label)
            && e.counts.0.unwrap_or(0) >= 1
    };
    let mut adj: HashMap<&str, Vec<&OCDeclareArc>> = HashMap::new();
    for e in model.iter().filter(|e| dominates(e)) {
        adj.entry(e.from.as_str()).or_default().push(e);
    }
    let mut seen: HashSet<&str> = HashSet::new();
    let mut queue = vec![(row.from.as_str(), 0usize)];
    seen.insert(row.from.as_str());
    while let Some((node, depth)) = queue.pop() {
        if node == row.to.as_str() && depth > 0 {
            return true;
        }
        for e in adj.get(node).into_iter().flatten() {
            if lossless && depth >= 1 {
                let overlap = row
                    .label
                    .any
                    .iter()
                    .any(|a| e.label.any.iter().any(|b| b == a));
                if overlap {
                    continue;
                }
            }
            if seen.insert(e.to.as_str()) {
                queue.push((e.to.as_str(), depth + 1));
            }
        }
    }
    false
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::core::process_models::oc_declare::{OCDeclareNode, ObjectTypeAssociation};

    fn label(any: &[&str], each: &[&str], all: &[&str]) -> OCDeclareArcLabel {
        let mk = |v: &[&str]| {
            let mut x: Vec<_> = v.iter().map(|s| ObjectTypeAssociation::new_simple(*s)).collect();
            x.sort();
            x
        };
        OCDeclareArcLabel {
            each: mk(each),
            any: mk(any),
            all: mk(all),
        }
    }
    fn row(from: &str, to: &str, l: OCDeclareArcLabel) -> CandidateRow {
        CandidateRow {
            from: from.into(),
            to: to.into(),
            arc_type: OCDeclareArcType::AS,
            label: l,
            satisfying: 1,
            testable: 1,
            total: 1,
            counts: (Some(1), None),
        }
    }
    fn arc(from: &str, to: &str, l: OCDeclareArcLabel) -> OCDeclareArc {
        OCDeclareArc {
            from: OCDeclareNode::new(from),
            to: OCDeclareNode::new(to),
            arc_type: OCDeclareArcType::AS,
            label: l,
            counts: (Some(1), None),
        }
    }

    /// For existence the entailment runs from the *stronger* arc to the weaker candidate, the
    /// opposite of the negative case.
    #[test]
    fn a_stronger_arc_entails_a_weaker_existence_candidate() {
        let weak = row("a", "b", label(&["items"], &[], &[]));
        let strong = arc("a", "b", label(&[], &[], &["items"]));
        assert!(entailed_existence(&weak, std::slice::from_ref(&strong), true));

        let strong_row = row("a", "b", label(&[], &[], &["items"]));
        let weak_arc = arc("a", "b", label(&["items"], &[], &[]));
        assert!(!entailed_existence(&strong_row, std::slice::from_ref(&weak_arc), true));
    }

    /// A path whose every edge dominates the candidate entails it; one whose edges do not, does
    /// not.
    #[test]
    fn a_dominating_path_entails_the_direct_candidate() {
        let c = row("a", "c", label(&[], &[], &["items"]));
        let path = vec![
            arc("a", "b", label(&[], &[], &["items"])),
            arc("b", "c", label(&[], &[], &["items"])),
        ];
        assert!(entailed_existence(&c, &path, true));

        let weak_path = vec![
            arc("a", "b", label(&["items"], &[], &[])),
            arc("b", "c", label(&["items"], &[], &[])),
        ];
        assert!(!entailed_existence(&c, &weak_path, true));
    }

    /// The lossless guard stops an `Any`-involvement chaining past the first hop.
    #[test]
    fn lossless_blocks_any_chaining() {
        let c = row("a", "c", label(&["items"], &[], &[]));
        let path = vec![
            arc("a", "b", label(&["items"], &[], &[])),
            arc("b", "c", label(&["items"], &[], &[])),
        ];
        assert!(!entailed_existence(&c, &path, true));
        assert!(entailed_existence(&c, &path, false));
    }
}
