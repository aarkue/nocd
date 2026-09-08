//! Minimal-satisfied frontier search for negative constraints.
use std::collections::{HashMap, HashSet};

use crate::core::{
    event_data::object_centric::linked_ocel::{
        e2o_rev_type_index::E2ORevByTypeIndex, SlimLinkedOCEL,
    },
    process_models::oc_declare::{OCDeclareArcLabel, OCDeclareArcType, ObjectTypeAssociation},
};

use super::support::{clears_threshold, TestabilityIndex};

// `any`/`all` must come out sorted: `OCDeclareArcLabel`'s derived `Eq`/`Hash` are
// vector-order-sensitive, and the rest of the codebase relies on labels always being
// canonically sorted (see `OCDeclareArcLabel::combine`) to compare equal across different
// activity pairs regardless of `types`'s own (HashMap-derived, per-call-random) order.
fn vector_to_label(v: &[u8], types: &[ObjectTypeAssociation]) -> OCDeclareArcLabel {
    let mut any = Vec::new();
    let mut all = Vec::new();
    for (i, &level) in v.iter().enumerate() {
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
}

#[allow(clippy::too_many_arguments)]
fn eval_cached(
    v: &[u8],
    types: &[ObjectTypeAssociation],
    act1: &str,
    act2: &str,
    arc_type: OCDeclareArcType,
    noise_threshold: f64,
    locel: &SlimLinkedOCEL,
    index: &E2ORevByTypeIndex,
    testability: &TestabilityIndex,
    memo: &mut HashMap<Vec<u8>, bool>,
) -> bool {
    if let Some(&r) = memo.get(v) {
        return r;
    }
    // Plain support, so that the clearing set is upward closed and the frontier's pruning is
    // sound. Conditional support is not monotone in the involvement order.
    let label = vector_to_label(v, types);
    // Only the plain-support verdict drives the frontier, which is what keeps the clearing set
    // upward closed; testability is applied as a filter after the search.
    let (r, _) = clears_threshold(
        act1, act2, &label, arc_type, noise_threshold, locel, index, testability,
    );
    memo.insert(v.to_vec(), r);
    r
}

// Arrow codes for the joint lattice: AS sits below both ordered arrows, which are
// incomparable to each other. `Each` is never enumerated, collapsing onto `Any` at n_max = 0.
const AR_AS: u8 = 0;
const AR_EF: u8 = 1;
const AR_EP: u8 = 2;

fn arc_type_of(a: u8) -> OCDeclareArcType {
    match a {
        AR_AS => OCDeclareArcType::AS,
        AR_EF => OCDeclareArcType::EF,
        _ => OCDeclareArcType::EP,
    }
}

#[allow(clippy::too_many_arguments)]
fn eval_joint(
    a: u8,
    v: &[u8],
    types: &[ObjectTypeAssociation],
    act1: &str,
    act2: &str,
    noise_threshold: f64,
    locel: &SlimLinkedOCEL,
    index: &E2ORevByTypeIndex,
    testability: &TestabilityIndex,
    memo: &mut HashMap<(u8, Vec<u8>), bool>,
) -> bool {
    if let Some(&r) = memo.get(&(a, v.to_vec())) {
        return r;
    }
    let label = vector_to_label(v, types);
    let (r, _) = clears_threshold(
        act1,
        act2,
        &label,
        arc_type_of(a),
        noise_threshold,
        locel,
        index,
        testability,
    );
    memo.insert((a, v.to_vec()), r);
    r
}

/// `<=`-minimal satisfied nodes of the joint lattice over arrow type *and* object involvement.
///
/// Searching the arrow types together rather than one at a time makes the result an antichain:
/// no returned constraint is `<=` another, so none is implied by another under reversed
/// domination. Per arrow type the search would return e.g. both the EF and the EP node where
/// the AS node below them already holds, and a later reduction pass would have to delete them.
#[allow(clippy::too_many_arguments)]
pub(crate) fn minimal_satisfied_joint(
    act1: &str,
    act2: &str,
    arrows: &HashSet<OCDeclareArcType>,
    types: &[ObjectTypeAssociation],
    noise_threshold: f64,
    locel: &SlimLinkedOCEL,
    index: &E2ORevByTypeIndex,
    testability: &TestabilityIndex,
) -> Vec<(OCDeclareArcType, OCDeclareArcLabel)> {
    let n = types.len();
    let considered: Vec<u8> = [AR_AS, AR_EF, AR_EP]
        .into_iter()
        .filter(|&a| arrows.contains(&arc_type_of(a)))
        .collect();
    if considered.is_empty() {
        return Vec::new();
    }
    let has_as = considered.contains(&AR_AS);
    let mut memo: HashMap<(u8, Vec<u8>), bool> = HashMap::new();
    let mut minimal = Vec::new();
    let mut seen: HashSet<(u8, Vec<u8>)> = HashSet::new();
    // Start from every considered arrow with no considered arrow below it.
    let mut frontier: Vec<(u8, Vec<u8>)> = if has_as {
        vec![(AR_AS, vec![0u8; n])]
    } else {
        considered.iter().map(|&a| (a, vec![0u8; n])).collect()
    };
    while !frontier.is_empty() {
        let mut next: HashSet<(u8, Vec<u8>)> = HashSet::new();
        for (a, v) in &frontier {
            if !seen.insert((*a, v.clone())) {
                continue;
            }
            if eval_joint(
                *a,
                v,
                types,
                act1,
                act2,
                noise_threshold,
                locel,
                index,
                testability,
                &mut memo,
            ) {
                minimal.push((arc_type_of(*a), vector_to_label(v, types)));
                continue;
            }
            let mut succs: Vec<(u8, Vec<u8>)> = Vec::new();
            for i in 0..n {
                if v[i] < 2 {
                    let mut w = v.clone();
                    w[i] += 1;
                    succs.push((*a, w));
                }
            }
            if *a == AR_AS {
                for &b in &[AR_EF, AR_EP] {
                    if considered.contains(&b) {
                        succs.push((b, v.clone()));
                    }
                }
            }
            for (b, w) in succs {
                // Reach a node only once every immediate predecessor is unsatisfied. Satisfaction
                // is upward closed, so a satisfied predecessor means something below already
                // covers this node.
                let mut open = true;
                for j in 0..n {
                    if w[j] > 0 {
                        let mut p = w.clone();
                        p[j] -= 1;
                        if eval_joint(
                            b, &p, types, act1, act2, noise_threshold, locel, index, testability,
                            &mut memo,
                        ) {
                            open = false;
                            break;
                        }
                    }
                }
                // The predecessor in the arrow dimension.
                if open
                    && b != AR_AS
                    && has_as
                    && eval_joint(
                        AR_AS, &w, types, act1, act2, noise_threshold, locel, index, testability,
                        &mut memo,
                    )
                {
                    open = false;
                }
                if open {
                    next.insert((b, w));
                }
            }
        }
        frontier = next.into_iter().collect();
    }
    minimal
}

/// `<=`-minimal satisfied involvement vectors over `{omitted, Any, All}^types`.
/// `Each` is never enumerated — it collapses onto `Any` at `n_max = 0`.
#[allow(clippy::too_many_arguments)]
#[allow(dead_code)]
pub(crate) fn minimal_satisfied(
    act1: &str,
    act2: &str,
    arc_type: OCDeclareArcType,
    types: &[ObjectTypeAssociation],
    noise_threshold: f64,
    locel: &SlimLinkedOCEL,
    index: &E2ORevByTypeIndex,
    testability: &TestabilityIndex,
) -> Vec<OCDeclareArcLabel> {
    let n = types.len();
    let mut memo: HashMap<Vec<u8>, bool> = HashMap::new();
    let mut minimal = Vec::new();
    let mut seen: HashSet<Vec<u8>> = HashSet::new();
    let mut frontier: Vec<Vec<u8>> = vec![vec![0u8; n]];
    while !frontier.is_empty() {
        let mut next: HashSet<Vec<u8>> = HashSet::new();
        for v in &frontier {
            if !seen.insert(v.clone()) {
                continue;
            }
            if eval_cached(v, types, act1, act2, arc_type, noise_threshold, locel, index, testability, &mut memo) {
                minimal.push(vector_to_label(v, types));
                continue;
            }
            for i in 0..n {
                if v[i] < 2 {
                    let mut w = v.clone();
                    w[i] += 1;
                    let preds_unsatisfied = (0..n).filter(|&j| w[j] > 0).all(|j| {
                        let mut p = w.clone();
                        p[j] -= 1;
                        !eval_cached(&p, types, act1, act2, arc_type, noise_threshold, locel, index, testability, &mut memo)
                    });
                    if preds_unsatisfied {
                        next.insert(w);
                    }
                }
            }
        }
        frontier = next.into_iter().collect();
    }
    minimal
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::core::{
        event_data::object_centric::{
            appendable::AppendableOCEL, linked_ocel::e2o_rev_type_index::E2ORevByTypeIndex,
            OCELRelationship, OCELType,
        },
        process_models::oc_declare::ObjectTypeAssociation,
    };
    use chrono::DateTime;

    fn empty_type(name: &str) -> OCELType {
        OCELType {
            name: name.into(),
            attributes: Vec::new(),
        }
    }
    fn rel(object_id: &str) -> OCELRelationship {
        OCELRelationship {
            object_id: object_id.into(),
            qualifier: "q".into(),
        }
    }

    fn test_index(locel: &SlimLinkedOCEL) -> TestabilityIndex {
        TestabilityIndex::build(
            locel,
            &["a".to_string(), "b".to_string()],
            &["items".to_string()],
        )
    }

    /// `a -/-> b` on `items`: `b1` shares no item with either `a`-event, so `{}` is
    /// unsatisfied (a `b`-event exists at all) and `Any(items)` is the unique minimal
    /// satisfied node — `All(items)` above it must not also be reported.
    fn sample_locel() -> SlimLinkedOCEL {
        let mut s = SlimLinkedOCEL::new();
        s.declare_event_type(empty_type("a")).unwrap();
        s.declare_event_type(empty_type("b")).unwrap();
        s.declare_object_type(empty_type("items")).unwrap();
        for id in ["i1", "i2", "i3"] {
            s.append_object(id.into(), "items", Vec::new(), Vec::new())
                .unwrap();
        }
        let t = |i: u32| DateTime::parse_from_rfc3339(&format!("2024-01-0{i}T00:00:00Z")).unwrap();
        s.append_event("a1".into(), "a", t(1), Vec::new(), vec![rel("i1")])
            .unwrap();
        s.append_event("a2".into(), "a", t(2), Vec::new(), vec![rel("i2")])
            .unwrap();
        s.append_event("b1".into(), "b", t(3), Vec::new(), vec![rel("i3")])
            .unwrap();
        s.finalize().unwrap();
        s
    }

    #[test]
    fn reports_the_minimal_satisfied_node_only() {
        let locel = sample_locel();
        let index = E2ORevByTypeIndex::build(&locel);
        let types = vec![ObjectTypeAssociation::new_simple("items")];
        let labels = minimal_satisfied(
            "a",
            "b",
            crate::core::process_models::oc_declare::OCDeclareArcType::AS,
            &types,
            0.0,
            &locel,
            &index,
            &test_index(&locel),
        );
        assert_eq!(labels.len(), 1);
        assert_eq!(labels[0].any, types);
        assert!(labels[0].all.is_empty());
    }

    #[test]
    fn support_is_upward_closed_over_the_lattice() {
        let locel = sample_locel();
        let index = E2ORevByTypeIndex::build(&locel);
        use crate::core::process_models::oc_declare::OCDeclareArcType;
        let types = vec![ObjectTypeAssociation::new_simple("items")];
        let mut memo = std::collections::HashMap::new();
        let rates: Vec<bool> = (0..3u8)
            .map(|level| {
                eval_cached(
                    &[level],
                    &types,
                    "a",
                    "b",
                    OCDeclareArcType::AS,
                    0.0,
                    &locel,
                    &index,
                    &test_index(&locel),
                    &mut memo,
                )
            })
            .collect();
        for i in 0..rates.len() {
            if rates[i] {
                assert!(
                    rates[i..].iter().all(|&r| r),
                    "support fell going from level {i} upward"
                );
            }
        }
    }
}
