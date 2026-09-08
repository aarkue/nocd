//! Rule C: object-set equivalence, equality version.
use std::collections::{BTreeSet, HashMap, HashSet};

use crate::core::process_models::oc_declare::{
    ActivityObjectFacts, OCDeclareArc, OCDeclareArcType, OCDeclareNode,
};

use super::base_type_name;

/// Keyed by the type set the premise pair established the equivalence on, not by single type:
/// `A ~_S B` asks one partner event to agree on all of `S` at once, which conjoining a pair
/// established on `S1` with one established on `S2` does not give.
type Equivalence = HashMap<BTreeSet<String>, HashSet<(String, String)>>;
/// Keyed by type set for the same reason as `Equivalence`: the order fact is a property of the
/// pairing that established it, so a transport over `dom` may only read an order derived from a
/// pairing whose key covers `dom`, not one established on some unrelated type set.
type Order = HashMap<(BTreeSet<String>, String, String), Option<String>>;

fn is_anchor(a: &str, b: &str, ot: &str, facts: &HashMap<String, HashMap<String, ActivityObjectFacts>>) -> bool {
    let ok = |act: &str| {
        facts
            .get(act)
            .and_then(|m| m.get(ot))
            .is_some_and(|f| f.always_present && f.at_most_one_event_per_object)
    };
    ok(a) && ok(b)
}

/// Direct (non-transitive) pairings from the existence model, rule C's premises.
fn direct_pairings(
    existing: &[OCDeclareArc],
    facts: &HashMap<String, HashMap<String, ActivityObjectFacts>>,
) -> (Equivalence, Order) {
    let mut eq: Equivalence = HashMap::new();
    let mut order: Order = HashMap::new();
    for e1 in existing {
        let s1: HashSet<&str> = e1.label.all.iter().map(base_type_name).collect();
        if s1.is_empty() {
            continue;
        }
        let a = e1.from.as_str();
        let b = e1.to.as_str();
        for e2 in existing {
            if e2.from.as_str() != b || e2.to.as_str() != a {
                continue;
            }
            // rule C's premises only need existence (n_min >= 1, filtered at the call site) --
            // the soundness proof never uses ar1/ar2's arrow type. Arrow type matters
            // only below, for determining EF/EP transport order, not for premise validity.
            let s2: HashSet<&str> = e2.label.all.iter().map(base_type_name).collect();
            let shared: HashSet<&str> = s1.intersection(&s2).copied().collect();
            if shared.is_empty() || !shared.iter().any(|ot| is_anchor(a, b, ot, facts)) {
                continue;
            }
            let key: BTreeSet<String> = shared.iter().map(|s| s.to_string()).collect();
            let entry = eq.entry(key.clone()).or_default();
            entry.insert((a.to_string(), b.to_string()));
            entry.insert((b.to_string(), a.to_string()));
            // DF/DP carry the same temporal fact as EF/EP, only more precisely -- treat them
            // the same for order determination (same reasoning as the DF/DP premise
            // broadening in reduce.rs's src_admissible/tgt_admissible).
            let is_forward = |t: OCDeclareArcType| {
                matches!(t, OCDeclareArcType::EF | OCDeclareArcType::DF)
            };
            let is_backward = |t: OCDeclareArcType| {
                matches!(t, OCDeclareArcType::EP | OCDeclareArcType::DP)
            };
            let earlier = if is_forward(e1.arc_type) {
                Some(a.to_string())
            } else if is_backward(e1.arc_type) || is_forward(e2.arc_type) {
                Some(b.to_string())
            } else if is_backward(e2.arc_type) {
                Some(a.to_string())
            } else {
                None
            };
            order
                .entry((key.clone(), a.to_string(), b.to_string()))
                .or_insert_with(|| earlier.clone());
            order
                .entry((key, b.to_string(), a.to_string()))
                .or_insert_with(|| earlier);
        }
    }
    (eq, order)
}

/// Activities object-set-equal to `activity` on every type in `dom`, at once.
///
/// A pair established on `S` restricts to any `dom` inside `S`, and restricted pairs compose,
/// so the relation to close is the union of the pairs whose key covers `dom` -- never the
/// per-type conjunction, which would admit partners agreeing on one type each.
fn cls(activity: &str, dom: &[&str], eq: &Equivalence) -> HashSet<String> {
    let mut adj: HashMap<&str, HashSet<&str>> = HashMap::new();
    for (key, pairs) in eq {
        if !dom.iter().all(|ot| key.contains(*ot)) {
            continue;
        }
        for (a, b) in pairs {
            adj.entry(a.as_str()).or_default().insert(b.as_str());
        }
    }
    let mut seen: HashSet<String> = [activity.to_string()].into_iter().collect();
    let mut stack = vec![activity];
    while let Some(u) = stack.pop() {
        for v in adj.get(u).into_iter().flatten() {
            if seen.insert(v.to_string()) {
                stack.push(v);
            }
        }
    }
    seen
}

/// Entailment edges from rule C: `p -> c` when `p` and `c` differ only by swapping one endpoint
/// for an object-set-equal activity.
pub(crate) fn rule_c_edges(
    m1: &[OCDeclareArc],
    existing: &[OCDeclareArc],
    facts: &HashMap<String, HashMap<String, ActivityObjectFacts>>,
) -> HashMap<OCDeclareArc, HashSet<OCDeclareArc>> {
    let existing: Vec<OCDeclareArc> = existing
        .iter()
        .filter(|e| e.counts.0.unwrap_or(0) >= 1)
        .cloned()
        .collect();
    let (eq, order) = direct_pairings(&existing, facts);
    let m1_set: HashSet<&OCDeclareArc> = m1.iter().collect();
    let mut edges: HashMap<OCDeclareArc, HashSet<OCDeclareArc>> = HashMap::new();
    for c in m1 {
        let dom: Vec<&str> = c
            .label
            .each
            .iter()
            .chain(c.label.any.iter())
            .chain(c.label.all.iter())
            .map(base_type_name)
            .collect();
        if dom.is_empty() {
            continue;
        }
        let s = c.from.as_str();
        let t = c.to.as_str();
        match c.arc_type {
            OCDeclareArcType::AS => {
                for s2 in cls(s, &dom, &eq) {
                    for t2 in cls(t, &dom, &eq) {
                        if s2 == t2 || (s2.as_str(), t2.as_str()) == (s, t) {
                            continue;
                        }
                        let premise = OCDeclareArc {
                            from: OCDeclareNode::new(s2.clone()),
                            to: OCDeclareNode::new(t2.clone()),
                            arc_type: c.arc_type,
                            label: c.label.clone(),
                            counts: c.counts,
                        };
                        if let Some(&p) = m1_set.get(&premise) {
                            edges.entry(p.clone()).or_default().insert(c.clone());
                        }
                    }
                }
            }
            OCDeclareArcType::EF | OCDeclareArcType::EP => {
                for s2 in cls(s, &dom, &eq) {
                    if s2 == s || s2 == t {
                        continue;
                    }
                    let outer = if c.arc_type == OCDeclareArcType::EF { s2.as_str() } else { s };
                    // A directly paired (s2, s), as before, but only an order established by a
                    // pairing that itself covers `dom` may license the transport.
                    let ordered = order.iter().any(|((key, a, b), earlier)| {
                        a.as_str() == s2.as_str()
                            && b.as_str() == s
                            && dom.iter().all(|ot| key.contains(*ot))
                            && earlier.as_deref() == Some(outer)
                    });
                    if !ordered {
                        continue;
                    }
                    let premise = OCDeclareArc {
                        from: OCDeclareNode::new(s2.clone()),
                        to: c.to.clone(),
                        arc_type: c.arc_type,
                        label: c.label.clone(),
                        counts: c.counts,
                    };
                    if let Some(&p) = m1_set.get(&premise) {
                        edges.entry(p.clone()).or_default().insert(c.clone());
                    }
                }
            }
            OCDeclareArcType::DF | OCDeclareArcType::DP => {}
        }
    }
    edges
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::core::process_models::oc_declare::{
        ActivityObjectFacts, OCDeclareArcLabel, OCDeclareArcType, OCDeclareNode,
        ObjectTypeAssociation,
    };
    use std::collections::HashMap;

    fn arc(from: &str, to: &str, arc_type: OCDeclareArcType, label: OCDeclareArcLabel) -> OCDeclareArc {
        OCDeclareArc {
            from: OCDeclareNode::new(from),
            to: OCDeclareNode::new(to),
            arc_type,
            label,
            counts: (Some(0), Some(0)),
        }
    }
    fn requiring(from: &str, to: &str, arc_type: OCDeclareArcType, label: OCDeclareArcLabel) -> OCDeclareArc {
        OCDeclareArc {
            counts: (Some(1), None),
            ..arc(from, to, arc_type, label)
        }
    }
    fn any_label(ot: &str) -> OCDeclareArcLabel {
        OCDeclareArcLabel {
            each: Vec::new(),
            any: vec![ObjectTypeAssociation::new_simple(ot)],
            all: Vec::new(),
        }
    }
    fn all_label(ot: &str) -> OCDeclareArcLabel {
        OCDeclareArcLabel {
            each: Vec::new(),
            any: Vec::new(),
            all: vec![ObjectTypeAssociation::new_simple(ot)],
        }
    }
    fn unique_facts(acts: &[&str], ot: &str) -> HashMap<String, HashMap<String, ActivityObjectFacts>> {
        let mut facts: HashMap<String, HashMap<String, ActivityObjectFacts>> = HashMap::new();
        for act in acts {
            facts.entry((*act).into()).or_default().insert(
                ot.into(),
                ActivityObjectFacts {
                    always_present: true,
                    at_most_one_event_per_object: true,
                },
            );
        }
        facts
    }

    #[test]
    fn derives_as_equivalence_via_anchor_type() {
        // A and B mutually require each other with All(items), items unique per event of both
        // -- A ~_items B, so a negative constraint on B transports to A and vice versa.
        let existing = vec![
            requiring("A", "B", OCDeclareArcType::AS, all_label("items")),
            requiring("B", "A", OCDeclareArcType::AS, all_label("items")),
        ];
        let facts = unique_facts(&["A", "B"], "items");
        let c_ac = arc("A", "C", OCDeclareArcType::AS, any_label("items"));
        let c_bc = arc("B", "C", OCDeclareArcType::AS, any_label("items"));
        let m1 = vec![c_ac.clone(), c_bc.clone()];

        let edges = rule_c_edges(&m1, &existing, &facts);
        assert!(
            edges.get(&c_ac).is_some_and(|s| s.contains(&c_bc))
                || edges.get(&c_bc).is_some_and(|s| s.contains(&c_ac))
        );
    }

    #[test]
    fn does_not_derive_without_a_confirmed_anchor_type() {
        let existing = vec![
            requiring("A", "B", OCDeclareArcType::AS, all_label("items")),
            requiring("B", "A", OCDeclareArcType::AS, all_label("items")),
        ];
        let c_ac = arc("A", "C", OCDeclareArcType::AS, any_label("items"));
        let c_bc = arc("B", "C", OCDeclareArcType::AS, any_label("items"));
        let m1 = vec![c_ac, c_bc];

        let edges = rule_c_edges(&m1, &existing, &HashMap::new());
        assert!(edges.is_empty());
    }
}

/// The object-set equivalences rule C derives from an existence model.
///
/// Each entry is a type set `S` and an unordered pair `A`, `B` with `A ~_S B`. Exposed so the
/// evaluation can check the derived relation against the log it was derived from.
pub fn derived_equivalences(
    existing: &[OCDeclareArc],
    facts: &HashMap<String, HashMap<String, ActivityObjectFacts>>,
) -> Vec<(BTreeSet<String>, String, String)> {
    let premises: Vec<OCDeclareArc> = existing
        .iter()
        .filter(|e| e.counts.0.unwrap_or(0) >= 1)
        .cloned()
        .collect();
    let (eq, _) = direct_pairings(&premises, facts);
    let mut out: Vec<(BTreeSet<String>, String, String)> = eq
        .iter()
        .flat_map(|(key, pairs)| {
            pairs
                .iter()
                .filter(|(a, b)| a < b)
                .map(move |(a, b)| (key.clone(), a.clone(), b.clone()))
        })
        .collect();
    out.sort();
    out.dedup();
    out
}

/// The rewritings rule C licenses, as `(premise, conclusion)` pairs.
pub fn rule_c_rewritings(
    m1: &[OCDeclareArc],
    existing: &[OCDeclareArc],
    facts: &HashMap<String, HashMap<String, ActivityObjectFacts>>,
) -> Vec<(OCDeclareArc, OCDeclareArc)> {
    let mut out: Vec<(OCDeclareArc, OCDeclareArc)> = rule_c_edges(m1, existing, facts)
        .into_iter()
        .flat_map(|(p, cs)| cs.into_iter().map(move |c| (p.clone(), c)))
        .collect();
    out.sort();
    out
}
