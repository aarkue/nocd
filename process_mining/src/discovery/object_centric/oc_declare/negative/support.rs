//! Conditional support: satisfied / testable, where a source event counts toward the
//! denominator only if some target event in scope could possibly match on cardinality
//! grounds.
use std::collections::HashMap;

use chrono::{DateTime, FixedOffset};

use crate::conformance::object_centric::oc_declare::event_violates;
use crate::core::{
    event_data::object_centric::linked_ocel::{
        e2o_rev_type_index::E2ORevByTypeIndex, slim_linked_ocel::EventIndex, SlimLinkedOCEL,
    },
    process_models::oc_declare::{EventOrSynthetic, OCDeclareArcLabel, OCDeclareArcType},
};

use super::base_type_name;

/// Per-activity events sorted ascending by time, with prefix/suffix max object-count
/// arrays per object type — the cheap testability check in [`evaluate`].
pub(crate) struct TestabilityIndex {
    events: HashMap<String, Vec<EventIndex>>,
    bounds: HashMap<(String, String), (Vec<usize>, Vec<usize>)>,
}

impl TestabilityIndex {
    pub(crate) fn build(locel: &SlimLinkedOCEL, acts: &[String], types: &[String]) -> Self {
        let mut events: HashMap<String, Vec<EventIndex>> = HashMap::new();
        for act in acts {
            let mut evs: Vec<EventIndex> = locel.get_evs_of_type(act).copied().collect();
            evs.sort_by_key(|e| *e.get_time(locel));
            events.insert(act.clone(), evs);
        }
        let mut bounds = HashMap::new();
        for act in acts {
            let evs = &events[act];
            for ot in types {
                let counts: Vec<usize> = evs
                    .iter()
                    .map(|ev| {
                        // an object can appear more than once per event via distinct
                        // qualifiers; count unique objects, not raw relationships
                        ev.get_e2o(locel)
                            .filter(|o| o.get_ob_type(locel) == ot)
                            .collect::<std::collections::HashSet<_>>()
                            .len()
                    })
                    .collect();
                if counts.iter().all(|&c| c == 0) {
                    continue;
                }
                let mut prefix = vec![0usize; counts.len() + 1];
                for (i, &c) in counts.iter().enumerate() {
                    prefix[i + 1] = prefix[i].max(c);
                }
                let mut suffix = vec![0usize; counts.len() + 1];
                for i in (0..counts.len()).rev() {
                    suffix[i] = suffix[i + 1].max(counts[i]);
                }
                bounds.insert((act.clone(), ot.clone()), (prefix, suffix));
            }
        }
        Self { events, bounds }
    }

    /// Max `|obj_ot|` over target events in scope, `None` if the scope is empty or the
    /// type is never carried there at all.
    fn max_in_scope(
        &self,
        activity: &str,
        ot: &str,
        time: DateTime<FixedOffset>,
        arc_type: OCDeclareArcType,
        locel: &SlimLinkedOCEL,
    ) -> Option<usize> {
        let evs = self.events.get(activity)?;
        let (lo, hi) = match arc_type {
            OCDeclareArcType::AS => (0, evs.len()),
            OCDeclareArcType::EF => (
                evs.partition_point(|e| *e.get_time(locel) <= time),
                evs.len(),
            ),
            OCDeclareArcType::EP => (0, evs.partition_point(|e| *e.get_time(locel) < time)),
            OCDeclareArcType::DF | OCDeclareArcType::DP => {
                unreachable!("negative discovery never searches DF/DP")
            }
        };
        if lo >= hi {
            return None;
        }
        let (prefix, suffix) = self.bounds.get(&(activity.to_string(), ot.to_string()))?;
        Some(match arc_type {
            OCDeclareArcType::EF => suffix[lo],
            _ => prefix[hi],
        })
    }
}

/// Whether the candidate clears `1 - noise_threshold` **plain** support, deciding as early as
/// possible, and whether any source event was testable at all.
///
/// Returns `(clears, any_testable)`.
///
/// The threshold is on plain support because conditional support is not monotone in the
/// involvement order: strengthening an involvement shrinks the testable set as well as raising
/// the satisfied count, so the ratio can fall and the clearing set stops being upward closed.
/// Measured on order management, 648 dominated pairs invert at `rho = 0.2`. Plain support keeps
/// the denominator fixed, so the clearing set is upward closed and the frontier search's
/// pruning is sound. Testability is reported alongside and applied as a filter afterwards.
///
/// Discovery needs the verdict, not the counts. [`evaluate`] returns exact counts by scanning
/// every source event serially, which is fine for the candidate table on a small log but is
/// the wrong shape for discovery on a log with hundreds of thousands of source events per
/// activity: this scans in parallel and stops once the violating tally settles the outcome.
pub(crate) fn clears_threshold(
    from_act: &str,
    to_act: &str,
    label: &OCDeclareArcLabel,
    arc_type: OCDeclareArcType,
    noise_threshold: f64,
    locel: &SlimLinkedOCEL,
    index: &E2ORevByTypeIndex,
    testability: &TestabilityIndex,
) -> (bool, bool) {
    use rayon::prelude::*;
    use std::sync::atomic::{AtomicUsize, Ordering};

    let from_evs = EventOrSynthetic::get_all_syn_evs(locel, from_act);
    let total = from_evs.len();
    let view = index.for_ev_type(to_act);
    // More than this many violations can never clear the threshold, whatever the rest do.
    let max_violations = (noise_threshold * total as f64).floor() as usize;
    let violations = AtomicUsize::new(0);
    let satisfied = AtomicUsize::new(0);
    let testable = AtomicUsize::new(0);
    from_evs
        .par_iter()
        .map(|ev| {
            // Satisfaction is counted over every source event: that is plain support.
            if event_violates(ev, label, to_act, &arc_type, &(Some(0), Some(0)), locel, view) {
                violations.fetch_add(1, Ordering::Relaxed);
            } else {
                satisfied.fetch_add(1, Ordering::Relaxed);
            }
            // Testability is tracked separately, for the filter that runs after the search.
            let time = ev.get_timestamp(locel);
            for ot in label.any.iter().chain(label.all.iter()) {
                let objs: std::collections::HashSet<_> =
                    ot.get_for_ev(ev, locel).into_iter().collect();
                if objs.is_empty() {
                    continue;
                }
                let need = if label.all.contains(ot) { objs.len() } else { 1 };
                let ok = testability
                    .max_in_scope(to_act, base_type_name(ot), time, arc_type, locel)
                    .is_some_and(|max| max >= need);
                if !ok {
                    return;
                }
            }
            testable.fetch_add(1, Ordering::Relaxed);
        })
        .take_any_while(|_| violations.load(Ordering::Relaxed) <= max_violations)
        .for_each(|_| {});

    // On an early exit both tallies are incomplete, but the exit condition is that violations
    // already exceed what the threshold tolerates, so `clears` is false either way.
    let sat = satisfied.into_inner();
    let clears = total >= 1 && sat as f64 >= (1.0 - noise_threshold) * total as f64;
    (clears, testable.into_inner() >= 1)
}

/// `(satisfied_among_testable, testable, total_source_events)` for one candidate.
pub(crate) fn evaluate(
    from_act: &str,
    to_act: &str,
    label: &OCDeclareArcLabel,
    arc_type: OCDeclareArcType,
    locel: &SlimLinkedOCEL,
    index: &E2ORevByTypeIndex,
    testability: &TestabilityIndex,
) -> (usize, usize, usize) {
    let from_evs = EventOrSynthetic::get_all_syn_evs(locel, from_act);
    let total = from_evs.len();
    let view = index.for_ev_type(to_act);
    let mut satisfied = 0;
    let mut testable = 0;
    for ev in &from_evs {
        let time = ev.get_timestamp(locel);
        let mut possible = true;
        for ot in label.any.iter().chain(label.all.iter()) {
            // an object can appear more than once per event via distinct qualifiers;
            // dedupe before counting, same reasoning as TestabilityIndex::build
            let objs: std::collections::HashSet<_> = ot.get_for_ev(ev, locel).into_iter().collect();
            if objs.is_empty() {
                continue;
            }
            let need = if label.all.contains(ot) { objs.len() } else { 1 };
            let ok = testability
                .max_in_scope(to_act, base_type_name(ot), time, arc_type, locel)
                .is_some_and(|max| max >= need);
            if !ok {
                possible = false;
                break;
            }
        }
        if !possible {
            continue;
        }
        testable += 1;
        if !event_violates(ev, label, to_act, &arc_type, &(Some(0), Some(0)), locel, view) {
            satisfied += 1;
        }
    }
    (satisfied, testable, total)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::core::{
        event_data::object_centric::{
            appendable::AppendableOCEL, linked_ocel::e2o_rev_type_index::E2ORevByTypeIndex,
            OCELRelationship, OCELType,
        },
        process_models::oc_declare::{OCDeclareArcLabel, OCDeclareArcType, ObjectTypeAssociation},
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

    /// `a1` needs `All(items)` to match against 2 items; the only `b` event ever carries at
    /// most 1, so no match is cardinality-possible for `a1` — untestable. `a2` needs only 1,
    /// which `b1` could carry (and doesn't) — testable and satisfied.
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
        s.append_event("a1".into(), "a", t(1), Vec::new(), vec![rel("i1"), rel("i2")])
            .unwrap();
        s.append_event("a2".into(), "a", t(2), Vec::new(), vec![rel("i3")])
            .unwrap();
        s.append_event("b1".into(), "b", t(3), Vec::new(), vec![rel("i1")])
            .unwrap();
        s.finalize().unwrap();
        s
    }

    #[test]
    fn cardinality_impossible_source_event_is_untestable() {
        let locel = sample_locel();
        let index = E2ORevByTypeIndex::build(&locel);
        let acts = vec!["a".to_string(), "b".to_string()];
        let types = vec!["items".to_string()];
        let testability = TestabilityIndex::build(&locel, &acts, &types);
        let label = OCDeclareArcLabel {
            each: Vec::new(),
            any: Vec::new(),
            all: vec![ObjectTypeAssociation::new_simple("items")],
        };
        let (sat, testable, total) =
            evaluate("a", "b", &label, OCDeclareArcType::AS, &locel, &index, &testability);
        assert_eq!(total, 2);
        assert_eq!(testable, 1); // a1 needs 2 items, b's max is 1 -- impossible
        assert_eq!(sat, 1); // a2 needs 1, b1={i1} doesn't contain i3 -- testable, satisfied
    }

    /// End-to-end wiring check: `discover_negative_oc_declare` should find `All(items)` as
    /// the minimal satisfied `AS a -/-> b` arc on this fixture (`Any(items)` still matches
    /// via `a1`, `All(items)` doesn't), and the conditional-support prune must not reject it.
    #[test]
    fn discover_negative_oc_declare_finds_the_minimal_arc() {
        use crate::discovery::object_centric::oc_declare::negative::{
            discover_negative_oc_declare, NegativeOCDeclareDiscoveryOptions,
        };
        let locel = sample_locel();
        let opts = NegativeOCDeclareDiscoveryOptions {
            noise_threshold: 0.0,
            ..Default::default()
        };
        let result = discover_negative_oc_declare(&locel, opts);
        assert!(result.iter().any(|c| c.from.as_str() == "a"
            && c.to.as_str() == "b"
            && c.arc_type == OCDeclareArcType::AS
            && c.label.all == vec![ObjectTypeAssociation::new_simple("items")]));
    }
}
