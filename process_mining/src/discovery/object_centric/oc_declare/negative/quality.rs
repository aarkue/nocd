//! Precision of a negative model against what the log supports.
//!
//! A candidate the log supports but the model does not entail is behaviour the model permits
//! and the log never shows, which is the precision notion. The reference is the candidate
//! table (see [`candidate_table`](super::candidate_table)), so the noise threshold selects only
//! which model was discovered and never what it is measured against.
//!
//! The reference is the *minimal* satisfied candidates, not every point of their up-set:
//! counting up-set points weights by lattice arity and charges one structural gap once per
//! dominated version above it.
//!
//! Entailment is the full rule set, obtained by reusing the reduction rather than
//! reimplementing it -- see [`entailed_by_rules`]. Weakening alone is available as
//! [`entailed_by_weakening`] but must not be used for reported numbers: it scores a reduced
//! model at 0.115 where the full relation scores it 1.000.

use crate::core::{
    event_data::object_centric::linked_ocel::SlimLinkedOCEL,
    process_models::oc_declare::{OCDeclareArc, OCDeclareArcType, OCDeclareNode},
};

use super::table::CandidateRow;

/// How much each candidate counts toward the score.
///
/// These answer different questions and none is canonical, so all three are reported: a rate
/// says how reliably something held, a count says how much evidence there was for it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Weighting {
    /// Every supported candidate counts once. Ignores both reliability and evidence.
    Binary,
    /// Weight by conditional support, so a candidate holding at 99% of its testable source
    /// events counts nearly fully and one holding at 60% counts less.
    Support,
    /// Weight by the absolute number of source events at which the candidate is testable and
    /// holds. Frequent activities dominate; rare ones barely register.
    ///
    /// Equal to `testable * conditional_support`: the chances the constraint had to be
    /// violated, weighted by how reliably it survived them.
    Evidence,
    /// [`Weighting::Evidence`] discounted by the conditional support a second time, i.e.
    /// `satisfying^2 / testable`. Punishes an unreliable constraint harder than the linear
    /// discount does.
    EvidenceConf,
}

impl Weighting {
    fn of(&self, row: &CandidateRow) -> f64 {
        match self {
            Weighting::Binary => 1.0,
            Weighting::Support => row.conditional_support(),
            Weighting::Evidence => row.satisfying as f64,
            Weighting::EvidenceConf => row.satisfying as f64 * row.conditional_support(),
        }
    }
}

/// Whether the model entails this candidate by weakening alone.
///
/// Sound but far from complete: the reduction removes arcs by composition, equivalence,
/// orientation and cardinality entailment as well, so a model reduced by those rules fails to
/// "entail" most of what it actually entails. Measured on order-management, using this alone
/// scores the reduced model at 0.115 against 1.000 for the unreduced one. Use
/// [`entailed_by_rules`] for anything reported.
pub fn entailed_by_weakening(row: &CandidateRow, model: &[OCDeclareArc]) -> bool {
    model.iter().any(|d| {
        d.from.as_str() == row.from
            && d.to.as_str() == row.to
            && d.arc_type.is_dominated_by_or_eq(&row.arc_type)
            && d.label.is_dominated_by(&row.label)
    })
}

/// Whether the model entails this candidate under the full rule set.
///
/// Defined by reusing the reduction rather than reimplementing its rules: the candidate is
/// entailed exactly when adding it to the model leaves it removable, since
/// [`reduce_negative_oc_declare`](super::reduce_negative_oc_declare) drops an arc only when the
/// retained arcs derive it. This cannot drift from the reduction it mirrors, which a separate
/// closure implementation could.
pub fn entailed_by_rules(
    row: &CandidateRow,
    model: &[OCDeclareArc],
    existence: &[OCDeclareArc],
    locel: &SlimLinkedOCEL,
) -> bool {
    let base = super::reduce_negative_oc_declare(locel, existence, model.to_vec());
    entailed_by_rules_with_base(row, model, &base, existence, locel)
}

/// [`entailed_by_rules`] with the model's own reduction supplied by the caller.
///
/// Computing it is the expensive half and it does not depend on the candidate, so a caller
/// scoring many candidates against one model should hoist it out; [`precision`] does.
pub fn entailed_by_rules_with_base(
    row: &CandidateRow,
    model: &[OCDeclareArc],
    base: &[OCDeclareArc],
    existence: &[OCDeclareArc],
    locel: &SlimLinkedOCEL,
) -> bool {
    if entailed_by_weakening(row, model) {
        return true;
    }
    let candidate = OCDeclareArc {
        from: OCDeclareNode::new(row.from.clone()),
        to: OCDeclareNode::new(row.to.clone()),
        arc_type: row.arc_type,
        label: row.label.clone(),
        counts: (Some(0), Some(0)),
    };
    let mut augmented = model.to_vec();
    augmented.push(candidate.clone());
    let reduced = super::reduce_negative_oc_declare(locel, existence, augmented);
    if !reduced.iter().any(|a| *a == candidate) {
        return true;
    }
    // The candidate survived, which is not yet a verdict. Condensation keeps one arbitrary
    // representative per strongly connected component, so when the candidate and a model arc
    // derive each other the representative may be the candidate -- and then a model arc that
    // survived on its own has vanished. That displacement is mutual derivability, hence
    // entailment; without this check the score is deflated by the tie-breaking order.
    base.iter().any(|a| !reduced.contains(a))
}

/// Expand a model to everything it entails, within `universe`.
///
/// The inverse of the reduction: every stage of
/// [`reduce_negative_oc_declare`](super::reduce_negative_oc_declare) run forward to a fixpoint
/// instead of used as a removal test. All eight, not the derivation rules only -- a model
/// reduced by a stage this misses is scored as not entailing what that stage removed, which is
/// what makes a reduced model look worse than the model it came from.
///
/// The stages divide in three:
///
/// * *Premise-free.* Cardinality entailment and rule B/B' remove an arc using log facts alone,
///   with no negative premise. Their inverse adds every such arc of `universe` outright, so the
///   closure of the empty model is already non-empty.
/// * *Derivation.* Source-anchored composition, target-anchored composition and rule C
///   contribute the edges the reduction condenses. Their inverse follows those edges forward.
///   Condensation itself is a removal policy over those edges, not a rule, so it adds nothing
///   here.
/// * *One-for-one.* Within-pair domination and orientation dedup drop an arc that another arc
///   restates. Their inverse adds the restatement: every dominated arc, and the transpose of
///   every arc whose endpoints both carry the involved types.
///
/// Iterating matters. The reduction removes arcs in chains -- it drops `c` because `d` derives
/// it, then drops `d` because `e` does -- and a single pass from the model would never reach
/// `c`, because the edge generators only build edges among arcs present in the set.
///
/// `universe` bounds the search; entailed arcs outside it are not found. Pass at least the
/// reference antichain and the unreduced model.
pub fn closure(
    model: &[OCDeclareArc],
    universe: &[OCDeclareArc],
    existence: &[OCDeclareArc],
    locel: &SlimLinkedOCEL,
) -> Vec<OCDeclareArc> {
    use std::collections::HashSet;

    let facts = crate::core::process_models::oc_declare::get_activity_object_facts(locel);
    let act_ob_inv =
        crate::core::process_models::oc_declare::get_activity_object_involvements(locel);

    let mut all: Vec<OCDeclareArc> = Vec::new();
    let mut seen: HashSet<OCDeclareArc> = HashSet::new();
    for a in universe.iter().chain(model.iter()) {
        if seen.insert(a.clone()) {
            all.push(a.clone());
        }
    }
    // Orientation dedup keeps one of a transposed pair, so the other name has to be in the
    // universe for the closure to be able to reach it.
    for a in all.clone() {
        if super::reduce::is_unoriented(&a, &facts) {
            if let Some(t) = super::reduce::transpose(&a) {
                if seen.insert(t.clone()) {
                    all.push(t);
                }
            }
        }
    }

    // Depends only on `all`, which does not change, so it is built once.
    let edges = super::reduce::merge_edges(vec![
        super::reduce::source_anchored_edges(&all, existence, &facts),
        super::reduce::target_anchored_edges(&all, existence),
        super::equiv::rule_c_edges(&all, existence, &facts),
    ]);

    let mut reached: HashSet<OCDeclareArc> = model.iter().cloned().collect();
    // Premise-free stages: true of the log whether or not the model says anything.
    for c in &all {
        if super::reduce::cardinality_entailed(c, &act_ob_inv, &facts)
            || super::reduce::rule_b_removable(c, existence, &facts)
        {
            reached.insert(c.clone());
        }
    }
    loop {
        let frontier: Vec<OCDeclareArc> = reached.iter().cloned().collect();
        let mut added = false;
        for p in &frontier {
            if let Some(concls) = edges.get(p) {
                for c in concls {
                    added |= reached.insert(c.clone());
                }
            }
            // Orientation dedup, reversed.
            if super::reduce::is_unoriented(p, &facts) {
                if let Some(t) = super::reduce::transpose(p) {
                    if all.contains(&t) {
                        added |= reached.insert(t);
                    }
                }
            }
        }
        // Within-pair domination, reversed: a weaker arc implies every stronger one.
        for c in &all {
            if reached.contains(c) {
                continue;
            }
            let weaker_present = frontier.iter().any(|d| {
                d.from == c.from
                    && d.to == c.to
                    && d.arc_type.is_dominated_by_or_eq(&c.arc_type)
                    && d.label.is_dominated_by(&c.label)
            });
            if weaker_present {
                added |= reached.insert(c.clone());
            }
        }
        if !added {
            break;
        }
    }
    reached.into_iter().collect()
}

/// The minimal satisfied candidates at `tau`, per (activity pair, arrow).
///
/// This is the reference a coverage measure should use. Counting points of the up-set instead
/// weights by lattice arity -- a unit gating five object types contributes up to `3^5` rows
/// against `3` for a single-type unit -- and charges one structural gap once per dominated
/// version above it.
pub fn minimal_satisfied_rows(table: &[CandidateRow], tau: f64) -> Vec<&CandidateRow> {
    let supported: Vec<&CandidateRow> = table
        .iter()
        .filter(|r| r.testable > 0 && r.discovered_at(tau))
        .collect();
    supported
        .iter()
        .filter(|r| {
            !supported.iter().any(|other| {
                other.label != r.label
                    && other.from == r.from
                    && other.to == r.to
                    && other.arc_type == r.arc_type
                    && other.label.is_dominated_by(&r.label)
            })
        })
        .copied()
        .collect()
}

/// Which entailment relation the measure uses.
///
/// The score is only meaningful relative to this choice, so it is explicit rather than
/// hard-wired: `Weakening` is sound but severely incomplete, `Rules` is what the reduction
/// actually removes by. Reported numbers must use `Rules`.
pub enum Entailment<'a> {
    /// Domination only. Cheap, needs no log, and under-reports badly on reduced models.
    Weakening,
    /// One application of the full rule set, by reusing the reduction as a removal test.
    ///
    /// Sound, but one-step: it cannot see a derivation that ran through an arc the reduction
    /// deleted, because the edge generators only build edges among arcs present in the set. On
    /// a reduced model that is exactly the common case. Use [`Entailment::Closure`].
    Rules {
        /// The existence model supplying composition premises.
        existence: &'a [OCDeclareArc],
        /// The log the model was discovered from.
        locel: &'a SlimLinkedOCEL,
    },
    /// Membership in the model's [`closure`]: the inverse of the reduction, iterated.
    ///
    /// This is the relation to report. It is also cheaper than `Rules`, which runs one full
    /// reduction per candidate; this runs one closure per model.
    Closure {
        /// The existence model supplying composition premises.
        existence: &'a [OCDeclareArc],
        /// The log the model was discovered from.
        locel: &'a SlimLinkedOCEL,
        /// Bounds the closure. Pass at least the reference antichain and the unreduced model.
        universe: &'a [OCDeclareArc],
    },
}

impl Entailment<'_> {
    /// The per-model work `holds` would otherwise redo for every candidate. Its meaning
    /// differs per variant: the model's own reduction for `Rules`, its closure for `Closure`.
    fn prepare(&self, model: &[OCDeclareArc]) -> Vec<OCDeclareArc> {
        match self {
            Entailment::Weakening => Vec::new(),
            Entailment::Rules { existence, locel } => {
                super::reduce_negative_oc_declare(locel, existence, model.to_vec())
            }
            Entailment::Closure {
                existence,
                locel,
                universe,
            } => closure(model, universe, existence, locel),
        }
    }

    fn holds(&self, row: &CandidateRow, model: &[OCDeclareArc], base: &[OCDeclareArc]) -> bool {
        match self {
            Entailment::Weakening => entailed_by_weakening(row, model),
            Entailment::Rules { existence, locel } => {
                entailed_by_rules_with_base(row, model, base, existence, locel)
            }
            Entailment::Closure { .. } => {
                let candidate = OCDeclareArc {
                    from: OCDeclareNode::new(row.from.clone()),
                    to: OCDeclareNode::new(row.to.clone()),
                    arc_type: row.arc_type,
                    label: row.label.clone(),
                    counts: (Some(0), Some(0)),
                };
                base.contains(&candidate)
            }
        }
    }
}

/// Result of a precision computation, reported with its denominator so the number can be
/// interpreted rather than just quoted.
#[derive(Debug, Clone)]
pub struct Precision {
    /// The score in `[0,1]`.
    pub value: f64,
    /// Weighted mass of supported candidates the model entails.
    pub covered: f64,
    /// Weighted mass of supported candidates.
    pub total: f64,
    /// Candidates in the denominator.
    pub candidates: usize,
}

/// Precision of `model` against the candidates the log supports at `reference_tau`.
///
/// `reference_tau` is deliberately independent of the threshold the model was discovered at.
/// Passing the model's own threshold makes the reference *be* the model and the score is 1 by
/// construction. Pinning it at 0 is the opposite error: it discards frequency, declaring a
/// constraint that holds at 95% of source events to be unsupported. The references nest
/// (`Sat(0)` is a subset of `Sat(0.1)` is a subset of `Sat(0.2)`), so a loose reference and a
/// strict model give the informative comparison.
///
/// Restricted to testable candidates: a candidate that could never have been violated is
/// satisfied for free, and counting it would penalise the model for not asserting something
/// vacuous.
pub fn precision(
    table: &[CandidateRow],
    model: &[OCDeclareArc],
    reference_tau: f64,
    weighting: Weighting,
    entailment: &Entailment<'_>,
) -> Precision {
    let base = entailment.prepare(model);
    let mut covered = 0.0;
    let mut total = 0.0;
    let mut candidates = 0usize;
    for row in minimal_satisfied_rows(table, reference_tau) {
        let w = weighting.of(row);
        if !w.is_finite() {
            continue;
        }
        total += w;
        candidates += 1;
        if entailment.holds(row, model, &base) {
            covered += w;
        }
    }
    Precision {
        value: if total > 0.0 { covered / total } else { f64::NAN },
        covered,
        total,
        candidates,
    }
}

/// Precision of a model already expanded by [`closure`], where entailment is membership.
///
/// Scored per `(from, to, arc_type)` unit and macro-averaged, rather than as one intersection
/// against the generators. Both choices matter:
///
/// * *Per unit, not globally.* A unit gating five object types has `3^5` candidates against `3`
///   for a single-type unit, so a global count would weight units by lattice arity. Normalising
///   inside a unit removes that.
/// * *Against the whole satisfied set, not its generators.* A model asserting a constraint
///   weaker than the generator still forbids something real and must not score what a model
///   silent on the unit scores. Counting how much of the unit's satisfied set the model entails
///   grades that automatically: the generators cover all of it, a maximally weak constraint
///   covers only itself, silence covers none. No distance metric is needed.
/// Which rows of `table` the model entails, independent of any reference threshold.
///
/// Hoisted out of [`precision_of_closed`] because the entailment test does not depend on
/// `reference_tau`; only which rows are in the reference does.
pub fn covered_rows(table: &[CandidateRow], closed: &[OCDeclareArc]) -> Vec<bool> {
    table
        .iter()
        .map(|row| entailed_by_weakening(row, closed))
        .collect()
}

/// Precision of a model already expanded by [`closure`], scored per
/// `(from, to, arc_type)` unit and macro-averaged.
///
/// Two choices matter. *Per unit, not globally*: a unit gating five object types has `3^5`
/// candidates against `3` for a single-type unit, so a global count would weight units by
/// lattice arity. *Against the whole satisfied set, not its generators*: a model asserting a
/// constraint weaker than the generator still forbids something real and must not score what a
/// model silent on the unit scores, and counting how much of the unit's satisfied set it
/// entails grades that without a distance metric.
pub fn precision_of_closed(
    table: &[CandidateRow],
    closed: &[OCDeclareArc],
    reference_tau: f64,
    weighting: Weighting,
) -> Precision {
    precision_from_coverage(table, &covered_rows(table, closed), reference_tau, weighting)
}

/// [`precision_of_closed`] with the coverage vector supplied by the caller.
pub fn precision_from_coverage(
    table: &[CandidateRow],
    covered: &[bool],
    reference_tau: f64,
    weighting: Weighting,
) -> Precision {
    use std::collections::HashMap;

    // Units are keyed by polarity, so the existence and negative lattices of one activity pair
    // are never averaged into a single fraction: different heights (four levels against three)
    // and opposite entailment directions.
    //
    // The arrow is part of the key only on the negative side. Negative discovery traverses the
    // lattice once per arrow type and reports a frontier for each, so `(s,t,ar)` is a unit it
    // can actually fill. Existence discovery reports the strictly-preferred constraint per
    // activity *pair* across arrows, so keying its units by arrow would score the two arrows it
    // did not report at zero and cap the measure near `1/3` for reasons that have nothing to do
    // with the model.
    let mut units: HashMap<(&str, &str, Option<OCDeclareArcType>, bool), (f64, f64)> =
        HashMap::new();
    let mut candidates = 0usize;
    for (row, &is_covered) in table.iter().zip(covered.iter()) {
        // `Cons_L` requires at least one involved object type, so the involvement-free
        // candidate is not in the space.
        let involved = row.label.each.len() + row.label.any.len() + row.label.all.len();
        if involved == 0 || row.testable == 0 || !row.discovered_at(reference_tau) {
            continue;
        }
        let w = weighting.of(row);
        if !w.is_finite() {
            continue;
        }
        candidates += 1;
        let entry = units
            .entry((
                row.from.as_str(),
                row.to.as_str(),
                row.is_negative().then_some(row.arc_type),
                row.is_negative(),
            ))
            .or_insert((0.0, 0.0));
        entry.1 += w;
        if is_covered {
            entry.0 += w;
        }
    }
    let mut covered_sum = 0.0;
    let mut total = 0.0;
    for (c, t) in units.values() {
        if *t > 0.0 {
            covered_sum += c / t;
            total += 1.0;
        }
    }
    Precision {
        value: if total > 0.0 { covered_sum / total } else { f64::NAN },
        covered: covered_sum,
        total,
        candidates,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::core::{
        event_data::object_centric::{
            appendable::AppendableOCEL, linked_ocel::SlimLinkedOCEL, OCELRelationship, OCELType,
        },
        process_models::oc_declare::{
            OCDeclareArcLabel, OCDeclareArcType, OCDeclareNode, ObjectTypeAssociation,
        },
    };
    use super::super::table::candidate_table;
    use super::super::{discover_negative_oc_declare, NegativeOCDeclareDiscoveryOptions};
    use chrono::DateTime;

    use OCDeclareArcType::{AS, EF};

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

    fn mk_label(any: &[&str], all: &[&str]) -> OCDeclareArcLabel {
        let mut any: Vec<_> = any
            .iter()
            .map(|s| ObjectTypeAssociation::new_simple(*s))
            .collect();
        let mut all: Vec<_> = all
            .iter()
            .map(|s| ObjectTypeAssociation::new_simple(*s))
            .collect();
        any.sort();
        all.sort();
        OCDeclareArcLabel {
            each: Vec::new(),
            any,
            all,
        }
    }

    fn mk_arc(from: &str, to: &str, arc_type: OCDeclareArcType, label: OCDeclareArcLabel) -> OCDeclareArc {
        OCDeclareArc {
            from: OCDeclareNode::new(from),
            to: OCDeclareNode::new(to),
            arc_type,
            label,
            counts: (Some(0), Some(0)),
        }
    }

    fn mk_row(
        from: &str,
        to: &str,
        arc_type: OCDeclareArcType,
        label: OCDeclareArcLabel,
        satisfying: usize,
        testable: usize,
        total: usize,
    ) -> CandidateRow {
        CandidateRow {
            from: from.into(),
            to: to.into(),
            arc_type,
            label,
            satisfying,
            testable,
            total,
            counts: (Some(0), Some(0)),
        }
    }

    /// Two `a`-events each carry both `i1` and `i2`; `b1` carries `i1` only, `b2` carries
    /// `i3`,`i4`. So `Any(items)` is *violated* on `a -/-> b` (`b1` shares `i1`) while
    /// `All(items)` holds (no `b`-event carries both `i1` and `i2`) -- the log itself shows
    /// the weaker involvement is the stronger negative statement. `b2` exists so that
    /// `All(items)` is testable at all (a `b`-event can carry two items).
    fn sample_locel() -> SlimLinkedOCEL {
        let mut s = SlimLinkedOCEL::new();
        s.declare_event_type(empty_type("a")).unwrap();
        s.declare_event_type(empty_type("b")).unwrap();
        s.declare_object_type(empty_type("items")).unwrap();
        s.declare_object_type(empty_type("orders")).unwrap();
        for id in ["i1", "i2", "i3", "i4"] {
            s.append_object(id.into(), "items", Vec::new(), Vec::new())
                .unwrap();
        }
        for id in ["o1", "o2"] {
            s.append_object(id.into(), "orders", Vec::new(), Vec::new())
                .unwrap();
        }
        let t = |i: u32| DateTime::parse_from_rfc3339(&format!("2024-01-0{i}T00:00:00Z")).unwrap();
        s.append_event(
            "a1".into(),
            "a",
            t(1),
            Vec::new(),
            vec![rel("i1"), rel("i2"), rel("o1")],
        )
        .unwrap();
        s.append_event(
            "a2".into(),
            "a",
            t(2),
            Vec::new(),
            vec![rel("i1"), rel("i2"), rel("o1")],
        )
        .unwrap();
        s.append_event("b1".into(), "b", t(3), Vec::new(), vec![rel("i1"), rel("o2")])
            .unwrap();
        s.append_event(
            "b2".into(),
            "b",
            t(4),
            Vec::new(),
            vec![rel("i3"), rel("i4"), rel("o2")],
        )
        .unwrap();
        s.finalize().unwrap();
        s
    }

    fn opts(tau: f64) -> NegativeOCDeclareDiscoveryOptions {
        NegativeOCDeclareDiscoveryOptions {
            noise_threshold: tau,
            ..Default::default()
        }
    }

    fn find<'a>(
        table: &'a [CandidateRow],
        from: &str,
        to: &str,
        arc_type: OCDeclareArcType,
        label: &OCDeclareArcLabel,
    ) -> &'a CandidateRow {
        table
            .iter()
            .find(|r| {
                r.from == from && r.to == to && r.arc_type == arc_type && &r.label == label
            })
            .unwrap_or_else(|| {
                panic!(
                    "no candidate row {from} -/-> {to} [{}] {}",
                    arc_type.get_name(),
                    label.as_template_string()
                )
            })
    }

    /// The empty model entails nothing, so every supported testable candidate is uncovered.
    #[test]
    fn empty_model_has_zero_precision() {
        let locel = sample_locel();
        let table = candidate_table(&locel, &opts(0.0));
        let p = precision(&table, &[], 0.0, Weighting::Binary, &Entailment::Weakening);
        assert!(
            p.candidates >= 1,
            "fixture must supply at least one supported testable candidate, got {p:?}"
        );
        assert_eq!(p.covered, 0.0);
        assert_eq!(p.value, 0.0, "{p:?}");
    }

    /// At `tau = 0` the discovered frontier is exactly the set of `<=`-minimal satisfied
    /// candidates, and satisfaction is upward closed, so weakening alone must cover every
    /// supported testable candidate.
    #[test]
    fn minimal_satisfied_model_is_fully_precise_at_tau_zero() {
        let locel = sample_locel();
        let table = candidate_table(&locel, &opts(0.0));
        let model = discover_negative_oc_declare(&locel, opts(0.0));
        assert!(!model.is_empty(), "fixture must discover something");
        let p = precision(&table, &model, 0.0, Weighting::Binary, &Entailment::Weakening);
        let uncovered: Vec<String> = table
            .iter()
            .filter(|r| r.testable > 0 && r.discovered_at(0.0) && !entailed_by_weakening(r, &model))
            .map(|r| {
                format!(
                    "{} -/-> {} [{}] {}",
                    r.from,
                    r.to,
                    r.arc_type.get_name(),
                    r.label.as_template_string()
                )
            })
            .collect();
        assert_eq!(p.value, 1.0, "uncovered: {uncovered:?} ({p:?})");
    }

    /// Adding an arc can only add entailed candidates; the denominator never moves. Checked
    /// over every prefix of the discovered model, and asserted non-vacuous (the full model is
    /// strictly better than the one-arc model).
    #[test]
    fn precision_is_monotone_in_the_model() {
        let locel = sample_locel();
        let model = discover_negative_oc_declare(&locel, opts(0.0));
        assert!(model.len() >= 2, "need a proper superset to test with");
        for tau in [0.0, 0.25, 1.0] {
            let table = candidate_table(&locel, &opts(tau));
            for weighting in [Weighting::Binary, Weighting::Support, Weighting::Evidence] {
                let values: Vec<f64> = (0..=model.len())
                    .map(|k| precision(&table, &model[..k], tau, weighting, &Entailment::Weakening).value)
                    .collect();
                for k in 1..values.len() {
                    assert!(
                        values[k] >= values[k - 1] - 1e-12,
                        "precision dropped from {} to {} adding arc {k} (tau={tau}, {weighting:?})",
                        values[k - 1],
                        values[k]
                    );
                }
                assert!(
                    values[model.len()] > values[1] + 1e-12,
                    "monotonicity check is vacuous at tau={tau} {weighting:?}: {values:?}"
                );
            }
        }
    }

    /// Reversed Domination, grounded in the log rather than in `is_dominated_by`: on this
    /// fixture `Any(items)` is violated everywhere and `All(items)` holds everywhere, so
    /// `Any` is the *stronger* negative constraint. Entailment must therefore run from the
    /// weaker involvement (`Any`) to the stronger one (`All`), never the other way.
    #[test]
    fn entailment_runs_from_weaker_to_stronger_involvement() {
        let locel = sample_locel();
        let table = candidate_table(&locel, &opts(0.0));
        let any_label = mk_label(&["items"], &[]);
        let all_label = mk_label(&[], &["items"]);
        let any_row = find(&table, "a", "b", AS, &any_label);
        let all_row = find(&table, "a", "b", AS, &all_label);
        assert_eq!(
            (any_row.satisfying, any_row.testable),
            (0, 2),
            "Any(items) should be violated at both a-events (b1 shares i1)"
        );
        assert_eq!(
            (all_row.satisfying, all_row.testable),
            (2, 2),
            "All(items) should hold at both a-events and be testable via b2"
        );

        let any_arc = mk_arc("a", "b", AS, any_label.clone());
        let all_arc = mk_arc("a", "b", AS, all_label.clone());
        assert!(
            entailed_by_weakening(all_row, std::slice::from_ref(&any_arc)),
            "a negative arc at Any(items) must entail the All(items) candidate"
        );
        assert!(
            !entailed_by_weakening(any_row, std::slice::from_ref(&all_arc)),
            "a negative arc at All(items) must NOT entail the Any(items) candidate \
             (domination is reversed for negative constraints)"
        );

        // reflexive, and the empty label is the weakest involvement of all
        assert!(entailed_by_weakening(any_row, std::slice::from_ref(&any_arc)));
        assert!(entailed_by_weakening(all_row, std::slice::from_ref(&all_arc)));
        let nothing = mk_arc("a", "b", AS, mk_label(&[], &[]));
        assert!(entailed_by_weakening(any_row, std::slice::from_ref(&nothing)));
        assert!(entailed_by_weakening(all_row, std::slice::from_ref(&nothing)));
        let nothing_row = mk_row("a", "b", AS, mk_label(&[], &[]), 1, 1, 1);
        assert!(
            !entailed_by_weakening(&nothing_row, std::slice::from_ref(&any_arc)),
            "Any(items) must not entail the unlabelled candidate"
        );

        // same reversal on the arrow order: AS is the weakest arrow
        let ef_row = mk_row("a", "b", EF, any_label.clone(), 1, 1, 1);
        let as_row = mk_row("a", "b", AS, any_label.clone(), 1, 1, 1);
        let ef_arc = mk_arc("a", "b", EF, any_label.clone());
        assert!(entailed_by_weakening(&ef_row, std::slice::from_ref(&any_arc)));
        assert!(!entailed_by_weakening(&as_row, std::slice::from_ref(&ef_arc)));

        // endpoints must match
        let other_pair = mk_arc("a", "c", AS, mk_label(&[], &[]));
        assert!(!entailed_by_weakening(any_row, std::slice::from_ref(&other_pair)));
    }

    /// With conditional support 1.0 everywhere and a uniform evidence count, the three
    /// weightings are the same number.
    #[test]
    fn weightings_agree_when_support_is_one_everywhere() {
        let l = mk_label(&[], &[]);
        let table = vec![
            mk_row("a", "b1", AS, l.clone(), 3, 3, 3),
            mk_row("a", "b2", AS, l.clone(), 3, 3, 3),
            mk_row("a", "b3", AS, l.clone(), 3, 3, 5),
            mk_row("a", "b4", AS, l.clone(), 3, 3, 4),
        ];
        let model = vec![mk_arc("a", "b1", AS, l.clone()), mk_arc("a", "b2", AS, l)];
        let locel = sample_locel();
        let values: Vec<f64> = [Weighting::Binary, Weighting::Support, Weighting::Evidence]
            .into_iter()
            .map(|w| precision(&table, &model, 0.0, w, &Entailment::Weakening).value)
            .collect();
        for v in &values {
            assert!((v - 0.5).abs() < 1e-12, "expected 0.5 everywhere, got {values:?}");
        }
    }

    /// When conditional support varies and the evidence counts are lopsided, the three
    /// weightings answer three different questions and give three different numbers.
    #[test]
    fn weightings_disagree_when_support_varies() {
        let l = mk_label(&[], &[]);
        let table = vec![
            // covered, huge evidence, fully supported
            mk_row("a", "b1", AS, l.clone(), 10, 10, 10),
            // uncovered, half supported
            mk_row("a", "b2", AS, l.clone(), 1, 2, 2),
            // uncovered, fully supported but barely any evidence
            mk_row("a", "b3", AS, l.clone(), 1, 1, 1),
        ];
        let model = vec![mk_arc("a", "b1", AS, l)];
        // tau = 0.5 so that the half-supported candidate is in the denominator at all
        let locel = sample_locel();
        let binary = precision(&table, &model, 0.5, Weighting::Binary, &Entailment::Weakening);
        let support = precision(&table, &model, 0.5, Weighting::Support, &Entailment::Weakening);
        let evidence = precision(&table, &model, 0.5, Weighting::Evidence, &Entailment::Weakening);
        assert_eq!(binary.candidates, 3);
        assert_eq!(support.candidates, 3);
        assert_eq!(evidence.candidates, 3);
        assert!((binary.value - 1.0 / 3.0).abs() < 1e-12, "{binary:?}");
        assert!((support.value - 1.0 / 2.5).abs() < 1e-12, "{support:?}");
        assert!((evidence.value - 10.0 / 12.0).abs() < 1e-12, "{evidence:?}");
        assert!(binary.value < support.value && support.value < evidence.value);
    }
}
