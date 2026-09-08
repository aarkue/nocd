//! Re-derivation of the source-anchored composition rule for OC-DECLARE
//! constraints, and ablations showing its side conditions are load-bearing.
//!
//! Activities: A is the source of the derived constraint, B the activity the
//! requiring constraint reaches, C the forbidden one.

use oc_declare_reason::*;

const A: ActId = 0;
const B: ActId = 1;
const C: ActId = 2;

fn bounds() -> Bounds {
    Bounds {
        max_events: 4,
        n_acts: 3,
        n_types: 1,
        objs_per_type: 2,
    }
}

fn all() -> Vec<Option<Level>> {
    vec![Some(Level::All)]
}

fn any() -> Vec<Option<Level>> {
    vec![Some(Level::Any)]
}

#[test]
fn countermodel_is_minimal_in_event_count() {
    let d_r = Constraint::existence(Arrow::Ep, A, B, all());
    let d_f = Constraint::negative(Arrow::Ef, B, C, any());
    let d_n = Constraint::negative(Arrow::Ef, A, C, any());
    let out = entails(&[d_r, d_f], &d_n, &[], &bounds());
    let cm = out.countermodel.expect("a countermodel exists");
    assert_eq!(
        cm.events.len(),
        3,
        "minimal witness is 3 events, got:\n{cm}"
    );
}

#[test]
fn source_anchored_needs_nonempty_source_objects() {
    let d_r = Constraint::existence(Arrow::Ep, A, B, all());
    let d_f = Constraint::negative(Arrow::Ef, B, C, any());
    let d_n = Constraint::negative(Arrow::Ef, A, C, any());

    let without = entails(&[d_r.clone(), d_f.clone()], &d_n, &[], &bounds());
    let cm = without
        .countermodel
        .as_ref()
        .expect("expected an empty-object-set countermodel");
    println!("countermodel without the side condition:\n{cm}");

    let with = entails(
        &[d_r, d_f],
        &d_n,
        &[SideCondition::Carries(A, 0)],
        &bounds(),
    );
    assert!(
        with.entailed(),
        "rule should hold once every source event carries the type, got:\n{}",
        with.countermodel.unwrap()
    );
}

#[test]
fn source_anchored_rejects_inadmissible_arrow() {
    // The arrow-type admissibility table of the source-anchored composition
    // rule admits EP or DP for the requiring constraint when the forbidding
    // one uses EF. EF itself is not admissible.
    let d_r = Constraint::existence(Arrow::Ef, A, B, all());
    let d_f = Constraint::negative(Arrow::Ef, B, C, any());
    let d_n = Constraint::negative(Arrow::Ef, A, C, any());

    let out = entails(
        &[d_r, d_f],
        &d_n,
        &[SideCondition::Carries(A, 0)],
        &bounds(),
    );
    let cm = out
        .countermodel
        .as_ref()
        .expect("EF as the requiring arrow should not compose");
    println!("countermodel for the inadmissible arrow:\n{cm}");
}

#[test]
fn source_anchored_rejects_any_as_requiring_involvement() {
    // The involvement admissibility table of the source-anchored composition
    // rule admits All or Each for the requiring constraint when the
    // forbidding one is at Any. Any itself is not admissible.
    let d_r = Constraint::existence(Arrow::Ep, A, B, any());
    let d_f = Constraint::negative(Arrow::Ef, B, C, any());
    let d_n = Constraint::negative(Arrow::Ef, A, C, any());

    let out = entails(
        &[d_r, d_f],
        &d_n,
        &[SideCondition::Carries(A, 0)],
        &bounds(),
    );
    let cm = out
        .countermodel
        .as_ref()
        .expect("Any as the requiring involvement should not compose");
    println!("countermodel for the inadmissible involvement:\n{cm}");
}

#[test]
fn domination_direction_is_reversed_for_negative_constraints() {
    // For negative constraints, domination runs opposite to positive ones: a
    // weaker involvement entails the stronger one above it, so Any entails
    // All.
    let weaker = Constraint::negative(Arrow::As, A, C, any());
    let stronger = Constraint::negative(Arrow::As, A, C, all());

    let up = entails(std::slice::from_ref(&weaker), &stronger, &[], &bounds());
    assert!(
        up.entailed(),
        "Any should entail All at bound zero, got:\n{}",
        up.countermodel.unwrap()
    );

    let down = entails(&[stronger], &weaker, &[], &bounds());
    assert!(down.countermodel.is_some(), "All must not entail Any");
}

#[test]
fn each_and_any_coincide_at_bound_zero() {
    // At n_max = 0, Each and Any collapse into each other; checked in both
    // directions.
    let each = Constraint::negative(Arrow::As, A, C, vec![Some(Level::Each)]);
    let anyc = Constraint::negative(Arrow::As, A, C, any());

    let a = entails(std::slice::from_ref(&each), &anyc, &[], &bounds());
    let b = entails(&[anyc], &each, &[], &bounds());
    assert!(
        a.entailed() && b.entailed(),
        "Each and Any should be interderivable at n_max = 0"
    );
}
