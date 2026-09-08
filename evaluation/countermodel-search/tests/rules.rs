//! Machine checks for the source-anchored composition rule's soundness claims,
//! and for the guard side-conditions that make the equivalence-set reduction
//! sound at the model level rather than only for one fixed log.

use oc_declare_reason::*;

const A: ActId = 0;
const B: ActId = 1;

fn any() -> Vec<Option<Level>> {
    vec![Some(Level::Any)]
}

fn bounds() -> Bounds {
    Bounds {
        max_events: 3,
        n_acts: 2,
        n_types: 1,
        objs_per_type: 2,
    }
}

const C: ActId = 2;

fn all() -> Vec<Option<Level>> {
    vec![Some(Level::All)]
}

fn wide() -> Bounds {
    Bounds {
        max_events: 5,
        n_acts: 3,
        n_types: 1,
        objs_per_type: 3,
    }
}

#[test]
fn source_anchored_rule_holds_under_its_side_conditions() {
    // d_r leads from the source of d_n to the source of d_f. Per the
    // arrow-type admissibility table of the source-anchored composition rule,
    // d_f = EF admits d_r in {EP, DP}. Per the involvement admissibility
    // table, oi_f = Any admits oi_r in {All, Each}.
    let d_r = Constraint::existence(Arrow::Ep, A, B, all());
    let d_f = Constraint::negative(Arrow::Ef, B, C, any());
    let d_n = Constraint::negative(Arrow::Ef, A, C, any());
    let out = entails(&[d_r, d_f], &d_n, &[SideCondition::Carries(A, 0)], &wide());
    assert!(
        out.entailed(),
        "source-anchored rule unsound, witness:\n{}",
        out.countermodel.unwrap()
    );
}

#[test]
fn target_anchored_rule_needs_no_source_non_emptiness() {
    // d_r leads from the target of d_n to the target of d_f, and d_f and d_n
    // share their source, so an empty source object set makes both vacuous at
    // the same event. Unlike the source-anchored rule this one therefore
    // needs no non-emptiness condition on the source.
    let d_f = Constraint::negative(Arrow::As, A, B, any());
    let d_r = Constraint::existence(Arrow::Ep, C, B, all());
    let d_n = Constraint::negative(Arrow::As, A, C, any());
    let out = entails(&[d_f, d_r], &d_n, &[], &wide());
    assert!(
        out.entailed(),
        "target-anchored rule unsound without source non-emptiness, witness:\n{}",
        out.countermodel.unwrap()
    );
}

#[test]
fn target_anchored_carry_condition_is_not_exercised() {
    // The target-anchored composition rule requires every target event in
    // scope to carry an object of every Each-involved type of d_r. With
    // oi_r = All that is vacuous, so it is only testable with oi_r = Each,
    // which the target-anchored rule's involvement admissibility table allows
    // against oi_f = Any. If no countermodel exists here, the condition is
    // not exercised at these bounds.
    let d_f = Constraint::negative(Arrow::As, A, B, any());
    let d_r = Constraint::existence(Arrow::Ep, C, B, vec![Some(Level::Each)]);
    let d_n = Constraint::negative(Arrow::As, A, C, any());
    let out = entails(&[d_f, d_r], &d_n, &[], &wide());
    match &out.countermodel {
        Some(cm) => println!("one type: carry condition IS load-bearing, witness:\n{cm}"),
        None => println!("one type: carry condition not exercised at 5 events / 3 objects"),
    }

    // The case the condition is actually about: an Each-involved type of d_r
    // that d_f omits, so it contributes a coordinate to beta that the forbidding
    // constraint says nothing about.
    let two = Bounds {
        max_events: 4,
        n_acts: 3,
        n_types: 2,
        objs_per_type: 2,
    };
    let d_f2 = Constraint::negative(Arrow::As, A, B, vec![Some(Level::Any), None]);
    let d_r2 = Constraint::existence(Arrow::Ep, C, B, vec![Some(Level::All), Some(Level::Each)]);
    let d_n2 = Constraint::negative(Arrow::As, A, C, vec![Some(Level::Any), None]);
    let out2 = entails(&[d_f2, d_r2], &d_n2, &[], &two);
    match &out2.countermodel {
        Some(cm) => println!("two types: carry condition IS load-bearing, witness:\n{cm}"),
        None => println!("two types: carry condition not exercised at 4 events / 2 types"),
    }
}

#[test]
fn thm_lossless_is_false_as_quantified_over_every_ocel() {
    // The equivalence-set reduction condenses these two mutually-derivable
    // arcs into one retained representative and claims the reduced model is
    // satisfied by exactly the same OCELs. That claim is false in general:
    // non-emptiness is a fact about one log, and extending the log can break
    // it.
    let d1 = Constraint::negative(Arrow::As, A, B, any());
    let d2 = Constraint::negative(Arrow::As, B, A, any());

    let bare = entails(std::slice::from_ref(&d1), &d2, &[], &bounds());
    let cm = bare
        .countermodel
        .as_ref()
        .expect("the retained arc must NOT entail the discarded one");
    println!("witness that the reduction is unsound without the side condition:\n{cm}");

    // The theorem is recoverable only relativised to logs where both activities
    // carry every involved type.
    let guarded = entails(
        &[d1],
        &d2,
        &[SideCondition::Carries(A, 0), SideCondition::Carries(B, 0)],
        &bounds(),
    );
    assert!(
        guarded.entailed(),
        "relativised to the side condition it must hold, got:\n{}",
        guarded.countermodel.unwrap()
    );
}

#[test]
fn self_loop_encodes_uniqueness_and_non_emptiness() {
    // (AS, A, A, {u -> Any}, 0, 1) is violated two independent ways, and the
    // equivalence-set reduction's guard side-conditions rely on both being
    // excluded.
    let uniq = Constraint::new(Arrow::As, A, A, any(), 0, 1);

    // (1) The empty-object-set path: an A-event carrying no u-object has F_Any
    // discharge vacuously, so it matches every A-event.
    let free = entails(&[], &uniq, &[], &bounds())
        .countermodel
        .expect("empty-set witness");
    assert!(
        free.events.iter().any(|e| e.act == A && e.objs[0] == 0),
        "expected a witness exploiting the empty object set:\n{free}"
    );

    // (2) With non-emptiness forced, what remains is genuine sharing.
    let carries = entails(&[], &uniq, &[SideCondition::Carries(A, 0)], &bounds())
        .countermodel
        .expect("sharing witness");
    assert!(
        carries.events.iter().filter(|e| e.act == A).count() >= 2,
        "expected two A-events sharing an object:\n{carries}"
    );

    // (3) Both excluded, nothing is left. So the arc asserts uniqueness AND
    // non-emptiness, which is why it discharges both premises the
    // equivalence-set reduction's guard needs.
    let both = entails(
        &[],
        &uniq,
        &[
            SideCondition::Carries(A, 0),
            SideCondition::AtMostOnePerObject(A, 0),
        ],
        &bounds(),
    );
    assert!(
        both.entailed(),
        "guarded on both sides the arc cannot be violated, got:\n{}",
        both.countermodel.unwrap()
    );
}

#[test]
fn self_loop_n_min_one_is_vacuous() {
    // An AS self-loop always matches its own source event, so [1,1] and [0,1]
    // agree. This is why the guard arc must be written [0,1]: [1,1] bounds the
    // count from both above and below, falling outside the one-sided
    // constraints (a lower bound alone, or an upper bound alone) that the
    // source-anchored composition rule covers.
    let zero_one = Constraint::new(Arrow::As, A, A, any(), 0, 1);
    let one_one = Constraint::new(Arrow::As, A, A, any(), 1, u32::MAX);
    let a = entails(std::slice::from_ref(&zero_one), &one_one, &[], &bounds());
    let c = entails(&[one_one], &zero_one, &[], &bounds());
    assert!(
        a.entailed(),
        "[0,1] must give [1,inf), got:\n{}",
        a.countermodel.unwrap()
    );
    assert!(
        !c.entailed(),
        "[1,inf) must NOT give [0,1]; it is the upper bound that bites"
    );
}

#[test]
fn as_self_loop_negative_forces_the_activity_absent() {
    // (AS, A, A, oi, 0, 0) is unsatisfiable whenever an A-event exists, which
    // justifies excluding AS self-loops from the search. It does not justify
    // excluding EF self-loops, which are satisfiable.
    let never = Constraint::negative(Arrow::As, A, A, any());
    let no_a_at_all = Constraint::negative(Arrow::As, B, A, vec![None]);
    let out = entails(&[never], &no_a_at_all, &[], &bounds());
    assert!(
        out.entailed(),
        "an AS self-loop prohibition forces E^A empty:\n{}",
        out.countermodel.unwrap()
    );

    let ef_self = Constraint::negative(Arrow::Ef, A, A, any());
    let sat = entails(&[], &ef_self, &[], &bounds());
    assert!(
        sat.countermodel.is_some(),
        "an EF self-loop prohibition must be violatable, hence meaningful"
    );
}
