# oc-declare-reason

Bounded countermodel search for entailment between OC-DECLARE constraints.

This crate is part of the artifact for the ICPM 2027 paper "Discovery and
Reduction of Negative Object-Centric Declarative Constraints". Given a set of
premise constraints and a conclusion constraint, it searches for a
countermodel: a log, up to a bounded number of events and objects, that
satisfies every premise while violating the conclusion. If none is found up
to the bound, that is evidence (not a proof) that the premises entail the
conclusion. A found countermodel is minimal in event count, since the search
runs iterative deepening over the event bound.

It is used to check the admissibility conditions of the paper's
source-anchored composition rule for negative OC-DECLARE constraints, by
exhaustively re-deriving every case of the rule's admissibility tables with
the search rather than by hand.

## Model

An OC-DECLARE constraint (`Constraint`) is:

- an arrow: `As` (a-succession, same event), `Ef` (eventually-follows, strictly
  later), or `Ep` (eventually-precedes, strictly earlier);
- a source and a target activity;
- an object involvement per type (`oi`): `None` (omitted), or `Some(Level)`
  with `Level::All`, `Level::Each`, or `Level::Any`;
- a cardinality range `[n_min, n_max]`. `Constraint::existence` is
  `[1, INF]`, `Constraint::negative` is `[0, 0]`.

A `MicroLog` is a totally ordered sequence of events; each event has an
activity and, per object type, a bitmask (`ObjSet`) of the objects it carries.
Object ids within a type are interchangeable, so the search only needs one
representative log per isomorphism class of object assignment.

Satisfaction (`holds`, `holds_at`) collects the target events in the arrow's
temporal scope, filters them by object involvement, and requires the match
count to lie within `[n_min, n_max]` for every object assignment ranging over
the Each-involved types.

Some facts used by the composition rule are properties of a whole log rather
than of a single event, so they are supplied to the search as
`SideCondition`s rather than derived automatically:

- `Carries(activity, type)`: every event of the activity carries at least one
  object of the type.
- `AtMostOnePerObject(activity, type)`: each object of the type occurs in at
  most one event of the activity. Combined with `Carries` on the same pair,
  this makes an AS self-loop constraint on that pair equivalent to per-object
  uniqueness, which is the guard side-condition behind the paper's
  equivalence-set reduction.

## Running the tests

```
cargo test --release
```

`tests/rules.rs` and `tests/composition.rs` re-derive the source-anchored and
target-anchored composition rules, check that their side conditions are
load-bearing (removing one produces a countermodel), and check the properties
behind the equivalence-set reduction's guard side-conditions.

## Running the examples

```
cargo run --release --example sweep
cargo run --release --example bounds
cargo run --release --example scaling
```

### sweep

Exhaustively checks every combination of forbidding arrow, requiring arrow,
forbidding involvement (omitted, Any, All), and requiring involvement
(omitted, Any, Each, All) for the source-anchored composition rule: 3 x 3 x 3
x 4 = 108 cells. For each cell it compares the admissibility predicted by the
rule's arrow-type and involvement admissibility tables against what the
search finds at a bound of 5 events and 3 objects per type, printing any
disagreements first and the full table after. Of the 108 cells, 30 are
predicted (and found) admissible and 78 excluded, each excluded cell backed
by a minimal countermodel. The last line of output is `agree 108, disagree
0`, meaning the search matches the tables' predicted verdict on every cell.
These tables are the paper's Figure 2 admissibility conditions for the
source-anchored composition rule.

The bound of 5 events is what the paper calls the countermodel search over
logs of at most five events.

### bounds

Measures how the search space (logs checked, wall time, logs per second)
grows as the two free bounds, `max_events` and `objs_per_type`, increase, for
a query known to be entailed so the search must exhaust the whole space
rather than stopping early at a found countermodel. `max_events` bounds the
log length; `objs_per_type` bounds how many distinct objects of a type the
search considers before it can assume isomorphism to an already-seen
assignment.

### scaling

Measures how far the bounded search can be pushed in practice before runtime
becomes unusable, varying `max_events`, `n_acts`, `n_types`, and
`objs_per_type` together on a fixed composition-rule query.

## License

Dual licensed under MIT OR Apache-2.0. See `LICENSE-MIT` and
`LICENSE-APACHE`.
