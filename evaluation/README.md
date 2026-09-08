# Evaluation

Artifact for the ICPM 2027 paper *Discovery and Reduction of Negative
Object-Centric Declarative Constraints*.

This directory holds the discovered and reduced models the paper reports, the
console output of the runs that produced them, and a script that rebuilds the
tables from those models. The implementation is in the crate itself:

- `process_mining/src/discovery/object_centric/oc_declare/negative/` -- negative
  discovery (`search.rs`, `support.rs`), mixed-model reduction (`reduce.rs`,
  `equiv.rs`), and the quality measures (`quality.rs`).
- `process_mining/src/core/process_models/object_centric/oc_declare/` -- the
  OC-DECLARE model, shared with existence discovery.
- `process_mining/examples/` -- the drivers listed below.

## Build

    cargo build --release --examples -p process_mining

Every command below assumes the repository root as the working directory and
writes its output there unless a flag says otherwise. Instead of the prebuilt
binaries you can use `cargo run --release --example <name> -- <args>`.

## Logs

The paper uses five OCEL 2.0 logs. They are not part of this repository; three
of them ship as test data under `process_mining/test_data/ocel/`.

| Log | File used | Source |
| --- | --- | --- |
| Order Management | `order-management.xml` | OCEL 2.0 standard example log, <https://www.ocel-standard.org/> (Zenodo doi:10.5281/zenodo.8428112) |
| Container Logistics | `ContainerLogistics.xml` | OCEL 2.0 standard example log, <https://www.ocel-standard.org/> (Zenodo doi:10.5281/zenodo.8428084) |
| P2P | `ocel2-p2p.xml` | OCEL 2.0 standard example log, <https://www.ocel-standard.org/> |
| BPIC2017 | `evaluation/data/bpic2017-ocel2.xml.gz` | OCEL 2.0 conversion of the BPI Challenge 2017 log, deposited in this repository; the original is at <https://data.4tu.nl/articles/_/12696884/1> |
| SLURM | `sacct-ocel-all.xml.gz` | Job scheduling on an HPC cluster. Cannot be redistributed. |

Two format notes:

- Use the **`.xml`** form of Order Management. The `.sqlite` form only imports
  when the crate is built with the `ocel-sqlite` feature, and the runs deposited
  here were not.
- BPIC2017 is deposited as `evaluation/data/bpic2017-ocel2.xml.gz` (53 MB),
  which imports directly. The runs deposited here read the same log from its
  `.json` form; `ocel_convert` converts between the OCEL 2.0 formats:

      cargo run --release --example ocel_convert -- <input> <output>

## Settings

Both settings discover the negative model at `rho` in `{0, 0.1, 0.2}` and both
restrict discovery to the arrow types `AS`, `EF`, `EP`, with `All` used for
single-valued object types. They differ only in the existence model that
supplies the composition and rule-C premises:

- **fixed premises** -- the existence model is discovered once at `rho = 0.2`
  and reused at every negative threshold (example `neg_datasets`).
- **matched thresholds** -- the existence model is discovered at the negative
  threshold itself (example `neg_diagonal_models`).

The two coincide at `rho = 0.2`.

## Reproducing the reported numbers

### Table 2, columns `N` and the fixed-premise reduction

    ./target/release/examples/neg_datasets <log> --taus=0,0.1,0.2 --out-dir=OUT

Prints, per threshold, the size of the discovered negative model (column `N`)
and of the reduction under fixed premises (column with the plain arrow), plus
discovery and reduction times. Writes `<stem>-existence.json`,
`<stem>-negative-discovered-tau<TAU>.json` and `<stem>-negative-tau<TAU>.json`.

### Table 2, existence columns and the matched-threshold reduction

    ./target/release/examples/neg_diagonal_models <log> --taus=0,0.1,0.2

Prints one row per threshold with the existence model before and after
transitive reduction (the two `exist.` columns are this row at `rho = 0.2`), the
discovered negative model, its reduction under matched thresholds (column with
the starred arrow), and the size of the combined mixed model. Writes
`<stem>-diag-tau<TAU>-{existence,existence-reduced,negative-discovered,negative}.json`
into the working directory.

The discovered negative model does not depend on the existence model, so the
`negative-discovered` files of the two drivers agree; only one copy is deposited
here.

### Per-stage attribution (Section 6)

    ./target/release/examples/neg_reduction_stages <log> --arrows=AS,EF,EP

Prints, per threshold, how many constraints each stage of the reduction removed
and what each composition rule alone would have condensed away. The paper's
Order Management figures (140 constraints reduced to 9 at `rho = 0`, with 84
removed by condensation, 45 by uniqueness and 2 by orientation) are the
`rho = 0` block of this run. `--arrows` restricts the *existence* model; over
all five arrow types existence discovery does not finish in reasonable time on
SLURM and BPIC2017.

The same numbers are pinned by the unit test
`stage_attribution_on_order_management_at_tau_zero`:

    cargo test --release -p process_mining --lib negative

### Constraints without a case-centric counterpart

    python3 evaluation/summarize.py

Its second table counts, per log and threshold, the retained arcs that involve
two object types or one type as `All`, which no per-type flattening can express.
The per-arc correspondence to *NotCoExistence*, *NotSuccession* and
*NotPrecedence* is checked by

    ./target/release/examples/neg_flat_baseline <log> <reduced-model.json>

### Runtimes

Printed by `neg_datasets` and `neg_diagonal_models`, and recorded in
`results/run-batch.log` and `results/run-order-management.log`.

## Verification drivers

These do not produce table entries; they check the rules against a log or a
bounded instance space.

| Example | Checks |
| --- | --- |
| `neg_carry_check` | The target-anchored composition rule derives nothing that the log violates at the threshold of its premises. |
| `neg_equiv_check` | The derived object-set equivalences hold event for event, and rule C's rewritings do not change how much of the log violates an arc. |
| `neg_antichain_check` | The joint arrow/involvement search returns an antichain. |
| `neg_upclosure_check` | The candidates clearing the threshold are upward closed under the involvement order, which the frontier search's pruning assumes. |
| `neg_rule_b_witnesses` | Prints concrete instances of rule B, negative constraints derived without a negative premise. |
| `negative_candidate_table` | Evaluates the whole candidate space and reports satisfied, testable and total source events per candidate, the reference for the precision measure. |
| `retained_arc_table` | One row per retained arc with its source-event counts, the per-arc confidence and testability the paper quotes. |
| `existence_sizes` | Existence-model size as a function of its own threshold, before and after transitive reduction. |
| `object_multiplicity` | Per activity and object type, whether `All`, `Each` and `Any` are distinguishable at all on the log. |

## Deposited results

`results/<log>/` holds the models, with `<log>` one of `order-management`,
`container-logistics`, `p2p`, `slurm`, `bpic2017`:

| File | Content |
| --- | --- |
| `existence.json` | Existence model at `rho = 0.2`, the fixed premises. |
| `existence-matched-rho<RHO>.json` | Existence model at `rho`. |
| `existence-reduced-rho<RHO>.json` | The same after transitive reduction; at `rho = 0.2` this is the existence half of the reported mixed model. |
| `negative-discovered-rho<RHO>.json` | Discovered negative model at `rho`, before reduction. |
| `negative-reduced-fixed-rho<RHO>.json` | Reduced under fixed premises. |
| `negative-reduced-matched-rho<RHO>.json` | Reduced under matched thresholds. |

Each file is a JSON array of arcs, one object per constraint, with `from`, `to`,
`arc_type`, the involvement `label` split into `each`/`any`/`all`, and the
cardinality bounds `counts` (`[0, 0]` for a negative constraint).

`results/run-batch.log` is the console output of the run over Container
Logistics, P2P, SLURM and BPIC2017; `results/run-order-management.log` is the
Order Management run, including the per-stage attribution. Repeated import
warnings were stripped and absolute paths shortened; the file names in the
`wrote ...` lines are the ones the drivers produced, before they were renamed
into `results/<log>/`.

`summarize.py` rebuilds both tables from these files and takes an optional
results directory as its argument.

## Runtime

The three simulated logs take seconds. SLURM and BPIC2017 take minutes per
threshold: negative discovery grows with `rho`, up to roughly five minutes at
`rho = 0.2` on either log, and existence discovery on BPIC2017 is about a
minute. Plan for around an hour for a full sequential pass over all five logs in
both settings. Peak memory stays within a few GB.
