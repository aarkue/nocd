# Examples

This folder contains example usages of the `process_mining` crate.

## Basic Usage

- **`event_log_stats.rs`**: Imports an XES event log and prints basic statistics (trace count, event count, etc.).
  ```bash
  cargo run --example event_log_stats -- <path_to_log.xes>
  ```

- **`process_discovery.rs`**: Imports an XES event log, discovers a Petri net using the Alpha+++ algorithm, and exports it to PNML.
  ```bash
  cargo run --example process_discovery -- <path_to_log.xes> <output_model.pnml>
  ```

- **`petri_net_import_export.rs`**: Imports a Petri net from PNML, prints stats, and exports it again.
  ```bash
  cargo run --example petri_net_import_export -- <input_model.pnml> <output_model.pnml>
  ```

## Object-Centric Process Mining

- **`ocel_stats.rs`**: Imports an OCEL and prints basic statistics.
  ```bash
  cargo run --example ocel_stats -- <path_to_ocel.xml>
  ```

- **`ocel_csv_export.rs`**: Imports an OCEL and exports it to CSV format.
  ```bash
  cargo run --example ocel_csv_export -- <path_to_ocel.xml> [output.ocel.csv]
  ```

- **`ocel_duckdb_export.rs`**: Imports an OCEL and exports it to a DuckDB database.
  ```bash
  cargo run --example ocel_duckdb_export -- <path_to_ocel.xml>
  ```

- **`ocel_kuzudb_export.rs`**: Imports an OCEL and exports it to a KuzuDB graph database.
  ```bash
  cargo run --example ocel_kuzudb_export -- <path_to_folder_containing_ocel_files>
  ```

## OC-DECLARE

- **`oc_declare.rs`**: Discovers an OC-DECLARE existence model with the default options and reports its size.
  ```bash
  cargo run --release --example oc_declare -- <path_to_ocel>
  ```

- **`oc_declare_evaluation.rs`**: Discovery and reduction timings over a directory of OCEL 2.0 logs.
  ```bash
  cargo run --release --example oc_declare_evaluation -- <directory_of_ocel_logs>
  ```

### Negative constraints (paper artifact)

Drivers for *Discovery and Reduction of Negative Object-Centric Declarative
Constraints*. The commands, the logs they expect and the numbers they reproduce
are documented in [`../../evaluation/README.md`](../../evaluation/README.md).

- **`neg_datasets.rs`**: Discovery and reduction under fixed premises; writes the models and reports counts and timings.
- **`neg_diagonal_models.rs`**: The same under matched thresholds, plus the existence model before and after transitive reduction.
- **`neg_reduction_stages.rs`**: Per-stage removal counts of the reduction pipeline.
- **`neg_flat_baseline.rs`**: How much of a reduced model a flat negative miner on per-type flattenings recovers.
- **`neg_carry_check.rs`**: Checks the target-anchored composition rule against a log.
- **`neg_equiv_check.rs`**: Checks the derived object-set equivalences and rule C's rewritings against a log.
- **`neg_antichain_check.rs`**: Checks that the joint arrow/involvement search returns an antichain.
- **`neg_upclosure_check.rs`**: Checks that the candidates clearing the threshold are upward closed.
- **`neg_rule_b_witnesses.rs`**: Prints concrete instances of rule B.
- **`negative_candidate_table.rs`**: Evaluates the whole candidate space, the reference for the precision measure.
- **`retained_arc_table.rs`**: Per-arc evidence table for a reduced model.
- **`existence_sizes.rs`**: Existence-model size as a function of its own threshold.
- **`object_multiplicity.rs`**: Where `All`, `Each` and `Any` are distinguishable at all on a log.

## Other

- **`schema_census.rs`**: Structural schema discovery over an OCEL 2.0 log (unrelated to the OC-DECLARE work).
  ```bash
  cargo run --release --example schema_census -- <path_to_ocel>
  ```
