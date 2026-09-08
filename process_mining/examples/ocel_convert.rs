//! Convert an OCEL 2.0 log between formats by file extension (json, xml, json.gz, xml.gz).
//!
//! Usage: cargo run --release --example ocel_convert -- <input> <output>

use std::path::PathBuf;

use process_mining::{Exportable, Importable, OCEL};

fn main() {
    let mut args = std::env::args().skip(1);
    let input = PathBuf::from(args.next().expect("input path"));
    let output = PathBuf::from(args.next().expect("output path"));
    let ocel = OCEL::import_from_path(&input).expect("import failed");
    ocel.export_to_path(&output).expect("export failed");
    println!("{} events, {} objects written to {}", ocel.events.len(), ocel.objects.len(), output.display());
}
