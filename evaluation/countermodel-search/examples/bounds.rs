//! Search-space size as a function of the two free bounds, on an entailed query
//! (so the search exhausts rather than exiting early).

use oc_declare_reason::*;
use std::time::Instant;

fn oi(n_types: usize, l: Level) -> Vec<Option<Level>> {
    let mut v = vec![None; n_types];
    v[0] = Some(l);
    v
}

fn main() {
    let n_acts = 3;
    for n_types in [1usize, 2] {
        println!("\n== {n_acts} activities, {n_types} object type(s) ==");
        println!(
            "{:>6} {:>5} {:>16} {:>9} {:>12}",
            "events", "objs", "logs", "secs", "logs/s"
        );
        for objs_per_type in [2u32, 3, 4] {
            for max_events in 3..=9usize {
                let b = Bounds {
                    max_events,
                    n_acts,
                    n_types,
                    objs_per_type,
                };
                let premises = [
                    Constraint::existence(Arrow::Ep, 0, 1, oi(n_types, Level::All)),
                    Constraint::negative(Arrow::Ef, 1, 2, oi(n_types, Level::Any)),
                ];
                let conclusion = Constraint::negative(Arrow::Ef, 0, 2, oi(n_types, Level::Any));
                let side = [SideCondition::Carries(0, 0)];

                let t = Instant::now();
                let out = entails(&premises, &conclusion, &side, &b);
                let secs = t.elapsed().as_secs_f64();
                assert!(out.entailed(), "query must exhaust the space");
                println!(
                    "{max_events:>6} {objs_per_type:>5} {:>16} {secs:>9.2} {:>12.0}",
                    out.logs_checked,
                    out.logs_checked as f64 / secs.max(1e-9)
                );
                if secs > 20.0 {
                    println!("       (stopping this row: over 20s)");
                    break;
                }
            }
        }
    }
}
