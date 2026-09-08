//! How far the bounded search reaches before it stops being usable.

use oc_declare_reason::*;
use std::time::Instant;

fn main() {
    let d_r = Constraint::existence(Arrow::Ep, 0, 1, vec![Some(Level::All), None]);
    let d_f = Constraint::negative(Arrow::Ef, 1, 2, vec![Some(Level::Any), None]);
    let d_n = Constraint::negative(Arrow::Ef, 0, 2, vec![Some(Level::Any), None]);
    let side = [SideCondition::Carries(0, 0)];

    println!(
        "{:>6} {:>6} {:>6} {:>14} {:>10}  verdict",
        "events", "acts", "types", "logs", "secs"
    );
    for (max_events, n_acts, n_types, objs) in [
        (3, 3, 1, 2),
        (4, 3, 1, 2),
        (5, 3, 1, 2),
        (4, 3, 2, 2),
        (5, 3, 2, 2),
        (6, 3, 1, 3),
        (5, 4, 2, 2),
    ] {
        let b = Bounds {
            max_events,
            n_acts,
            n_types,
            objs_per_type: objs,
        };
        let oi = |l: Option<Level>| {
            let mut v = vec![None; n_types];
            v[0] = l;
            v
        };
        let pr = [
            Constraint {
                oi: oi(d_r.oi[0]),
                ..d_r.clone()
            },
            Constraint {
                oi: oi(d_f.oi[0]),
                ..d_f.clone()
            },
        ];
        let cc = Constraint {
            oi: oi(d_n.oi[0]),
            ..d_n.clone()
        };

        let t = Instant::now();
        let out = entails(&pr, &cc, &side, &b);
        let secs = t.elapsed().as_secs_f64();
        println!(
            "{max_events:>6} {n_acts:>6} {n_types:>6} {:>14} {secs:>10.3}  {}",
            out.logs_checked,
            if out.entailed() {
                "entailed"
            } else {
                "countermodel"
            }
        );
    }
}
