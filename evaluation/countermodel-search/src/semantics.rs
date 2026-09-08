//! Satisfaction of an OC-DECLARE constraint: collect the target events in the
//! arrow's temporal scope, filter them by object involvement, and require the
//! count to lie within the bounds for *every* object assignment.

use crate::model::*;

fn in_scope(arrow: Arrow, i: usize, j: usize) -> bool {
    match arrow {
        Arrow::As => true,
        Arrow::Ef => j > i,
        Arrow::Ep => j < i,
    }
}

/// Object assignments for the Each-involved types the source event actually
/// carries. A type the source does not carry drops out of the quantifier.
pub fn assignments(d: &Constraint, e: &Event) -> Vec<Vec<(TypeId, u32)>> {
    let mut out = vec![Vec::new()];
    for (t, lvl) in d.oi.iter().enumerate() {
        if *lvl != Some(Level::Each) || e.objs[t] == 0 {
            continue;
        }
        let mut next = Vec::new();
        for o in 0..32u32 {
            if e.objs[t] & (1 << o) == 0 {
                continue;
            }
            for base in &out {
                let mut b = base.clone();
                b.push((t, o));
                next.push(b);
            }
        }
        out = next;
    }
    out
}

fn passes(d: &Constraint, e: &Event, ep: &Event, beta: &[(TypeId, u32)]) -> bool {
    for (t, o) in beta {
        if ep.objs[*t] & (1 << o) == 0 {
            return false;
        }
    }
    for (t, lvl) in d.oi.iter().enumerate() {
        match lvl {
            Some(Level::All) => {
                if e.objs[t] & !ep.objs[t] != 0 {
                    return false;
                }
            }
            // Guarded: a type the source does not carry imposes nothing.
            Some(Level::Any) if e.objs[t] != 0 && e.objs[t] & ep.objs[t] == 0 => {
                return false;
            }
            _ => {}
        }
    }
    true
}

pub fn count_matches(events: &[Event], d: &Constraint, i: usize, beta: &[(TypeId, u32)]) -> u32 {
    let e = &events[i];
    let mut c = 0;
    for (j, ep) in events.iter().enumerate() {
        if ep.act == d.target && in_scope(d.arrow, i, j) && passes(d, e, ep, beta) {
            c += 1;
        }
    }
    c
}

pub fn holds_at(events: &[Event], d: &Constraint, i: usize) -> bool {
    let e = &events[i];
    if e.act != d.source {
        return true;
    }
    for beta in assignments(d, e) {
        let c = count_matches(events, d, i, &beta);
        if c < d.n_min || c > d.n_max {
            return false;
        }
    }
    true
}

pub fn holds(events: &[Event], d: &Constraint) -> bool {
    (0..events.len()).all(|i| holds_at(events, d, i))
}
