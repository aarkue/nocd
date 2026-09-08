//! Entailment by bounded countermodel search: `premises |= conclusion` holds up
//! to the bound iff no log within the bound satisfies every premise and
//! violates the conclusion. A returned log is a witness that the entailment
//! fails; `None` is evidence, not proof.

use crate::model::*;
use crate::semantics::{assignments, count_matches, holds};

#[derive(Clone, Debug)]
pub struct Bounds {
    pub max_events: usize,
    pub n_acts: ActId,
    pub n_types: usize,
    pub objs_per_type: u32,
}

/// Facts about a whole log that a single event cannot decide by itself, so the
/// search needs them supplied explicitly rather than derived from the model.
#[derive(Clone, Debug)]
pub enum SideCondition {
    /// Every event of this activity carries at least one object of this type.
    Carries(ActId, TypeId),
    /// Each object of this type occurs in at most one event of this activity.
    /// Combined with `Carries` on the same (activity, type), this makes an AS
    /// self-loop constraint on that pair equivalent to per-object uniqueness,
    /// the guard side-condition behind the equivalence-set reduction.
    AtMostOnePerObject(ActId, TypeId),
}

#[derive(Debug)]
pub struct Outcome {
    pub countermodel: Option<MicroLog>,
    pub logs_checked: u64,
}

impl Outcome {
    pub fn entailed(&self) -> bool {
        self.countermodel.is_none()
    }
}

/// Iterative deepening, so a returned countermodel is minimal in event count:
/// once depth `d-1` has been exhausted, anything found at depth `d` is smallest.
pub fn entails(
    premises: &[Constraint],
    conclusion: &Constraint,
    side: &[SideCondition],
    b: &Bounds,
) -> Outcome {
    let mut checked = 0u64;
    for depth in 1..=b.max_events {
        let bd = Bounds {
            max_events: depth,
            ..b.clone()
        };
        let mut events = Vec::new();
        let mut used = vec![0u32; b.n_types];
        if let Some(cm) = dfs(
            premises,
            conclusion,
            side,
            &bd,
            &mut events,
            &mut used,
            &mut checked,
        ) {
            return Outcome {
                countermodel: Some(cm),
                logs_checked: checked,
            };
        }
    }
    Outcome {
        countermodel: None,
        logs_checked: checked,
    }
}

/// Object ids within a type are interchangeable, so an event may reuse any id
/// already seen and introduce only the single next one. That keeps one
/// representative per isomorphism class.
fn object_choices(n_types: usize, used: &[ObjSet], cap: u32) -> Vec<Vec<ObjSet>> {
    let widths: Vec<u64> = (0..n_types)
        .map(|t| 1u64 << (used[t].count_ones() + 1).min(cap))
        .collect();
    let total: u64 = widths.iter().product();
    (0..total)
        .map(|idx| {
            let mut rest = idx;
            let mut c = Vec::with_capacity(n_types);
            for w in &widths {
                c.push((rest % w) as ObjSet);
                rest /= w;
            }
            c
        })
        .collect()
}

fn side_ok(act: ActId, objs: &[ObjSet], side: &[SideCondition]) -> bool {
    side.iter().all(|s| match s {
        SideCondition::Carries(a, t) => act != *a || objs[*t] != 0,
        SideCondition::AtMostOnePerObject(..) => true,
    })
}

/// Conditions that need the prefix rather than the single event.
fn side_ok_prefix(events: &[Event], side: &[SideCondition]) -> bool {
    side.iter().all(|s| match s {
        SideCondition::Carries(..) => true,
        SideCondition::AtMostOnePerObject(a, t) => {
            let mut seen: ObjSet = 0;
            for e in events.iter().filter(|e| e.act == *a) {
                if seen & e.objs[*t] != 0 {
                    return false;
                }
                seen |= e.objs[*t];
            }
            true
        }
    })
}

/// Match sets grow monotonically as later events are appended (AS and EF gain
/// targets, EP scopes of existing sources are already fixed), so an
/// upper-bounded premise violated on a prefix stays violated.
fn prefix_violates_upper(events: &[Event], premises: &[Constraint]) -> bool {
    for p in premises {
        if !p.upper_bounded() {
            continue;
        }
        for i in 0..events.len() {
            if events[i].act != p.source {
                continue;
            }
            for beta in assignments(p, &events[i]) {
                if count_matches(events, p, i, &beta) > p.n_max {
                    return true;
                }
            }
        }
    }
    false
}

fn dfs(
    premises: &[Constraint],
    conclusion: &Constraint,
    side: &[SideCondition],
    b: &Bounds,
    events: &mut Vec<Event>,
    used: &mut Vec<ObjSet>,
    checked: &mut u64,
) -> Option<MicroLog> {
    if !events.is_empty() {
        *checked += 1;
        if premises.iter().all(|p| holds(events, p)) && !holds(events, conclusion) {
            return Some(MicroLog {
                events: events.clone(),
            });
        }
    }
    if events.len() >= b.max_events {
        return None;
    }
    for act in 0..b.n_acts {
        for objs in object_choices(b.n_types, used, b.objs_per_type) {
            if !side_ok(act, &objs, side) {
                continue;
            }
            let saved = used.clone();
            for t in 0..b.n_types {
                used[t] |= objs[t];
            }
            events.push(Event { act, objs });
            let found = if prefix_violates_upper(events, premises) || !side_ok_prefix(events, side)
            {
                None
            } else {
                dfs(premises, conclusion, side, b, events, used, checked)
            };
            events.pop();
            used.clone_from(&saved);
            if found.is_some() {
                return found;
            }
        }
    }
    None
}
