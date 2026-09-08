//! Exhaustive check of every cell of the source-anchored composition rule's
//! arrow-type and involvement admissibility tables against bounded
//! countermodel search. Reports disagreements first: a cell where the
//! predicted verdict and the search's verdict differ.

use oc_declare_reason::*;

const A: ActId = 0;
const B: ActId = 1;
const C: ActId = 2;

fn name(ar: Arrow) -> &'static str {
    match ar {
        Arrow::As => "AS",
        Arrow::Ef => "EF",
        Arrow::Ep => "EP",
    }
}

fn lname(l: Option<Level>) -> &'static str {
    match l {
        None => "omit",
        Some(Level::Any) => "Any",
        Some(Level::Each) => "Each",
        Some(Level::All) => "All",
    }
}

/// Arrow-type admissibility for the source-anchored composition rule,
/// restricted to the three enumerated arrow types.
fn arrow_admissible(af: Arrow, ar: Arrow) -> bool {
    match af {
        Arrow::As => true,
        Arrow::Ef => ar == Arrow::Ep,
        Arrow::Ep => ar == Arrow::Ef,
    }
}

/// Involvement-level admissibility for the source-anchored composition rule:
/// omitted admits anything; Any admits All or Each; All admits nothing.
fn oi_admissible(lf: Option<Level>, lr: Option<Level>) -> bool {
    match lf {
        None => true,
        Some(Level::Any) | Some(Level::Each) => matches!(lr, Some(Level::All) | Some(Level::Each)),
        Some(Level::All) => false,
    }
}

fn main() {
    let arrows = [Arrow::As, Arrow::Ef, Arrow::Ep];
    let f_levels = [None, Some(Level::Any), Some(Level::All)];
    let r_levels = [None, Some(Level::Any), Some(Level::Each), Some(Level::All)];
    let b = Bounds {
        max_events: 5,
        n_acts: 3,
        n_types: 1,
        objs_per_type: 3,
    };

    let mut rows = Vec::new();
    let (mut agree, mut disagree) = (0, 0);

    for af in arrows {
        for ar in arrows {
            for lf in f_levels {
                for lr in r_levels {
                    let d_r = Constraint::existence(ar, A, B, vec![lr]);
                    let d_f = Constraint::negative(af, B, C, vec![lf]);
                    let d_n = Constraint::negative(af, A, C, vec![lf]);
                    let side: Vec<SideCondition> = if lf.is_some() {
                        vec![SideCondition::Carries(A, 0)]
                    } else {
                        vec![]
                    };

                    let out = entails(&[d_r, d_f], &d_n, &side, &b);
                    let found = out.entailed();
                    let predicted = arrow_admissible(af, ar) && oi_admissible(lf, lr);
                    if found == predicted {
                        agree += 1;
                    } else {
                        disagree += 1;
                    }
                    rows.push((af, ar, lf, lr, predicted, found, out.countermodel));
                }
            }
        }
    }

    println!("## Disagreements with the paper's tables\n");
    let mut any_bad = false;
    for (af, ar, lf, lr, predicted, found, cm) in &rows {
        if predicted == found {
            continue;
        }
        any_bad = true;
        println!(
            "- **{} / {} / oi_f={} / oi_r={}**: paper says {}, search says {}",
            name(*af),
            name(*ar),
            lname(*lf),
            lname(*lr),
            if *predicted { "admissible" } else { "excluded" },
            if *found { "admissible" } else { "excluded" }
        );
        if let Some(m) = cm {
            println!("```\n{m}```");
        }
    }
    if !any_bad {
        println!("None. All {agree} cells agree.\n");
    }

    println!("\n## All cells\n");
    println!("| ar(d_f) | ar(d_r) | oi_f | oi_r | verdict | witness |");
    println!("|---|---|---|---|---|---|");
    for (af, ar, lf, lr, _, found, cm) in &rows {
        let w = cm
            .as_ref()
            .map(|m| format!("{} events", m.events.len()))
            .unwrap_or_default();
        println!(
            "| {} | {} | {} | {} | {} | {} |",
            name(*af),
            name(*ar),
            lname(*lf),
            lname(*lr),
            if *found { "admissible" } else { "excluded" },
            w
        );
    }
    eprintln!("agree {agree}, disagree {disagree}");
}
