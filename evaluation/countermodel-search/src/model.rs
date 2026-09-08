pub type ActId = u8;
pub type TypeId = usize;

/// Objects of one type, as a bitmask over object ids. Ids are namespaced per
/// type, so the same bit in two types is two different objects.
pub type ObjSet = u32;

pub const INF: u32 = u32::MAX;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Arrow {
    As,
    Ef,
    Ep,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Level {
    All,
    Each,
    Any,
}

#[derive(Clone, Debug)]
pub struct Constraint {
    pub arrow: Arrow,
    pub source: ActId,
    pub target: ActId,
    /// Indexed by TypeId; None is an omitted type.
    pub oi: Vec<Option<Level>>,
    pub n_min: u32,
    pub n_max: u32,
}

impl Constraint {
    pub fn new(
        arrow: Arrow,
        source: ActId,
        target: ActId,
        oi: Vec<Option<Level>>,
        n_min: u32,
        n_max: u32,
    ) -> Self {
        Self {
            arrow,
            source,
            target,
            oi,
            n_min,
            n_max,
        }
    }

    pub fn existence(arrow: Arrow, source: ActId, target: ActId, oi: Vec<Option<Level>>) -> Self {
        Self::new(arrow, source, target, oi, 1, INF)
    }

    pub fn negative(arrow: Arrow, source: ActId, target: ActId, oi: Vec<Option<Level>>) -> Self {
        Self::new(arrow, source, target, oi, 0, 0)
    }

    pub fn upper_bounded(&self) -> bool {
        self.n_max != INF
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Event {
    pub act: ActId,
    pub objs: Vec<ObjSet>,
}

/// Events are totally ordered by index, which stands in for the injective
/// timestamp function.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct MicroLog {
    pub events: Vec<Event>,
}

impl std::fmt::Display for MicroLog {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (i, e) in self.events.iter().enumerate() {
            let objs: Vec<String> = e
                .objs
                .iter()
                .enumerate()
                .map(|(t, s)| {
                    let ids: Vec<String> = (0..32)
                        .filter(|o| s & (1 << o) != 0)
                        .map(|o| format!("o{t}_{o}"))
                        .collect();
                    format!("{{{}}}", ids.join(","))
                })
                .collect();
            writeln!(f, "  e{i}: act={} objs={}", e.act, objs.join(" "))?;
        }
        Ok(())
    }
}
