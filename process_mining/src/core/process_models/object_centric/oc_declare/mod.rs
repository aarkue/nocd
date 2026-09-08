//! OC-DECLARE Object-Centric Declarative Process Models
pub use crate::core::event_data::object_centric::utils::init_exit_events::{
    add_init_exit_events_to_ocel, EXIT_EVENT_PREFIX, INIT_EVENT_PREFIX,
};
use chrono::{DateTime, Duration, FixedOffset};
use schemars::JsonSchema;

use std::collections::{HashMap, HashSet};
use std::hash::Hash;

use itertools::Itertools;
use serde::{Deserialize, Serialize};

use crate::conformance::oc_declare::{satisfies_threshold, violation_fraction};
use crate::core::event_data::object_centric::linked_ocel::e2o_rev_type_index::E2ORevByTypeIndex;
use crate::core::event_data::object_centric::linked_ocel::slim_linked_ocel::{
    EventIndex, ObjectIndex,
};
use crate::core::event_data::object_centric::linked_ocel::{LinkedOCELAccess, SlimLinkedOCEL};

#[derive(
    Debug, Clone, Hash, PartialEq, Eq, Serialize, Deserialize, PartialOrd, Ord, JsonSchema,
)]
/// OC-DECLARE node (Activity or Object Init/Exit)
pub struct OCDeclareNode(String);

impl<'a> From<&'a OCDeclareNode> for &'a String {
    fn from(val: &'a OCDeclareNode) -> Self {
        &val.0
    }
}

impl OCDeclareNode {
    /// Create OC-DECLARE node from String
    pub fn new<T: Into<String>>(act: T) -> Self {
        Self(act.into())
    }

    /// Return node name
    pub fn as_str(&self) -> &str {
        self.0.as_str()
    }
}

#[derive(
    Debug, Clone, PartialEq, Eq, Serialize, Deserialize, Hash, PartialOrd, Ord, JsonSchema,
)]
/// OC-DECLARE Constraint arc/edge between two nodes (i.e., activities)
pub struct OCDeclareArc {
    /// Source node (e.g., triggering activity)
    pub from: OCDeclareNode,
    /// Target node (e.g., target activity)
    pub to: OCDeclareNode,
    /// Arc type, modeling temporal relation
    pub arc_type: OCDeclareArcType,
    /// Arc label specifying object involvement criteria
    pub label: OCDeclareArcLabel,
    /// First tuple element: min count (optional), Second: max count (optional)
    pub counts: (Option<usize>, Option<usize>),
}

impl OCDeclareArc {
    /// Clone this arc, only modifying its arc/arrow type
    pub fn clone_with_arc_type(&self, arc_type: OCDeclareArcType) -> Self {
        let mut ret = self.clone();
        ret.arc_type = arc_type;
        ret
    }

    /// Generate template string representation
    pub fn as_template_string(&self) -> String {
        format!(
            "{}({}, {}, {},{},{})",
            self.arc_type.get_name(),
            self.from.0,
            self.to.0,
            self.label.as_template_string(),
            self.counts.0.unwrap_or_default(),
            self.counts
                .1
                .map(|x| x.to_string())
                .unwrap_or(String::from("∞"))
        )
    }

    /// Get fraction of source events violating this constraint arc
    ///
    /// Returns a value from 0 (all source events satisfy this constraint) to 1 (all source events violate this constraint)
    pub fn violation_fraction(&self, linked_ocel: &SlimLinkedOCEL) -> f64 {
        violation_fraction(
            self.from.as_str(),
            self.to.as_str(),
            &self.label,
            &self.arc_type,
            &self.counts,
            linked_ocel,
            None,
        )
    }

    /// Checks whether the number of events violating this constraint arc is below (<=) the given noise threshold
    ///
    /// Returns false, if the fraction of events violating the constraint is above the noise threshold.
    pub fn satisfies_threshold(&self, linked_ocel: &SlimLinkedOCEL, noise_thresh: f64) -> bool {
        self.satisfies_threshold_indexed(linked_ocel, noise_thresh, None)
    }

    /// As [`OCDeclareArc::satisfies_threshold`], but reusing an existing index
    pub(crate) fn satisfies_threshold_indexed(
        &self,
        linked_ocel: &SlimLinkedOCEL,
        noise_thresh: f64,
        index: Option<&E2ORevByTypeIndex>,
    ) -> bool {
        satisfies_threshold(
            self.from.as_str(),
            self.to.as_str(),
            &self.label,
            &self.arc_type,
            &self.counts,
            linked_ocel,
            noise_thresh,
            index,
        )
    }
}

/// OC-DECLARE Arc Direction/Type
///
/// Models temporal relationships
#[derive(
    Debug, Clone, Copy, Hash, PartialEq, Eq, Serialize, Deserialize, PartialOrd, Ord, JsonSchema,
)]
pub enum OCDeclareArcType {
    /// Association: No temporal restrictions
    AS,
    /// Eventually-Follows: Target must occur after source event
    EF,
    /// Eventually-Precedes: Target must occur before source event
    EP,
    /// Directly-Follows: Target must occur directly after source event (considering events that involve all required objects)
    DF,
    /// Directly-Precedes: Target must occur directly before source event (considering events that involve all required objects)
    DP,
}
/// All OC-DECLARE Arc Types
pub const ALL_OC_DECLARE_ARC_TYPES: &[OCDeclareArcType] = &[
    OCDeclareArcType::AS,
    OCDeclareArcType::EF,
    OCDeclareArcType::EP,
    OCDeclareArcType::DF,
    OCDeclareArcType::DP,
];

impl OCDeclareArcType {
    /// Parse a string to an arc type
    ///
    /// e.g., `"AS"` -> [`OCDeclareArcType::AS`], `"EF"` -> [`OCDeclareArcType::EF`]
    ///
    /// Returns `None` if the string cannot be parsed
    pub fn parse_str(s: impl AsRef<str>) -> Option<Self> {
        match s.as_ref() {
            "AS" => Some(Self::AS),
            "EF" => Some(Self::EF),
            "EP" => Some(Self::EP),
            "DF" => Some(Self::DF),
            "DP" => Some(Self::DP),
            _ => None,
        }
    }

    /// Get name of this arc type as string (e.g., `"EF"`)
    pub fn get_name(&self) -> &'static str {
        match self {
            OCDeclareArcType::AS => "AS",
            OCDeclareArcType::EF => "EF",
            OCDeclareArcType::EP => "EP",
            OCDeclareArcType::DF => "DF",
            OCDeclareArcType::DP => "DP",
        }
    }

    /// Check if this arc type is dominated by other arc type
    pub fn is_dominated_by_or_eq(&self, arc_type: &OCDeclareArcType) -> bool {
        if *self == OCDeclareArcType::AS || self == arc_type {
            return true;
        }
        if *arc_type == OCDeclareArcType::AS {
            return false;
        }
        match arc_type {
            OCDeclareArcType::DF => *self == OCDeclareArcType::EF,
            OCDeclareArcType::DP => *self == OCDeclareArcType::EP,
            _ => false,
        }
    }
}

/// Object Type Association: Direct or O2O Object Types
#[derive(
    Debug, Clone, Hash, PartialEq, Eq, Serialize, Deserialize, PartialOrd, Ord, JsonSchema,
)]
#[serde(tag = "type")]
pub enum ObjectTypeAssociation {
    /// Simple: Direct Object Types involved with an Activity
    Simple {
        /// The object type
        object_type: String,
    },
    /// Indirect: Object Association through an O2O relationship
    O2O {
        /// First object type (for source event)
        first: String,
        /// Second object type (for target event)
        second: String,
        /// Specifies the direction of the O2O relationship.
        ///
        /// If reversed is `False`, `(first,second)` is considered
        reversed: bool,
    },
}

impl ObjectTypeAssociation {
    /// Create new simple (i.e., direct) object type association
    pub fn new_simple<T: Into<String>>(ot: T) -> Self {
        Self::Simple {
            object_type: ot.into(),
        }
    }
    /// Create indirect (i.e., O2O) object type association
    ///
    /// Considers the non-reversed direction, i.e., O2O from `ot1` to `ot2`
    pub fn new_o2o<T: Into<String>>(ot1: T, ot2: T) -> Self {
        Self::O2O {
            first: ot1.into(),
            second: ot2.into(),
            reversed: false,
        }
    }
    /// Create reversed indirect (i.e., O2O) object type association
    ///
    /// Considers the reversed direction, i.e., O2O from `ot2` to `ot1`
    pub fn new_o2o_rev<T: Into<String>>(ot1: T, ot2: T) -> Self {
        Self::O2O {
            first: ot1.into(),
            second: ot2.into(),
            reversed: true,
        }
    }

    /// Format as string
    pub fn as_template_string(&self) -> String {
        match self {
            ObjectTypeAssociation::Simple { object_type } => object_type.clone(),
            ObjectTypeAssociation::O2O {
                first,
                second,
                reversed,
            } => format!("{}{}{}", first, if !reversed { ">" } else { "<" }, second),
        }
    }

    /// Get the object index for all objects specified by the association for a specified event
    pub fn get_for_ev<'a>(
        &'a self,
        ev: &'a EventOrSynthetic,
        linked_ocel: &'a SlimLinkedOCEL,
    ) -> Vec<&'a ObjectIndex> {
        match self {
            ObjectTypeAssociation::Simple { object_type } => ev
                .get_e2o(linked_ocel)
                .filter(|o| {
                    let ot = o.get_ob_type(linked_ocel);
                    ot == object_type
                })
                .collect(),
            ObjectTypeAssociation::O2O {
                first,
                second,
                reversed,
            } => ev
                .get_e2o(linked_ocel)
                .filter(|o| o.get_ob_type(linked_ocel) == first)
                .flat_map(|o| {
                    if !reversed {
                        o.get_o2o(linked_ocel)
                            .filter(|o2| o2.get_ob_type(linked_ocel) == second)
                            .collect_vec()
                    } else {
                        o.get_o2o_rev(linked_ocel)
                            .filter(|o2| o2.get_ob_type(linked_ocel) == second)
                            .collect_vec()
                    }
                })
                .collect(),
        }
    }
}

#[derive(
    Debug, Clone, PartialEq, Eq, Serialize, Deserialize, Default, Hash, PartialOrd, Ord, JsonSchema,
)]
/// Object Involvement Label of an OC-DECLARE arc
pub struct OCDeclareArcLabel {
    /// Each (for each object of that type separately, there must be the specified number of relevant target events)
    pub each: Vec<ObjectTypeAssociation>,
    /// Any (there must be the specified number of relevant target events involving at least one of the objects of this type involved in the source event)
    pub any: Vec<ObjectTypeAssociation>,
    /// All (there must be the specified number of relevant target events involving all of the objects of this type involved in the source event)
    pub all: Vec<ObjectTypeAssociation>,
}

impl OCDeclareArcLabel {
    /// Format as template string
    pub fn as_template_string(&self) -> String {
        let mut ret = String::new();
        if !self.each.is_empty() {
            ret.push_str(&format!(
                "Each({})",
                self.each.iter().map(|ot| ot.as_template_string()).join(",")
            ));
        }
        if !self.all.is_empty() {
            if !self.each.is_empty() {
                ret.push_str(", ");
            }
            ret.push_str(&format!(
                "All({})",
                self.all.iter().map(|ot| ot.as_template_string()).join(",")
            ));
        }
        if !self.any.is_empty() {
            if !self.each.is_empty() || !self.all.is_empty() {
                ret.push_str(", ");
            }
            ret.push_str(&format!(
                "Any({})",
                self.any.iter().map(|ot| ot.as_template_string()).join(",")
            ));
        }
        ret
    }
}

impl OCDeclareArcLabel {
    /// Combine this OC-DECLARE arc label with another one
    ///
    /// Merges the different object involvements, where more strict requirements take precedence (e.g., ALL over ANY)
    pub fn combine(&self, other: &Self) -> Self {
        let all = self
            .all
            .iter()
            .chain(other.all.iter())
            .cloned()
            .collect::<HashSet<_>>();
        let each = self
            .each
            .iter()
            .chain(other.each.iter())
            .filter(|e| !all.contains(e))
            .cloned()
            .collect::<HashSet<_>>();
        let any = self
            .any
            .iter()
            .chain(other.any.iter())
            .filter(|e| !all.contains(e) && !each.contains(e))
            .cloned()
            .collect::<HashSet<_>>();
        Self {
            each: each.into_iter().sorted().collect(),
            all: all.into_iter().sorted().collect(),
            any: any.into_iter().sorted().collect(),
        }
    }

    /// Tests if this arc label is dominated by the other one
    pub fn is_dominated_by(&self, other: &Self) -> bool {
        let all_all = self.all.iter().all(|a| other.all.contains(a));
        if !all_all {
            return false;
        }
        let all_each = self
            .each
            .iter()
            .all(|a| other.each.contains(a) || other.all.contains(a));
        if !all_each {
            return false;
        }
        let all_any = self
            .any
            .iter()
            .all(|a| other.any.contains(a) || other.each.contains(a) || other.all.contains(a));
        all_any
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "type")]
/// Set filter modeling the predicate that all or any of the included elements must be present
pub enum SetFilter<T: Eq + Hash> {
    /// Any predicate: At least one of the contained elements must be present
    Any(Vec<T>),
    /// All predicate: All of the contained elements must be present
    All(Vec<T>),
}

impl<T: Eq + Hash + Ord> SetFilter<T> {
    /// Check if the specified `HashSet` fulfills this predicate
    pub fn check(&self, s: &[T]) -> bool {
        match self {
            SetFilter::Any(items) => items.iter().any(|i| s.binary_search(i).is_ok()),
            SetFilter::All(items) => items.iter().all(|i| s.binary_search(i).is_ok()),
        }
    }
}

impl<'b> OCDeclareArcLabel {
    /// Get all bindings for an OC-DECLARE arc label for a specified event.
    ///
    /// Bindings correspond to all scenarios for which the constraint has to be checked.
    /// In particular, there are multiple bindings for an event if there are multiple objects of a type that is included with EACH involvement.
    ///
    /// A type the event carries no object of is dropped rather than turned into a filter over an
    /// empty object list. The semantics makes such a type inert: the EACH quantifier ranges only
    /// over the types actually carried, an ALL containment out of the empty set holds of every
    /// target event, and an ANY conjunct is guarded on the source carrying the type. An empty
    /// filter would instead yield an empty target-event iterator (as the seed, and through
    /// `SetFilter::check` for ANY), which reports a negative constraint as vacuously satisfied
    /// where it is in fact violated, and a `min`-count constraint as violated where it holds.
    pub fn get_bindings<'a>(
        &'a self,
        ev: &'a EventOrSynthetic,
        linked_ocel: &'a SlimLinkedOCEL,
    ) -> impl Iterator<Item = Vec<SetFilter<&'a ObjectIndex>>> + use<'a, 'b> {
        self.each
            .iter()
            .sorted_by_key(|ot| match ot {
                ObjectTypeAssociation::Simple { object_type } => {
                    -(linked_ocel.get_obs_of_type(object_type).count() as i32)
                }
                ObjectTypeAssociation::O2O { second, .. } => {
                    -(linked_ocel.get_obs_of_type(second).count() as i32)
                }
            })
            .map(|otass| otass.get_for_ev(ev, linked_ocel))
            .filter(|objs| !objs.is_empty())
            .multi_cartesian_product()
            .map(|product| {
                self.all
                    .iter()
                    .sorted_by_key(|ot| match ot {
                        ObjectTypeAssociation::Simple { object_type } => {
                            -(linked_ocel.get_obs_of_type(object_type).count() as i32)
                        }
                        ObjectTypeAssociation::O2O { second, .. } => {
                            -(linked_ocel.get_obs_of_type(second).count() as i32)
                        }
                    })
                    .map(|otass| otass.get_for_ev(ev, linked_ocel))
                    .filter(|objs| !objs.is_empty())
                    .map(SetFilter::All)
                    .chain(if product.is_empty() {
                        Vec::default()
                    } else {
                        vec![SetFilter::All(product)]
                    })
                    .chain(
                        self.any
                            .iter()
                            .sorted_by_key(|ot| match ot {
                                ObjectTypeAssociation::Simple { object_type } => {
                                    -(linked_ocel.get_obs_of_type(object_type).count() as i32)
                                }
                                ObjectTypeAssociation::O2O { second, .. } => {
                                    -(linked_ocel.get_obs_of_type(second).count() as i32)
                                }
                            })
                            .map(|otass| otass.get_for_ev(ev, linked_ocel))
                            .filter(|x| !x.is_empty())
                            .map(|x| {
                                if x.len() == 1 {
                                    SetFilter::All(x)
                                } else {
                                    SetFilter::Any(x)
                                }
                            }),
                    )
                    .collect_vec()
            })
    }
}

#[derive(Serialize, Deserialize, Clone, Debug)]
/// Stores statistics on the number of objects of a certain type involved with an activity or in an O2O relationship.
pub struct ObjectInvolvementCounts {
    /// The minimum number of objects of a given type involved in a single instance.
    pub min: usize,
    /// The maximum number of objects of a given type involved in a single instance.
    pub max: usize,
    // mean: usize,
}
impl Default for ObjectInvolvementCounts {
    fn default() -> Self {
        Self {
            min: usize::MAX,
            max: Default::default(),
        }
    }
}

/// Get the object type involvements for an activity
///
/// Produces the min and max counts for objects per object type and activity
///
/// The result is a mapping: Activity -> (Object Type -> Counts)
pub fn get_activity_object_involvements(
    locel: &SlimLinkedOCEL,
) -> HashMap<String, HashMap<String, ObjectInvolvementCounts>> {
    locel
        .get_ev_types()
        .map(|et| {
            let mut nums_of_objects_per_type: HashMap<String, ObjectInvolvementCounts> = locel
                .get_ob_types()
                .map(|ot| (ot.to_string(), ObjectInvolvementCounts::default()))
                .collect();
            for ev in locel.get_evs_of_type(et) {
                // an object can appear more than once per event via distinct qualifiers;
                // count unique objects, not raw relationships
                let mut objs_for_ev: HashMap<&str, HashSet<&ObjectIndex>> = HashMap::new();
                for oi in ev.get_e2o(locel) {
                    let ot = oi.get_ob_type(locel);
                    objs_for_ev.entry(ot).or_default().insert(oi);
                }
                let num_of_objects_for_ev: HashMap<&str, usize> =
                    objs_for_ev.into_iter().map(|(ot, obs)| (ot, obs.len())).collect();
                for (ot, count) in num_of_objects_for_ev {
                    let num_ob_per_type = nums_of_objects_per_type.get_mut(ot).unwrap();

                    if count < num_ob_per_type.min {
                        num_ob_per_type.min = count
                    }
                    if count > num_ob_per_type.max {
                        num_ob_per_type.max = count;
                    }
                }
            }
            (
                et.to_string(),
                nums_of_objects_per_type
                    .into_iter()
                    .filter(|(_x, y)| y.max > 0)
                    .collect(),
            )
        })
        .collect()
}

#[derive(Serialize, Deserialize, Clone, Debug, Default)]
/// How many distinct objects of a type the events of an activity carry.
///
/// This is the precondition for the object-involvement dimension to have any
/// content: where no event of an activity carries two or more distinct objects
/// of a type, `All`, `Each` and `Any` impose the identical filter there, so
/// which level a discovery procedure reports is arbitrary.
pub struct ObjectMultiplicity {
    /// Number of events of the activity.
    pub events: usize,
    /// Events carrying at least one object of the type.
    pub carrying: usize,
    /// Events carrying two or more *distinct* objects of the type.
    pub converging: usize,
    /// Largest number of distinct objects of the type on a single event.
    pub max: usize,
}

impl ObjectMultiplicity {
    /// Whether `All`, `Each` and `Any` can differ at this activity and type.
    pub fn levels_distinguishable(&self) -> bool {
        self.converging > 0
    }
    /// Whether some event of the activity carries none of the type, which makes
    /// the involvement vacuous at those events.
    pub fn partially_carried(&self) -> bool {
        self.carrying > 0 && self.carrying < self.events
    }
}

/// Get the distribution of object counts per activity and object type.
///
/// Like [`get_activity_object_involvements`] this counts *distinct* objects: an
/// event may reference the same object under several qualifiers, and counting
/// relationships instead would inflate the multiplicity.
///
/// Object types no event of the activity carries are omitted.
pub fn get_activity_object_multiplicity(
    locel: &SlimLinkedOCEL,
) -> HashMap<String, HashMap<String, ObjectMultiplicity>> {
    locel
        .get_ev_types()
        .map(|et| {
            let mut per_type: HashMap<String, ObjectMultiplicity> = locel
                .get_ob_types()
                .map(|ot| (ot.to_string(), ObjectMultiplicity::default()))
                .collect();
            let mut n_events = 0usize;
            for ev in locel.get_evs_of_type(et) {
                n_events += 1;
                let mut objs_for_ev: HashMap<&str, HashSet<&ObjectIndex>> = HashMap::new();
                for oi in ev.get_e2o(locel) {
                    objs_for_ev
                        .entry(oi.get_ob_type(locel))
                        .or_default()
                        .insert(oi);
                }
                for (ot, obs) in objs_for_ev {
                    let m = per_type.get_mut(ot).unwrap();
                    m.carrying += 1;
                    if obs.len() >= 2 {
                        m.converging += 1;
                    }
                    if obs.len() > m.max {
                        m.max = obs.len();
                    }
                }
            }
            for m in per_type.values_mut() {
                m.events = n_events;
            }
            (
                et.to_string(),
                per_type
                    .into_iter()
                    .filter(|(_, m)| m.carrying > 0)
                    .collect(),
            )
        })
        .collect()
}

/// Get the multiplicity per activity over arbitrary object type associations,
/// including the transitive (O2O) ones.
///
/// [`get_activity_object_multiplicity`] covers only direct object types, which
/// is not what the involvement dimension ranges over: a constraint may involve
/// `(ot1 > ot2)`, the `ot2`-objects reachable from the event's `ot1`-objects. On
/// a log converted from case-centric data every event typically carries exactly
/// one object of each type, so the direct multiplicity is 1 everywhere while the
/// transitive multiplicity need not be.
///
/// Counts distinct objects. Associations no event of the activity resolves to
/// anything are omitted, keyed by [`ObjectTypeAssociation::as_template_string`].
pub fn get_activity_association_multiplicity(
    locel: &SlimLinkedOCEL,
    associations: &[ObjectTypeAssociation],
) -> HashMap<String, HashMap<String, ObjectMultiplicity>> {
    locel
        .get_ev_types()
        .map(|et| {
            let mut per_assoc: HashMap<String, ObjectMultiplicity> = associations
                .iter()
                .map(|a| (a.as_template_string(), ObjectMultiplicity::default()))
                .collect();
            let mut n_events = 0usize;
            for ev in locel.get_evs_of_type(et) {
                n_events += 1;
                let ev = EventOrSynthetic::Event(*ev);
                for assoc in associations {
                    let distinct: HashSet<&ObjectIndex> =
                        assoc.get_for_ev(&ev, locel).into_iter().collect();
                    if distinct.is_empty() {
                        continue;
                    }
                    let m = per_assoc.get_mut(&assoc.as_template_string()).unwrap();
                    m.carrying += 1;
                    if distinct.len() >= 2 {
                        m.converging += 1;
                    }
                    if distinct.len() > m.max {
                        m.max = distinct.len();
                    }
                }
            }
            for m in per_assoc.values_mut() {
                m.events = n_events;
            }
            (
                et.to_string(),
                per_assoc
                    .into_iter()
                    .filter(|(_, m)| m.carrying > 0)
                    .collect(),
            )
        })
        .collect()
}

/// All object type associations over the types of the log: every direct type,
/// and every ordered pair in both O2O directions.
pub fn all_object_type_associations(locel: &SlimLinkedOCEL) -> Vec<ObjectTypeAssociation> {
    let types: Vec<String> = locel.get_ob_types().map(|t| t.to_string()).collect();
    let mut out: Vec<ObjectTypeAssociation> = types
        .iter()
        .map(|t| ObjectTypeAssociation::new_simple(t.clone()))
        .collect();
    for a in &types {
        for b in &types {
            out.push(ObjectTypeAssociation::new_o2o(a.clone(), b.clone()));
            out.push(ObjectTypeAssociation::new_o2o_rev(a.clone(), b.clone()));
        }
    }
    out
}

/// Get Object-to-Object Involvements in the passed OCEL
///
/// Returns a mapping Object Type -> (Object Type -> Count)
///
/// where Count specifies how many objects of the second object type are referenced by each objects of the first object type
pub fn get_object_to_object_involvements(
    locel: &SlimLinkedOCEL,
) -> HashMap<String, HashMap<String, ObjectInvolvementCounts>> {
    locel
        .get_ob_types()
        .map(|ot| {
            let mut nums_of_objects_per_type: HashMap<String, ObjectInvolvementCounts> = locel
                .get_ob_types()
                .map(|ot| (ot.to_string(), ObjectInvolvementCounts::default()))
                .collect();
            for ob in locel.get_obs_of_type(ot) {
                let mut num_of_objects_for_ob: HashMap<&str, usize> = HashMap::new();
                for oi in ob.get_o2o(locel) {
                    let ot = oi.get_ob_type(locel);
                    *num_of_objects_for_ob.entry(ot).or_default() += 1;
                }
                for (ot, count) in num_of_objects_for_ob {
                    let num_ob_per_type = nums_of_objects_per_type.get_mut(ot).unwrap();

                    if count < num_ob_per_type.min {
                        num_ob_per_type.min = count
                    }
                    if count > num_ob_per_type.max {
                        num_ob_per_type.max = count;
                    }
                }
            }
            (
                ot.to_string(),
                nums_of_objects_per_type
                    .into_iter()
                    .filter(|(_x, y)| y.max > 0)
                    .collect(),
            )
        })
        .collect()
}

/// Get object involvement counts for the reverse direction of O2O relationships
///
/// Returns a mapping Object Type -> (Object Type -> Count)
///
/// where Count specifies how many objects of the second object type reference each object of the first object type
pub fn get_rev_object_to_object_involvements(
    locel: &SlimLinkedOCEL,
) -> HashMap<String, HashMap<String, ObjectInvolvementCounts>> {
    locel
        .get_ob_types()
        .map(|ot| {
            let mut nums_of_objects_per_type: HashMap<String, ObjectInvolvementCounts> = locel
                .get_ob_types()
                .map(|ot| (ot.to_string(), ObjectInvolvementCounts::default()))
                .collect();
            for ob in locel.get_obs_of_type(ot) {
                let mut num_of_objects_for_ob: HashMap<&str, usize> = HashMap::new();
                for oi in ob.get_o2o_rev(locel) {
                    let ot = oi.get_ob_type(locel);
                    *num_of_objects_for_ob.entry(ot).or_default() += 1;
                }
                for (ot, count) in num_of_objects_for_ob {
                    let num_ob_per_type = nums_of_objects_per_type.get_mut(ot).unwrap();

                    if count < num_ob_per_type.min {
                        num_ob_per_type.min = count
                    }
                    if count > num_ob_per_type.max {
                        num_ob_per_type.max = count;
                    }
                }
            }
            (
                ot.to_string(),
                nums_of_objects_per_type
                    .into_iter()
                    .filter(|(_x, y)| y.max > 0)
                    .collect(),
            )
        })
        .collect()
}
/// Extra per-(activity, object type) facts negative-constraint rules need, beyond min/max
/// counts: whether every event carries the type at all, and whether the type is unique
/// per event of the activity.
#[derive(Debug, Clone, Copy, Default)]
pub struct ActivityObjectFacts {
    /// Every event of the activity carries at least one object of this type.
    pub always_present: bool,
    /// No object of this type occurs in more than one event of the activity.
    pub at_most_one_event_per_object: bool,
}

/// Get [`ActivityObjectFacts`] per activity and object type.
///
/// Only includes `(activity, object type)` pairs the activity carries at least once —
/// missing means the type never occurs there.
pub fn get_activity_object_facts(
    locel: &SlimLinkedOCEL,
) -> HashMap<String, HashMap<String, ActivityObjectFacts>> {
    locel
        .get_ev_types()
        .map(|et| {
            let evs: Vec<_> = locel.get_evs_of_type(et).collect();
            let mut present_count: HashMap<String, usize> = HashMap::new();
            let mut per_object_event_count: HashMap<(String, ObjectIndex), usize> = HashMap::new();
            for ev in &evs {
                // an object can appear more than once per event via distinct qualifiers;
                // dedupe within this event before counting either fact
                let mut objs_here: HashSet<(String, ObjectIndex)> = HashSet::new();
                for oi in ev.get_e2o(locel) {
                    objs_here.insert((oi.get_ob_type(locel).to_string(), *oi));
                }
                for (ot, oi) in &objs_here {
                    *per_object_event_count.entry((ot.clone(), *oi)).or_default() += 1;
                }
                let types_here: HashSet<String> = objs_here.into_iter().map(|(ot, _)| ot).collect();
                for ot in types_here {
                    *present_count.entry(ot).or_default() += 1;
                }
            }
            let mut max_events_per_object: HashMap<String, usize> = HashMap::new();
            for ((ot, _), count) in &per_object_event_count {
                let m = max_events_per_object.entry(ot.clone()).or_default();
                *m = (*m).max(*count);
            }
            let facts = present_count
                .into_iter()
                .map(|(ot, count)| {
                    let always_present = count == evs.len();
                    let at_most_one_event_per_object =
                        max_events_per_object.get(&ot).copied().unwrap_or(0) <= 1;
                    (
                        ot,
                        ActivityObjectFacts {
                            always_present,
                            at_most_one_event_per_object,
                        },
                    )
                })
                .collect();
            (et.to_string(), facts)
        })
        .collect()
}

/// Represents either a regular event or a synthetic initialization/exit event for an object.
///
/// This enum is used to model synthetic events (as source or target) for OC-DECLARE constraints, which can be activated by
/// regular events from the log or by synthetic events marking object lifecycles.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum EventOrSynthetic {
    /// A regular event from the event log, identified by its index.
    Event(EventIndex),
    /// A synthetic event marking the initialization of an object, identified by the object's index.
    Init(ObjectIndex),
    /// A synthetic event marking the exit of an object, identified by the object's index.
    Exit(ObjectIndex),
}

impl EventOrSynthetic {
    /// Get the event type of the event (regular or synthetic)
    pub fn get_as_event_type(&self, locel: &SlimLinkedOCEL) -> String {
        match self {
            EventOrSynthetic::Event(event_index) => event_index.get_ev_type(locel).to_string(),
            EventOrSynthetic::Init(object_index) => {
                format!("{INIT_EVENT_PREFIX} {}", object_index.get_ob_type(locel))
            }
            EventOrSynthetic::Exit(object_index) => {
                format!("{EXIT_EVENT_PREFIX} {}", object_index.get_ob_type(locel))
            }
        }
    }
    fn get_mock_ev_index(&self, locel: &SlimLinkedOCEL) -> EventIndex {
        match self {
            EventOrSynthetic::Event(event_index) => *event_index,
            EventOrSynthetic::Init(x) | EventOrSynthetic::Exit(x) => {
                let evs = x.get_e2o_rev(locel);

                if matches!(self, EventOrSynthetic::Init(_)) {
                    evs.min_by_key(|ev| locel.get_ev_time(*ev))
                        .copied()
                        .unwrap_or(0_u32.into())
                } else {
                    evs.max_by_key(|ev| locel.get_ev_time(*ev))
                        .copied()
                        .unwrap_or(0_u32.into())
                }
            }
        }
    }

    /// Get the timestamp of the event (regular or synthetic)
    pub fn get_timestamp(&self, locel: &SlimLinkedOCEL) -> DateTime<FixedOffset> {
        let mock_ev_index = self.get_mock_ev_index(locel);

        let time = mock_ev_index.get_time(locel);
        match self {
            EventOrSynthetic::Event(_) => *time,
            EventOrSynthetic::Init(_) => *time - Duration::milliseconds(1),
            EventOrSynthetic::Exit(_) => *time + Duration::milliseconds(1),
        }
    }

    /// Get iterator over objects involved in the event (regular or synthetic)
    pub fn get_e2o<'a>(
        &'a self,
        locel: &'a SlimLinkedOCEL,
    ) -> Box<dyn Iterator<Item = &'a ObjectIndex> + 'a> {
        match self {
            EventOrSynthetic::Event(event_index) => Box::new(event_index.get_e2o(locel)),
            EventOrSynthetic::Init(x) | EventOrSynthetic::Exit(x) => Box::new(vec![x].into_iter()),
        }
    }
    /// Get set of objects involved in the event (regular or synthetic)
    pub fn get_e2o_set<'a>(&'a self, locel: &'a SlimLinkedOCEL) -> Vec<&'a ObjectIndex> {
        match self {
            EventOrSynthetic::Event(event_index) => {
                event_index
                    .get_e2o(locel)
                    // .sorted_unstable()
                    .collect()
            }
            EventOrSynthetic::Init(x) | EventOrSynthetic::Exit(x) => vec![x].into_iter().collect(),
        }
    }
    /// Get all events (regular or synthetic) of a specific event type
    pub fn get_all_syn_evs(locel: &SlimLinkedOCEL, ev_type: &str) -> Vec<Self> {
        if ev_type.starts_with(INIT_EVENT_PREFIX) {
            let ob_type = &ev_type[INIT_EVENT_PREFIX.len() + 1..ev_type.len()];
            locel
                .get_obs_of_type(ob_type)
                .map(|ob| EventOrSynthetic::Init(*ob))
                .collect()
        } else if ev_type.starts_with(EXIT_EVENT_PREFIX) {
            let ob_type = &ev_type[EXIT_EVENT_PREFIX.len() + 1..ev_type.len()];
            locel
                .get_obs_of_type(ob_type)
                .map(|ob| EventOrSynthetic::Exit(*ob))
                .collect()
        } else {
            locel
                .get_evs_of_type(ev_type)
                .map(|ev| EventOrSynthetic::Event(*ev))
                .collect()
        }
    }

    /// Get all events (regular or synthetic) of a specific event type involving a specific object
    pub fn get_all_of_et_for_ob<'a>(
        locel: &'a SlimLinkedOCEL,
        ev_type: &'a str,
        ob: ObjectIndex,
    ) -> Box<dyn Iterator<Item = Self> + 'a> {
        if ev_type.starts_with(INIT_EVENT_PREFIX) {
            let ob_type = &ev_type[INIT_EVENT_PREFIX.len() + 1..ev_type.len()];
            if ob.get_ob_type(locel) == ob_type {
                Box::new(vec![Self::Init(ob)].into_iter())
            } else {
                Box::new(Vec::default().into_iter())
            }
        } else if ev_type.starts_with(EXIT_EVENT_PREFIX) {
            let ob_type = &ev_type[EXIT_EVENT_PREFIX.len() + 1..ev_type.len()];
            if ob.get_ob_type(locel) == ob_type {
                Box::new(vec![Self::Exit(ob)].into_iter())
            } else {
                Box::new(Vec::default().into_iter())
            }
        } else {
            Box::new(
                ob.get_e2o_rev_of_evtype(locel, ev_type)
                    .map(|ev| Self::Event(*ev)),
            )
            // .collect()
        }
    }
    /// Get all events (regular or synthetic) involving a specific object
    pub fn get_all_for_ob(locel: &SlimLinkedOCEL, ob: ObjectIndex) -> Vec<Self> {
        ob.get_e2o_rev(locel)
            .map(|e| Self::Event(*e))
            .chain(vec![Self::Init(ob), Self::Exit(ob)])
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::core::event_data::object_centric::{
        appendable::AppendableOCEL, OCELRelationship, OCELType,
    };
    use chrono::DateTime;

    fn empty_type(name: &str) -> OCELType {
        OCELType {
            name: name.into(),
            attributes: Vec::new(),
        }
    }

    fn rel(object_id: &str) -> OCELRelationship {
        OCELRelationship {
            object_id: object_id.into(),
            qualifier: "q".into(),
        }
    }

    /// `place` always carries `order`; `o1` occurs in two `place` events (not unique).
    /// `pay` carries `order` on some events but not all (not always-present), always exactly one.
    fn sample_locel() -> SlimLinkedOCEL {
        let mut s = SlimLinkedOCEL::new();
        s.declare_event_type(empty_type("place")).unwrap();
        s.declare_event_type(empty_type("pay")).unwrap();
        s.declare_object_type(empty_type("order")).unwrap();
        for id in ["o1", "o2"] {
            s.append_object(id.into(), "order", Vec::new(), Vec::new())
                .unwrap();
        }
        let t = |i: u32| DateTime::parse_from_rfc3339(&format!("2024-01-0{i}T00:00:00Z")).unwrap();
        s.append_event("e0".into(), "place", t(1), Vec::new(), vec![rel("o1")])
            .unwrap();
        s.append_event("e1".into(), "place", t(2), Vec::new(), vec![rel("o1")])
            .unwrap();
        s.append_event("e2".into(), "place", t(3), Vec::new(), vec![rel("o2")])
            .unwrap();
        s.append_event("e3".into(), "pay", t(4), Vec::new(), vec![rel("o1")])
            .unwrap();
        s.append_event("e4".into(), "pay", t(5), Vec::new(), Vec::new())
            .unwrap();
        s.finalize().unwrap();
        s
    }

    #[test]
    fn facts_match_manual_computation() {
        let locel = sample_locel();
        let facts = get_activity_object_facts(&locel);

        let place = facts.get("place").unwrap().get("order").unwrap();
        assert!(place.always_present);
        assert!(!place.at_most_one_event_per_object); // o1 occurs in e0 and e1

        let pay = facts.get("pay").unwrap().get("order").unwrap();
        assert!(!pay.always_present); // e4 carries no order
        assert!(pay.at_most_one_event_per_object);
    }

    /// Two `place` events carry two distinct orders each, one carries a single
    /// order; every `pay` event carries at most one. So the involvement levels
    /// can differ at (`place`, `order`) and provably cannot at (`pay`, `order`).
    fn multiplicity_locel() -> SlimLinkedOCEL {
        let mut s = SlimLinkedOCEL::new();
        s.declare_event_type(empty_type("place")).unwrap();
        s.declare_event_type(empty_type("pay")).unwrap();
        s.declare_object_type(empty_type("order")).unwrap();
        for id in ["o1", "o2", "o3"] {
            s.append_object(id.into(), "order", Vec::new(), Vec::new())
                .unwrap();
        }
        let t = |i: u32| DateTime::parse_from_rfc3339(&format!("2024-01-0{i}T00:00:00Z")).unwrap();
        s.append_event(
            "p1".into(),
            "place",
            t(1),
            Vec::new(),
            vec![rel("o1"), rel("o2")],
        )
        .unwrap();
        s.append_event("p2".into(), "place", t(2), Vec::new(), vec![rel("o3")])
            .unwrap();
        // the same object under two qualifiers is still one object
        s.append_event(
            "y1".into(),
            "pay",
            t(3),
            Vec::new(),
            vec![
                rel("o1"),
                OCELRelationship {
                    object_id: "o1".into(),
                    qualifier: "other".into(),
                },
            ],
        )
        .unwrap();
        s.append_event("y2".into(), "pay", t(4), Vec::new(), Vec::new())
            .unwrap();
        s.finalize().unwrap();
        s
    }

    #[test]
    fn multiplicity_counts_distinct_objects_not_relationships() {
        let m = get_activity_object_multiplicity(&multiplicity_locel());

        let place = m.get("place").unwrap().get("order").unwrap();
        assert_eq!(place.events, 2);
        assert_eq!(place.carrying, 2);
        assert_eq!(place.converging, 1); // only p1
        assert_eq!(place.max, 2);
        assert!(place.levels_distinguishable());
        assert!(!place.partially_carried());

        let pay = m.get("pay").unwrap().get("order").unwrap();
        assert_eq!(pay.events, 2);
        assert_eq!(pay.carrying, 1); // y2 carries none
        // y1 references o1 twice under distinct qualifiers; that is one object
        assert_eq!(pay.converging, 0);
        assert_eq!(pay.max, 1);
        assert!(!pay.levels_distinguishable());
        assert!(pay.partially_carried());
    }

    #[test]
    fn multiplicity_omits_types_no_event_of_the_activity_carries() {
        let mut s = multiplicity_locel_with_unused_type();
        s.finalize().ok();
        let m = get_activity_object_multiplicity(&s);
        assert!(m.get("place").unwrap().get("unused").is_none());
    }

    fn multiplicity_locel_with_unused_type() -> SlimLinkedOCEL {
        let mut s = SlimLinkedOCEL::new();
        s.declare_event_type(empty_type("place")).unwrap();
        s.declare_object_type(empty_type("order")).unwrap();
        s.declare_object_type(empty_type("unused")).unwrap();
        s.append_object("o1".into(), "order", Vec::new(), Vec::new())
            .unwrap();
        s.append_object("u1".into(), "unused", Vec::new(), Vec::new())
            .unwrap();
        let t = DateTime::parse_from_rfc3339("2024-01-01T00:00:00Z").unwrap();
        s.append_event("p1".into(), "place", t, Vec::new(), vec![rel("o1")])
            .unwrap();
        s
    }
}
