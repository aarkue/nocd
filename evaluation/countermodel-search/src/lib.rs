//! Entailment between OC-DECLARE constraints, decided by searching for a
//! countermodel within a bounded universe of logs.
//!
//! The point is to replace hand-derived composition rules and their
//! side-condition tables with a procedure: ask whether a set of premises
//! entails a conclusion, and get either a witness log where it fails or the
//! statement that none exists up to the bound.

pub mod model;
pub mod search;
pub mod semantics;

pub use model::{ActId, Arrow, Constraint, Event, Level, MicroLog, ObjSet, TypeId, INF};
pub use search::{entails, Bounds, Outcome, SideCondition};
pub use semantics::{holds, holds_at};
