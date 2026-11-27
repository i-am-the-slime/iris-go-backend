//! Uniqueness: which values a function holds the only reference to, so that it may overwrite
//! their memory instead of allocating.
//!
//! Go has no reference counts, so uniqueness is proven statically. A value is unique where it
//! was built in the function, or passed in by a caller that gives up its last reference to it,
//! and the function then uses it linearly ([`paths`]): it consumes it at most once on every
//! path, reads it only before that, and no relative sharing its cells is used next to it.
//! Values that closures capture, effects run later, or the program keeps elsewhere are shared.
//!
//! The analyses that reuse memory are clients of these queries:
//!
//! - `reuse.rs` overwrites the cells of constructors that a function matched and owns
//!   ([`is_unique`], [`relatives`]);
//! - `recycling.rs` writes a tail loop's next array into the one it built an iteration before
//!   ([`next_iterations`]).
//!
//! `IRIS_GO_REUSE=0` turns both off, to measure what they buy. The switch is temporary.

mod iteration;
mod linearity;
mod paths;

pub(super) use iteration::{TailLoop, next_iterations};
pub(super) use linearity::{
    Branch, Forced, Scope, Shapes, guarded_expressions, is_only_read, is_unique, is_unique_field,
    is_unique_path, relatives,
};

/// Whether code may reuse the memory of the values it owns. `IRIS_GO_REUSE=0` turns reuse off.
pub(super) fn enabled() -> bool {
    static ENABLED: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ENABLED.get_or_init(|| std::env::var_os("IRIS_GO_REUSE").is_none_or(|value| value != "0"))
}
