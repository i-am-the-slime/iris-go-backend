use std::sync::Arc;

use checking::TypeId;
use checking::evidence::InstanceCandidateOrigin;
use smol_str::SmolStr;

/// A type-class dictionary resolved for a closed world. Dictionaries never reach
/// the generated program: they select which specialization a member reference
/// calls.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Dictionary {
    Instance(Arc<InstanceDictionary>),
    Symbol(SmolStr),
    Reflectable(Reflected),
    Trivial,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct InstanceDictionary {
    pub origin: InstanceCandidateOrigin,
    /// Closed types for the instance's variables, in signature order.
    pub types: Arc<[TypeId]>,
    /// Dictionaries for the instance's own constraints, in signature order.
    pub context: Arc<[Dictionary]>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Reflected {
    Integer(i32),
    String(SmolStr),
    Boolean(bool),
    Ordering(SmolStr),
}
