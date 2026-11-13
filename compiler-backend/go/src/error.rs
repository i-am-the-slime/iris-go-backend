use building_types::QueryError;
use thiserror::Error;

pub type GoResult<T> = Result<T, GoError>;

#[derive(Debug, Error)]
pub enum GoError {
    #[error(transparent)]
    Query(#[from] QueryError),
    #[error("module {module_name} has source or checking errors")]
    SourceErrors { module_name: String },
    #[error("entry point {0} does not exist")]
    MissingEntry(String),
    #[error("cannot specialize {definition}: {state}")]
    Unsupported { definition: String, state: UnsupportedState },
}

#[derive(Debug, Clone, PartialEq, Eq, Error)]
pub enum UnsupportedState {
    #[error("checked expression contains an error")]
    ExpressionError,
    #[error("checked binder contains an error")]
    BinderError,
    #[error("checked declaration is missing")]
    MissingDeclaration,
    #[error("checked local declaration is missing")]
    MissingLocalDeclaration,
    #[error("value declaration has no equations")]
    MissingEquation,
    #[error("evidence is unsolved or erroneous")]
    UnsolvedEvidence,
    #[error("evidence refers to a dictionary parameter that is not in scope")]
    UnboundEvidence,
    #[error("instance head does not match the constraint {constraint}")]
    InstanceMismatch { constraint: String },
    #[error("instance has no member {member}")]
    MissingInstanceMember { member: String },
    #[error("instance has no superclass evidence for {superclass}")]
    MissingSuperclass { superclass: String },
    #[error("type variable {variable} has no instantiation at this use")]
    UninstantiatedVariable { variable: String },
    #[error("type {rendered} has no closed representation")]
    OpenType { rendered: String },
    #[error("type constructor {name} is applied to too few arguments")]
    UnsaturatedType { name: String },
    #[error("specialization exceeded {limit} instances; polymorphic recursion is not supported")]
    SpecializationLimit { limit: usize },
    #[error("declaration interleaves arguments before its constraints")]
    InterleavedAbstractions,
    #[error("foreign import {name} has no Go implementation")]
    UnknownForeign { name: String },
    #[error("{construct} is not supported by the Go backend yet")]
    Construct { construct: &'static str },
}
