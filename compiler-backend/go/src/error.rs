use building_types::QueryError;
use files::FileId;
use thiserror::Error;

use crate::blocker::Blockers;

pub type GoResult<T> = Result<T, GoError>;

#[derive(Debug, Error)]
pub enum GoError {
    #[error(transparent)]
    Query(#[from] QueryError),
    #[error("cannot compile modules with source or checking errors: {}", .module_names.join(", "))]
    SourceErrors { files: Vec<FileId>, module_names: Vec<String> },
    #[error("entry point {0} does not exist")]
    MissingEntry(String),
    #[error("cannot specialize {definition}: {state}")]
    Unsupported { definition: String, state: UnsupportedState },
    #[error("{0}")]
    Blocked(Blockers),
    #[error("entry module {entry} is imported by {importer}, but Go cannot import package main")]
    EntryImported { entry: String, importer: String },
    #[error(
        "the Go structs {first} and {second} both represent records with the same fields; a record can have one Go struct"
    )]
    SharedRecordStruct { first: String, second: String },
    #[error(transparent)]
    RepresentationChange(Box<RepresentationChange>),
}

#[derive(Debug, Error)]
#[error(
    "{location}cannot specialize {definition}: unsafeCoerce from {from} (Go {from_go}) to {to} (Go {to_go}) changes representation"
)]
pub struct RepresentationChange {
    /// `path:line:column: `, or empty when the coercion's source is unknown.
    pub location: String,
    pub definition: String,
    pub from: String,
    pub from_go: String,
    pub to: String,
    pub to_go: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Error)]
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
    #[error("evidence is applied to a value whose type does not abstract over it")]
    UnabstractedEvidence,
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
    #[error(
        "polymorphic recursion grows the type class evidence it passes, which only run-time dictionaries could erase"
    )]
    GrowingEvidence,
    #[error(
        "foreign data type {name} has no Go representation; the Go file next to its module's source (Foo.go beside Foo.purs) declares it as a named type"
    )]
    ForeignData { name: String },
    #[error(
        "foreign import {name} has no Go implementation; write one in a Go file next to its module's source (Foo.go beside Foo.purs)"
    )]
    UnknownForeign { name: String },
    #[error("foreign import {name} has no Go implementation in {files} (expected func {function})")]
    MissingGoFunction { name: String, files: String, function: String },
    #[error(
        "foreign data type {name} has no Go representation in {files} (expected type {type_name})"
    )]
    MissingGoType { name: String, files: String, type_name: String },
    #[error(
        "reallyUnsafeRefEq compares values of different Go types, {left} and {right}, which share no reference"
    )]
    ReferenceEqualityAcrossTypes { left: String, right: String },
    #[error("{construct} is not supported by the Go backend yet")]
    Construct { construct: &'static str },
    #[error(
        "Data.Int64.Internal's Long' is applied to {rendered}, which is neither Signed nor Unsigned; Go has an int64 for Long' Signed and a uint64 for Long' Unsigned"
    )]
    OpenSignedness { rendered: String },
    #[error(
        "a Data.Int64.Internal Long here is neither Int64's nor UInt64's: the definition's types name no single Long' Signed or Long' Unsigned for it to be"
    )]
    UnknownSignedness,
}

impl GoError {
    /// A construct the emitter cannot compile.
    pub fn unsupported_construct(construct: &'static str) -> GoError {
        GoError::Unsupported {
            definition: "code generation".into(),
            state: UnsupportedState::Construct { construct },
        }
    }
}
