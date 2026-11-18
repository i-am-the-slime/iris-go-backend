//! `Unsafe.Reference.reallyUnsafeRefEq`, which JavaScript answers with `===`.
//!
//! Each instantiation is decided from the Go type its two arguments share.
//! Pointers and scalars compare with `==`, as `===` compares JavaScript's
//! objects and primitives. Functions and slices have no `==` in Go, so the
//! `refeq` package compares their closure and backing-array pointers. Structs
//! (records and unboxed data) compare field by field, with `==` when every
//! field has it: equal contents are the same struct value, where JavaScript
//! would compare two objects. A value at `any` asks `refeq.SameAny`.
//!
//! Arguments of different Go types are a compile-time blocker: no value of
//! one is a value of the other, so the answer would always be `false`, which
//! JavaScript does not promise.

use super::{Emitter, binary, call, field, is_untyped_constant};
use crate::blocker::{Blocker, Blockers};
use crate::error::{GoError, GoResult, UnsupportedState};
use crate::foreign::{GoFunction, GoPackage};
use crate::mono::Expression;
use crate::syntax::{GoDeclaration, GoExpression, GoStatement, GoType};

/// Go's predeclared comparable types that the backend names.
pub(super) const BASIC_TYPES: &[&str] = &[
    "bool", "int", "int8", "int16", "int32", "int64", "uint", "uint8", "uint16", "uint32",
    "uint64", "uintptr", "byte", "rune", "float32", "float64", "string",
];

impl<'q, Q> Emitter<'_, '_, 'q, Q>
where
    Q: checking::ExternalQueries,
{
    pub(super) fn reference_equal(
        &mut self,
        left: &Expression,
        right: &Expression,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<GoExpression> {
        let shared = self.shared_type(left, right)?;
        let left = self.value(left, out)?;
        let right = self.value(right, out)?;
        let left = typed(left, &shared);
        let right = typed(right, &shared);
        Ok(self.same(&shared, left, right, out))
    }

    /// The Go type both arguments have, or the blocker naming both.
    fn shared_type(&mut self, left: &Expression, right: &Expression) -> GoResult<GoType> {
        let mut left_type = self.go_type(left.monotype)?;
        let mut right_type = self.go_type(right.monotype)?;
        self.resolve_aliases(&mut left_type);
        self.resolve_aliases(&mut right_type);
        if left_type == right_type {
            return Ok(left_type);
        }
        let state = UnsupportedState::ReferenceEqualityAcrossTypes {
            left: left_type.render(),
            right: right_type.render(),
        };
        let definition = match self.current {
            Some(function) => self.program.function(function).name.to_string(),
            None => "code generation".into(),
        };
        let blocker = Blocker { definition, state, requesters: vec![], occurrences: 1 };
        Err(GoError::Blocked(Blockers { blockers: vec![blocker] }))
    }

    fn same(
        &mut self,
        type_: &GoType,
        left: GoExpression,
        right: GoExpression,
        out: &mut Vec<GoStatement>,
    ) -> GoExpression {
        let mut type_ = type_.clone();
        self.resolve_aliases(&mut type_);
        match &type_ {
            GoType::Int
            | GoType::Float64
            | GoType::Bool
            | GoType::Rune
            | GoType::String
            | GoType::EmptyStruct
            | GoType::Pointer(_) => binary("==", left, right),
            GoType::Function { .. } => self.support("SameFunc", left, right),
            GoType::Slice(_) => self.support("SameSlice", left, right),
            GoType::Any | GoType::Erased(_) | GoType::Generic { .. } => {
                self.support("SameAny", left, right)
            }
            GoType::Struct(fields) => self.same_fields(fields, left, right, out),
            GoType::Named(name) if BASIC_TYPES.contains(&name.as_str()) => {
                binary("==", left, right)
            }
            GoType::Named(name) => match self.declared_type(name) {
                Some(GoType::Struct(fields)) => self.same_fields(&fields, left, right, out),
                Some(underlying) => self.same(&underlying, left, right, out),
                // A type a Go package declares, whose representation the
                // backend does not see.
                None => self.support("SameAny", left, right),
            },
        }
    }

    fn same_fields(
        &mut self,
        fields: &[(String, GoType)],
        left: GoExpression,
        right: GoExpression,
        out: &mut Vec<GoStatement>,
    ) -> GoExpression {
        if fields.iter().all(|(_, type_)| self.comparable(type_)) {
            return binary("==", left, right);
        }
        let left = self.shared(left, "left", out);
        let right = self.shared(right, "right", out);
        let mut comparisons = fields.iter().map(|(name, type_)| {
            (type_.clone(), field(left.clone(), name), field(right.clone(), name))
        });
        let Some((type_, first_left, first_right)) = comparisons.next() else {
            return GoExpression::Boolean(true);
        };
        let rest: Vec<_> = comparisons.collect();
        let mut conjunction = self.same(&type_, first_left, first_right, out);
        for (type_, field_left, field_right) in rest {
            let comparison = self.same(&type_, field_left, field_right, out);
            conjunction = binary("&&", conjunction, comparison);
        }
        conjunction
    }

    /// Whether Go's `==` compares the type without panicking: an interface
    /// may hold a function, and a foreign type's representation is unknown.
    fn comparable(&self, type_: &GoType) -> bool {
        let mut type_ = type_.clone();
        self.resolve_aliases(&mut type_);
        match &type_ {
            GoType::Int
            | GoType::Float64
            | GoType::Bool
            | GoType::Rune
            | GoType::String
            | GoType::EmptyStruct
            | GoType::Pointer(_) => true,
            GoType::Function { .. }
            | GoType::Slice(_)
            | GoType::Any
            | GoType::Erased(_)
            | GoType::Generic { .. } => false,
            GoType::Struct(fields) => fields.iter().all(|(_, field)| self.comparable(field)),
            GoType::Named(name) if BASIC_TYPES.contains(&name.as_str()) => true,
            GoType::Named(name) => {
                self.declared_type(name).is_some_and(|underlying| self.comparable(&underlying))
            }
        }
    }

    fn declared_type(&self, name: &str) -> Option<GoType> {
        self.type_declarations.iter().find_map(|declaration| match declaration {
            GoDeclaration::Type { name: declared, type_ } if declared == name => {
                Some(type_.clone())
            }
            _ => None,
        })
    }

    fn support(
        &mut self,
        name: &'static str,
        left: GoExpression,
        right: GoExpression,
    ) -> GoExpression {
        let function = self.go_function(GoFunction { package: GoPackage::RefEq, name });
        call(function, vec![left, right])
    }
}

/// An untyped constant at the type it is compared at, which `refeq.SameAny`
/// would otherwise box at the constant's default type.
fn typed(value: GoExpression, type_: &GoType) -> GoExpression {
    if !is_untyped_constant(&value) {
        return value;
    }
    GoExpression::Conversion { type_: type_.clone(), value: Box::new(value) }
}
