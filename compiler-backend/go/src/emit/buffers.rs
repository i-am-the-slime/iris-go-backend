//! A string that a loop only appends to, `acc <> s`, is built in a `[]byte` that grows in place,
//! and becomes a string once, where the loop ends. Go strings are immutable, so `acc + s` copies
//! the whole accumulated string at every step, which is quadratic; JavaScript engines build ropes.
//!
//! The ownership analysis decides when this is safe: the step reads the accumulator only to append
//! to it or to pass it on unchanged, so no one sees the buffer while it still grows.

use super::iteration::Callback;
use super::ownership::{self, Carried, Place};
use super::{Emitter, Mode, Sink, identifier_expression};
use crate::error::GoResult;
use crate::monomorphic::{Expression, ExpressionKind, Function, FunctionId};
use crate::monotype::{Monotype, MonotypeId};
use crate::syntax::{GoExpression, GoStatement, GoType};

impl<'q, Q> Emitter<'_, '_, 'q, Q>
where
    Q: checking::ExternalQueries,
{
    /// `append(buffer, s...)` for an owned `acc <> s`.
    pub(super) fn append_to_buffer(
        &mut self,
        arguments: &[Expression],
        out: &mut Vec<GoStatement>,
    ) -> GoResult<GoExpression> {
        let buffer = match &arguments[0].kind {
            ExpressionKind::Local(id) if let Some(buffer) = self.byte_buffers.get(id) => {
                identifier_expression(buffer)
            }
            _ => self.value(&arguments[0], out)?,
        };
        if let GoExpression::Identifier(name) = &buffer {
            self.sink(&arguments[1], Mode::Value, Sink::Write(name.clone()), out)?;
            return Ok(buffer);
        }
        let suffix = self.value(&arguments[1], out)?;
        Ok(self.buffer_append(buffer, suffix))
    }

    /// The appends of a fold's step that extend its string accumulator in place.
    pub(super) fn owned_string_appends<'e>(
        &self,
        callback: &Callback<'e>,
        accumulator_position: usize,
        monotype: MonotypeId,
    ) -> Vec<&'e Expression> {
        let Callback::Inline { parameters, body } = callback else { return vec![] };
        if !matches!(self.monotypes.get(monotype), Monotype::String) {
            return vec![];
        }
        let carried = Carried::new(parameters[accumulator_position].id, &Place::Whole);
        ownership::owned_snocs(carried, body).unwrap_or_default()
    }

    /// The string parameters of a self-recursive loop that its tail calls only append to, with
    /// the appends; not the ones a closure captures.
    pub(super) fn owned_loop_strings(
        &self,
        id: FunctionId,
        function: &Function,
        captured: &[usize],
    ) -> Vec<(usize, Vec<*const Expression>)> {
        let arity = function.parameters.len();
        let mut owned = vec![];
        for (position, parameter) in function.parameters.iter().enumerate() {
            if captured.contains(&position)
                || !matches!(self.monotypes.get(parameter.monotype), Monotype::String)
            {
                continue;
            }
            let tail_call = ownership::TailCall { function: id, arity, position };
            let carried = Carried::new(parameter.id, &Place::Whole);
            let Some(nodes) = ownership::owned_loop_snocs(carried, &function.body, tail_call)
            else {
                continue;
            };
            if !nodes.is_empty() {
                owned.push((position, nodes.into_iter().map(std::ptr::from_ref).collect()));
            }
        }
        owned
    }
}

pub(super) fn byte_slice() -> GoType {
    GoType::Slice(Box::new(GoType::Named("byte".into())))
}

/// `[]byte(value)`: a buffer of its own, whatever shares the string.
pub(super) fn to_bytes(value: GoExpression) -> GoExpression {
    // An empty buffer is nil, which `append` grows as it would any other.
    if matches!(&value, GoExpression::String(text) if text.is_empty()) {
        let nil = GoExpression::nil();
        return GoExpression::Conversion { type_: byte_slice(), value: Box::new(nil) };
    }
    GoExpression::Conversion { type_: byte_slice(), value: Box::new(value) }
}

pub(super) fn to_string(buffer: GoExpression) -> GoExpression {
    GoExpression::Conversion { type_: GoType::String, value: Box::new(buffer) }
}
