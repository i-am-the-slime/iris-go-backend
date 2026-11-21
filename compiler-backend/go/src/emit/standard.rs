//! Go's standard library in place of a go-support function where the two do exactly the same,
//! so that the code reads as Go: `strconv.Itoa(int(n))` for `show n`, `strings.Contains` for
//! `contains`. A function that counts or indexes UTF-16 code units, or joins strings whose
//! lone surrogates may meet, stays in go-support's prim package.

use super::{Emitter, call, is_simple};
use crate::foreign::{GoFunction, GoPackage};
use crate::mono::Expression;
use crate::monotype::Monotype;
use crate::syntax::{GoExpression, GoType};

impl<Q> Emitter<'_, '_, '_, Q>
where
    Q: checking::ExternalQueries,
{
    /// `function` applied to `values`, the emitted `arguments`, as the standard library says it,
    /// if it has the function.
    pub(super) fn standard_call(
        &mut self,
        function: GoFunction,
        values: &[GoExpression],
        arguments: &[Expression],
    ) -> Option<GoExpression> {
        match (function.package, function.name, values) {
            (GoPackage::Prim, "ShowInt", [value]) if let Some(constant) = integer(value) => {
                Some(GoExpression::String(constant.to_string()))
            }
            (GoPackage::Prim, "ShowInt", [value]) => {
                let value = as_int(value.clone());
                Some(self.standard("strconv", "Itoa", vec![value]))
            }
            // strings.Contains takes its operands the other way around, which keeps the order
            // they are worked out in where one of them is a variable or a constant.
            (GoPackage::Prim, "StringContains", [pattern, value])
                if is_simple(pattern) || is_simple(value) =>
            {
                Some(self.standard("strings", "Contains", vec![value.clone(), pattern.clone()]))
            }
            // A separator of whole characters splits the WTF-8 bytes where it splits the code
            // units.
            (GoPackage::Prim, "StringSplit", [separator @ GoExpression::String(text), value])
                if !text.is_empty() =>
            {
                Some(self.standard("strings", "Split", vec![value.clone(), separator.clone()]))
            }
            (GoPackage::Int64, "ToString_", [value, radix @ GoExpression::Integer(2..=36)]) => {
                let name = match self.monotypes.get(arguments[0].monotype) {
                    Monotype::UInt64 => "FormatUint",
                    _ => "FormatInt",
                };
                Some(self.standard("strconv", name, vec![value.clone(), radix.clone()]))
            }
            _ => None,
        }
    }

    /// `strconv.FormatBool(condition)`, `show` of a Boolean.
    pub(super) fn format_boolean(&mut self, condition: GoExpression) -> GoExpression {
        self.standard("strconv", "FormatBool", vec![condition])
    }

    fn standard(
        &mut self,
        package: &str,
        name: &str,
        arguments: Vec<GoExpression>,
    ) -> GoExpression {
        self.imports.insert(package.into());
        let function = GoExpression::Qualified { package: package.into(), name: name.into() };
        call(function, arguments)
    }
}

/// An `int32` as Go's `int`: a length the emitter made an `int32` is the length again.
fn as_int(value: GoExpression) -> GoExpression {
    if let GoExpression::Conversion { type_: GoType::Named(type_), value: inner } = &value
        && type_ == "int32"
        && let GoExpression::Call { function, .. } = inner.as_ref()
        && matches!(function.as_ref(), GoExpression::Identifier(name) if name == "len")
    {
        return *inner.clone();
    }
    GoExpression::Conversion { type_: GoType::Int, value: Box::new(value) }
}

fn integer(expression: &GoExpression) -> Option<i64> {
    match expression {
        GoExpression::Integer(value) => Some(*value),
        GoExpression::Unary { operator: "-", operand } => match operand.as_ref() {
            GoExpression::Integer(value) => Some(-value),
            _ => None,
        },
        _ => None,
    }
}

/// Whether a call is of a `strconv` function whose result is never empty and begins and ends
/// in ASCII.
pub(super) fn is_ascii_ended(function: &GoExpression) -> bool {
    matches!(
        function,
        GoExpression::Qualified { package, name }
            if package == "strconv"
                && matches!(name.as_str(), "Itoa" | "FormatInt" | "FormatUint" | "FormatBool")
    )
}
