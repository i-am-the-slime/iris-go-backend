//! Go's standard library in place of a go-support function where the two do exactly the same,
//! so that the code reads as Go: `strconv.Itoa(n)` for `show n`, `strings.Contains` for
//! `contains`. A function that counts or indexes UTF-16 code units, or joins strings whose
//! lone surrogates may meet, stays in go-support's prim package.

use super::{Emitter, call, is_simple};
use crate::foreign::GoFunction;
use crate::monomorphic::Expression;
use crate::monotype::Monotype;
use crate::syntax::{GoExpression, GoPackage, GoUnaryOperator};

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
                Some(self.standard(GoPackage::Strconv, "Itoa", vec![value.clone()]))
            }
            // strings.Contains takes its operands the other way around, which keeps the order
            // they are worked out in where one of them is a variable or a constant.
            (GoPackage::Prim, "StringContains", [pattern, value])
                if is_simple(pattern) || is_simple(value) =>
            {
                Some(self.standard(
                    GoPackage::Strings,
                    "Contains",
                    vec![value.clone(), pattern.clone()],
                ))
            }
            // A separator of whole characters splits the WTF-8 bytes where it splits the code
            // units.
            (GoPackage::Prim, "StringSplit", [separator @ GoExpression::String(text), value])
                if !text.is_empty() =>
            {
                Some(self.standard(
                    GoPackage::Strings,
                    "Split",
                    vec![value.clone(), separator.clone()],
                ))
            }
            (GoPackage::Int64, "ToString_", [value, radix @ GoExpression::Integer(2..=36)]) => {
                let name = match self.monotypes.get(arguments[0].monotype) {
                    Monotype::UInt64 => "FormatUint",
                    _ => "FormatInt",
                };
                Some(self.standard(GoPackage::Strconv, name, vec![value.clone(), radix.clone()]))
            }
            _ => None,
        }
    }

    /// `strconv.FormatBool(condition)`, `show` of a Boolean.
    pub(super) fn format_boolean(&mut self, condition: GoExpression) -> GoExpression {
        self.standard(GoPackage::Strconv, "FormatBool", vec![condition])
    }

    fn standard(
        &mut self,
        package: GoPackage,
        name: &str,
        arguments: Vec<GoExpression>,
    ) -> GoExpression {
        let function = self.qualified(package, name);
        call(function, arguments)
    }
}

fn integer(expression: &GoExpression) -> Option<i64> {
    match expression {
        GoExpression::Integer(value) => Some(*value),
        GoExpression::Unary { operator: GoUnaryOperator::Negate, operand } => {
            match operand.as_ref() {
                GoExpression::Integer(value) => Some(-value),
                _ => None,
            }
        }
        _ => None,
    }
}

/// Whether a call is of a `strconv` function whose result is never empty and begins and ends
/// in ASCII.
pub(super) fn is_ascii_ended(function: &GoExpression) -> bool {
    function
        .name_in(GoPackage::Strconv)
        .is_some_and(|name| matches!(name, "Itoa" | "FormatInt" | "FormatUint" | "FormatBool"))
}
