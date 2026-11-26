//! purescript-int64's Longs as Go's `int64` and `uint64`.
//!
//! The operations wrap as long.js's two's complement does, which Go's own
//! operators on 64-bit integers already do. Go checks constant expressions
//! for overflow instead, so an operation whose operands are all constants
//! is worked out here, with wrapping, and written as one constant.

use super::{Emitter, binary, negated};
use crate::foreign::{Comparison, GoFunction, GoPackage};
use crate::primitives::{Int64Operation, Int64Value, Signedness};
use crate::syntax::{GoExpression, GoType};

impl<'p, Q> Emitter<'p, '_, '_, Q>
where
    Q: checking::ExternalQueries,
{
    pub(super) fn int64_operation(
        &mut self,
        operation: Int64Operation,
        signedness: Signedness,
        mut values: Vec<GoExpression>,
    ) -> GoExpression {
        use Int64Operation as Operation;
        let long = signedness.go_type();
        let typed = |type_: &str, value: GoExpression| GoExpression::Conversion {
            type_: GoType::Named(type_.into()),
            value: Box::new(value),
        };
        if operation == Operation::FromInt {
            return match int_value(&values[0]) {
                Some(value) => long_literal(value, signedness),
                None => typed(long, values.remove(0)),
            };
        }
        let constants: Option<Vec<i64>> = values.iter().map(long_constant).collect();
        if let Some(constants) = constants
            && let Some(folded) = self.folded(operation, signedness, &constants)
        {
            return folded;
        }
        let count = |amount: GoExpression| match long_constant(&amount) {
            Some(amount) => GoExpression::Integer(amount & 63),
            None => binary("&", amount, GoExpression::Integer(63)),
        };
        match operation {
            Operation::Constant(bits) => long_literal(bits, signedness),
            Operation::FromInt | Operation::Convert => typed(long, values.remove(0)),
            Operation::IsUnsigned => GoExpression::Boolean(signedness == Signedness::Unsigned),
            Operation::Add => arithmetic("+", values),
            Operation::Subtract => arithmetic("-", values),
            Operation::Multiply => arithmetic("*", values),
            Operation::Quotient | Operation::Remainder => self.division(operation, values),
            Operation::And => arithmetic("&", values),
            Operation::Or => arithmetic("|", values),
            Operation::Xor => arithmetic("^", values),
            Operation::Negate => negated(values.remove(0)),
            Operation::Not => {
                GoExpression::Unary { operator: "^", operand: Box::new(values.remove(0)) }
            }
            Operation::ShiftLeft => {
                let amount = count(values.remove(1));
                binary("<<", values.remove(0), amount)
            }
            Operation::ShiftRight => {
                let amount = count(values.remove(1));
                match signedness {
                    Signedness::Signed => binary(">>", values.remove(0), amount),
                    Signedness::Unsigned => {
                        let shifted = binary(">>", typed("int64", values.remove(0)), amount);
                        typed("uint64", shifted)
                    }
                }
            }
            Operation::ShiftRightUnsigned => {
                let amount = count(values.remove(1));
                match signedness {
                    Signedness::Signed => {
                        let shifted = binary(">>", typed("uint64", values.remove(0)), amount);
                        typed("int64", shifted)
                    }
                    Signedness::Unsigned => binary(">>", values.remove(0), amount),
                }
            }
            Operation::Compare(comparison) => arithmetic(comparison_symbol(comparison), values),
            Operation::IsZero => binary("==", values.remove(0), GoExpression::Integer(0)),
            Operation::IsEven | Operation::IsOdd => {
                let low = binary("&", values.remove(0), GoExpression::Integer(1));
                let parity = i64::from(operation == Operation::IsOdd);
                binary("==", low, GoExpression::Integer(parity))
            }
            Operation::IsNegative => match signedness {
                Signedness::Signed => binary("<", values.remove(0), GoExpression::Integer(0)),
                Signedness::Unsigned => GoExpression::Boolean(false),
            },
            Operation::IsPositive => match signedness {
                Signedness::Signed => binary(">=", values.remove(0), GoExpression::Integer(0)),
                Signedness::Unsigned => GoExpression::Boolean(true),
            },
            // long.js's toInt is the low 32 bits, sign and all.
            Operation::ToInt => GoExpression::Conversion {
                type_: GoType::Int,
                value: Box::new(typed("int32", values.remove(0))),
            },
            Operation::ToNumber => GoExpression::Conversion {
                type_: GoType::Float64,
                value: Box::new(values.remove(0)),
            },
            Operation::HighBits { unsigned } => {
                let high = binary(">>", values.remove(0), GoExpression::Integer(32));
                let half = typed(if unsigned { "uint32" } else { "int32" }, high);
                GoExpression::Conversion { type_: GoType::Float64, value: Box::new(half) }
            }
            Operation::LowBits { unsigned } => {
                let half = typed(if unsigned { "uint32" } else { "int32" }, values.remove(0));
                GoExpression::Conversion { type_: GoType::Float64, value: Box::new(half) }
            }
            Operation::Same => values.remove(0),
        }
    }

    /// The operation on constant operands, worked out as long.js would at run time.
    fn folded(
        &mut self,
        operation: Int64Operation,
        signedness: Signedness,
        constants: &[i64],
    ) -> Option<GoExpression> {
        Some(match operation.evaluate(signedness, constants)? {
            Int64Value::Long(bits) => long_literal(bits, signedness),
            Int64Value::Boolean(value) => GoExpression::Boolean(value),
            Int64Value::Int(value) => GoExpression::Integer(i64::from(value)),
            Int64Value::Number(value) => self.number_constant(value),
        })
    }

    /// `divide_` or `modulo_`: Go's own operator where the divisor is a
    /// constant other than zero, and otherwise the runtime's, which throws
    /// for zero as long.js does.
    fn division(&mut self, operation: Int64Operation, values: Vec<GoExpression>) -> GoExpression {
        let (operator, runtime) = match operation {
            Int64Operation::Quotient => ("/", "Divide_"),
            _ => ("%", "Modulo_"),
        };
        if long_constant(&values[1]).is_some_and(|divisor| divisor != 0) {
            return arithmetic(operator, values);
        }
        let function = self.go_function(GoFunction { package: GoPackage::Int64, name: runtime });
        GoExpression::Call { function: Box::new(function), arguments: values }
    }
}

/// A binary operator on a Long and a Long, or a Long and a constant, whose
/// constant Go gives the other operand's type.
fn arithmetic(operator: &'static str, mut values: Vec<GoExpression>) -> GoExpression {
    let right = values.pop().expect("invariant violated: binary operator arity");
    let left = values.pop().expect("invariant violated: binary operator arity");
    let (left, right) = match (long_constant(&left).is_some(), long_constant(&right).is_some()) {
        (true, false) => (untyped(left), right),
        (false, true) => (left, untyped(right)),
        _ => (left, right),
    };
    binary(operator, left, right)
}

fn comparison_symbol(comparison: Comparison) -> &'static str {
    match comparison {
        Comparison::Equal => "==",
        Comparison::NotEqual => "!=",
        Comparison::LessThan => "<",
        Comparison::LessThanOrEqual => "<=",
        Comparison::GreaterThan | Comparison::GreaterThanOrUnordered => ">",
        Comparison::GreaterThanOrEqual | Comparison::GreaterThanOrEqualOrUnordered => ">=",
    }
}

/// `int64(-5)` or `uint64(18446744073709551615)`: a Long constant of these bits.
fn long_literal(bits: i64, signedness: Signedness) -> GoExpression {
    let digits = match signedness {
        Signedness::Signed => bits.to_string(),
        Signedness::Unsigned => (bits as u64).to_string(),
    };
    GoExpression::Conversion {
        type_: GoType::Named(signedness.go_type().into()),
        value: Box::new(GoExpression::Identifier(digits)),
    }
}

/// The bits of a constant `long_literal` wrote.
fn long_constant(expression: &GoExpression) -> Option<i64> {
    let GoExpression::Conversion { type_: GoType::Named(type_), value } = expression else {
        return None;
    };
    let GoExpression::Identifier(digits) = value.as_ref() else { return None };
    match type_.as_str() {
        "int64" => digits.parse().ok(),
        "uint64" => digits.parse::<u64>().ok().map(|bits| bits as i64),
        _ => None,
    }
}

/// A Long constant as an untyped Go constant, which takes the type of the
/// Long it meets.
fn untyped(expression: GoExpression) -> GoExpression {
    match &expression {
        GoExpression::Conversion { type_: GoType::Named(_), value }
            if long_constant(&expression).is_some() =>
        {
            let GoExpression::Identifier(digits) = value.as_ref() else { unreachable!() };
            match digits.parse::<i64>() {
                Ok(value) => GoExpression::Integer(value),
                Err(_) => GoExpression::Identifier(digits.clone()),
            }
        }
        _ => expression,
    }
}

fn int_value(expression: &GoExpression) -> Option<i64> {
    match expression {
        GoExpression::Integer(value) => Some(*value),
        GoExpression::Unary { operator: "-", operand } => match operand.as_ref() {
            GoExpression::Integer(value) => value.checked_neg(),
            _ => None,
        },
        _ => None,
    }
}
