use super::{Emitter, binary, call, identifier_expression, negated};
use crate::foreign::{Comparison, GoPackage, Operator};
use crate::monotype::{Monotype, MonotypeId};
use crate::numeric::fold_bitwise;
use crate::syntax::{GoExpression, GoType};

impl<'q, Q> Emitter<'_, '_, 'q, Q>
where
    Q: checking::ExternalQueries,
{
    /// go-support represents PureScript `Int` as Go `int`; generated code uses
    /// `int32`, whose overflow wraps exactly like JavaScript's `| 0`.
    pub(super) fn narrow(&mut self, value: GoExpression, monotype: MonotypeId) -> GoExpression {
        if let Monotype::Int = self.monotypes.get(monotype) {
            return GoExpression::Conversion {
                type_: GoType::Named("int32".into()),
                value: Box::new(value),
            };
        }
        value
    }

    fn fold_number(
        &mut self,
        operator: Operator,
        left: &GoExpression,
        right: &GoExpression,
    ) -> Option<GoExpression> {
        let fold: fn(f64, f64) -> f64 = match operator {
            Operator::NumberAdd => |left, right| left + right,
            Operator::NumberSubtract => |left, right| left - right,
            Operator::NumberMultiply => |left, right| left * right,
            Operator::NumberDivide => |left, right| left / right,
            _ => return None,
        };
        let folded = fold(float_constant(left)?, float_constant(right)?);
        Some(self.number_constant(folded))
    }

    pub(super) fn number_constant(&mut self, value: f64) -> GoExpression {
        let math =
            |name: &str| GoExpression::Qualified { package: "math".into(), name: name.into() };
        if value.is_nan() {
            self.imports.insert("math".into());
            return call(math("NaN"), vec![]);
        }
        if value.is_infinite() {
            self.imports.insert("math".into());
            let sign = if value < 0.0 { -1 } else { 1 };
            return call(math("Inf"), vec![GoExpression::Integer(sign)]);
        }
        if value == 0.0 && value.is_sign_negative() {
            self.imports.insert("math".into());
            let zero = GoExpression::Integer(0);
            return call(math("Copysign"), vec![zero, GoExpression::Integer(-1)]);
        }
        GoExpression::Float(format!("{value:?}"))
    }

    pub(super) fn string_ordering(
        &mut self,
        comparison: Comparison,
        values: Vec<GoExpression>,
    ) -> GoExpression {
        // Go orders strings by their UTF-8 bytes, which is the order of code points; PureScript
        // by UTF-16 code units, which agrees but between a character past U+FFFF and one from
        // U+E000. Text below U+D800 has neither, so each order meets it the same way.
        let below_surrogates = |value: &GoExpression| matches!(value, GoExpression::String(text) if text.chars().all(|character| character <= '\u{D7FF}'));
        if values.iter().any(below_surrogates) {
            return self.operator(Operator::Compare(comparison), values);
        }
        let package = GoPackage::Prim;
        self.imports.insert(package.path().into());
        let function = GoExpression::Qualified {
            package: package.name().into(),
            name: "CompareString".into(),
        };
        let ordering = call(function, values);
        let zero = GoExpression::Integer(0);
        self.operator(Operator::Compare(comparison), vec![ordering, zero])
    }

    pub(super) fn operator(
        &mut self,
        operator: Operator,
        mut values: Vec<GoExpression>,
    ) -> GoExpression {
        let unary = |operator: &'static str, values: &mut Vec<GoExpression>| GoExpression::Unary {
            operator,
            operand: Box::new(values.remove(0)),
        };
        if operator.arity() == 1 {
            return match operator {
                Operator::NumberNegate => match float_constant(&values[0]) {
                    Some(value) => self.number_constant(-value),
                    None => negated(values.remove(0)),
                },
                Operator::IntNegate => match int32_constant(&values[0]) {
                    Some(value) => GoExpression::Integer(i64::from(value.wrapping_neg())),
                    None => negated(values.remove(0)),
                },
                Operator::BooleanNot => unary("!", &mut values),
                Operator::ArrayLength => GoExpression::Conversion {
                    type_: GoType::Named("int32".into()),
                    value: Box::new(call(identifier_expression("len"), values)),
                },
                Operator::IntToNumber => GoExpression::Conversion {
                    type_: GoType::Float64,
                    value: Box::new(values.remove(0)),
                },
                Operator::IntComplement => unary("^", &mut values),
                _ => unreachable!(),
            };
        }
        let right = values.pop().expect("invariant violated: binary operator arity");
        let left = values.pop().expect("invariant violated: binary operator arity");
        if let Operator::ArrayIndex = operator {
            return GoExpression::Index { value: Box::new(left), index: Box::new(right) };
        }
        if let Operator::StringAppend = operator {
            return self.string_append(left, right);
        }
        if let Some(bitwise) = bitwise(operator, left.clone(), right.clone()) {
            return bitwise;
        }
        if let Operator::IntMultiply = operator {
            // int32 multiplication wraps, as PureScript's Int does.
            if let (Some(x), Some(y)) = (int32_constant(&left), int32_constant(&right)) {
                return GoExpression::Integer(i64::from(x.wrapping_mul(y)));
            }
            return binary("*", left, right);
        }
        if let Some(folded) = self.fold_number(operator, &left, &right) {
            return folded;
        }
        if let Operator::NumberDivide = operator
            && is_untyped_constant(&left)
            && is_untyped_constant(&right)
        {
            let left = GoExpression::Conversion { type_: GoType::Float64, value: Box::new(left) };
            return binary("/", left, right);
        }
        // Go folds untyped constants exactly; JavaScript rounds every step.
        let left = match operator {
            Operator::NumberAdd | Operator::NumberSubtract | Operator::NumberMultiply
                if is_untyped_constant(&left) && is_untyped_constant(&right) =>
            {
                GoExpression::Conversion { type_: GoType::Float64, value: Box::new(left) }
            }
            _ => left,
        };
        let negated_opposite = match operator {
            Operator::Compare(Comparison::GreaterThanOrUnordered) => Some("<="),
            Operator::Compare(Comparison::GreaterThanOrEqualOrUnordered) => Some("<"),
            _ => None,
        };
        if let Some(opposite) = negated_opposite {
            let opposite = binary(opposite, left, right);
            return GoExpression::Unary { operator: "!", operand: Box::new(opposite) };
        }
        let symbol = match operator {
            Operator::IntAdd | Operator::NumberAdd | Operator::StringAppend => "+",
            Operator::IntSubtract | Operator::NumberSubtract => "-",
            Operator::NumberMultiply => "*",
            Operator::NumberDivide => "/",
            Operator::BooleanAnd => "&&",
            Operator::BooleanOr => "||",
            Operator::Compare(comparison) => match comparison {
                Comparison::Equal => "==",
                Comparison::NotEqual => "!=",
                Comparison::LessThan => "<",
                Comparison::LessThanOrEqual => "<=",
                Comparison::GreaterThan => ">",
                Comparison::GreaterThanOrEqual => ">=",
                Comparison::GreaterThanOrUnordered | Comparison::GreaterThanOrEqualOrUnordered => {
                    unreachable!()
                }
            },
            _ => unreachable!(),
        };
        binary(symbol, left, right)
    }
}

/// The Data.Int.Bits operators, which follow JavaScript: operands are int32 and
/// shift counts are taken modulo 32. Constant operands are folded so that Go never
/// sees an untyped constant overflow int32 or uint32.
fn bitwise(operator: Operator, left: GoExpression, right: GoExpression) -> Option<GoExpression> {
    let symbol = match operator {
        Operator::IntAnd => "&",
        Operator::IntOr => "|",
        Operator::IntXor => "^",
        Operator::IntShiftLeft => "<<",
        Operator::IntShiftRight | Operator::IntZeroFillShiftRight => ">>",
        _ => return None,
    };
    if let (Some(x), Some(y)) = (int32_constant(&left), int32_constant(&right)) {
        return Some(GoExpression::Integer(fold_bitwise(operator, x, y)));
    }
    let shifts = !matches!(operator, Operator::IntAnd | Operator::IntOr | Operator::IntXor);
    if !shifts {
        return Some(binary(symbol, left, right));
    }
    let count = match int32_constant(&right) {
        Some(count) => GoExpression::Integer(i64::from(count & 31)),
        None => binary("&", right, GoExpression::Integer(31)),
    };
    let int32 = || GoType::Named("int32".into());
    if let Operator::IntZeroFillShiftRight = operator {
        let unsigned = match int32_constant(&left) {
            Some(x) => GoExpression::Integer(i64::from(x as u32)),
            None => left,
        };
        let unsigned = GoExpression::Conversion {
            type_: GoType::Named("uint32".into()),
            value: Box::new(unsigned),
        };
        return Some(GoExpression::Conversion {
            type_: int32(),
            value: Box::new(binary(symbol, unsigned, count)),
        });
    }
    let left = match is_untyped_constant(&left) {
        true => GoExpression::Conversion { type_: int32(), value: Box::new(left) },
        false => left,
    };
    Some(binary(symbol, left, count))
}

pub(super) fn float_constant(expression: &GoExpression) -> Option<f64> {
    match expression {
        GoExpression::Integer(value) => Some(*value as f64),
        GoExpression::Float(value) => value.parse().ok(),
        GoExpression::Unary { operator: "-", operand } => {
            float_constant(operand).map(|value| -value)
        }
        _ => None,
    }
}

fn int32_constant(expression: &GoExpression) -> Option<i32> {
    match expression {
        GoExpression::Integer(value) => i32::try_from(*value).ok(),
        GoExpression::Unary { operator: "-", operand } => match operand.as_ref() {
            GoExpression::Integer(value) => i32::try_from(-*value).ok(),
            _ => None,
        },
        _ => None,
    }
}

pub(super) fn is_untyped_constant(expression: &GoExpression) -> bool {
    match expression {
        GoExpression::Integer(_) | GoExpression::Float(_) | GoExpression::Rune(_) => true,
        GoExpression::Identifier(name) => name == "nil",
        GoExpression::Unary { operand, .. } => is_untyped_constant(operand),
        GoExpression::Binary { left, right, .. } => {
            is_untyped_constant(left) && is_untyped_constant(right)
        }
        _ => false,
    }
}
