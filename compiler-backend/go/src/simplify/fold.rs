//! Operators over literals, evaluated at compile time exactly as JavaScript
//! evaluates them at run time: `Int` wraps like `|0`, `Number` is IEEE double
//! arithmetic, and strings compare by UTF-16 code units. Folding exposes the
//! conditions that inlining makes constant, such as an index check against a
//! literal index, so that the choices they guard disappear.

use std::cmp::Ordering;

use super::{Simplifier, is_discardable};
use crate::foreign::{self, Comparison, Foreign, Operator};
use crate::mono::{Expression, ExpressionKind, Literal};
use crate::monotype::{Monotype, MonotypeId};
use crate::primitives::Int64Operation;

impl Simplifier<'_> {
    /// An operator application, folded when its operands are literals and
    /// otherwise rewritten by the identities that hold for every operand.
    pub(super) fn operator(
        &mut self,
        foreign: &'static Foreign,
        arguments: Vec<Expression>,
        monotype: MonotypeId,
    ) -> Expression {
        if let Some(literal) = evaluate(*foreign, &arguments) {
            return Expression::new(ExpressionKind::Literal(literal), monotype);
        }
        let Foreign::Operator(operator) = *foreign else {
            return Expression::new(ExpressionKind::Foreign { foreign, arguments }, monotype);
        };
        match (operator, <[Expression; 1]>::try_from(arguments)) {
            (Operator::BooleanNot, Ok([operand])) => self.not(operand, monotype),
            (_, Ok(arguments)) => operation(operator, arguments.into(), monotype),
            (_, Err(arguments)) => {
                let [left, right] = <[Expression; 2]>::try_from(arguments)
                    .unwrap_or_else(|_| unreachable!("invariant violated: operator arity"));
                self.binary(operator, left, right, monotype)
            }
        }
    }

    /// `if c then true else false` is `c`, and with the branches swapped it is
    /// `not c`; choices by comparisons of the same two values join where they
    /// choose the same, as `joined_comparisons` says.
    pub(super) fn boolean_choice(
        &mut self,
        condition: Expression,
        then: Expression,
        otherwise: Expression,
        monotype: MonotypeId,
    ) -> Expression {
        if let Some(joined) = self.joined_comparisons(&condition, &then, &otherwise, monotype) {
            return joined;
        }
        self.plain_choice(condition, then, otherwise, monotype)
    }

    /// `boolean_choice` without joining choices by comparisons.
    pub(super) fn plain_choice(
        &mut self,
        condition: Expression,
        then: Expression,
        otherwise: Expression,
        monotype: MonotypeId,
    ) -> Expression {
        match (boolean(&then), boolean(&otherwise)) {
            (Some(true), Some(false)) => condition,
            (Some(false), Some(true)) => self.not(condition, monotype),
            _ => {
                let kind = ExpressionKind::If {
                    condition: Box::new(condition),
                    then: Box::new(then),
                    otherwise: Box::new(otherwise),
                };
                Expression::new(kind, monotype)
            }
        }
    }

    fn not(&mut self, operand: Expression, monotype: MonotypeId) -> Expression {
        if let Some(value) = boolean(&operand) {
            return boolean_literal(!value, monotype);
        }
        match operand.kind {
            ExpressionKind::Foreign {
                foreign: Foreign::Operator(Operator::BooleanNot),
                mut arguments,
            } => arguments.pop().expect("invariant violated: not has one argument"),
            ExpressionKind::Foreign {
                foreign: Foreign::Operator(Operator::Compare(comparison)),
                arguments,
            } if let Some(negated) = self.negated(*comparison, &arguments[0]) => {
                operation(Operator::Compare(negated), arguments, monotype)
            }
            // Longs are totally ordered, so every comparison of them has a negation.
            ExpressionKind::Foreign {
                foreign:
                    Foreign::Int64 { operation: Int64Operation::Compare(comparison), signedness },
                arguments,
            } if let Some(negated) = self.negated(*comparison, &arguments[0]) => {
                let operation = Int64Operation::Compare(negated);
                let foreign = Foreign::Int64 { operation, signedness: *signedness }.interned();
                Expression::new(ExpressionKind::Foreign { foreign, arguments }, monotype)
            }
            kind => {
                let operand = Expression::new(kind, operand.monotype);
                operation(Operator::BooleanNot, vec![operand], monotype)
            }
        }
    }

    /// The comparison that holds exactly when `comparison` does not. Ordering
    /// comparisons of numbers have none: every one of them is false for NaN.
    fn negated(&self, comparison: Comparison, operand: &Expression) -> Option<Comparison> {
        let ordered = !matches!(self.monotypes.get(operand.monotype), Monotype::Number);
        match comparison {
            Comparison::Equal => Some(Comparison::NotEqual),
            Comparison::NotEqual => Some(Comparison::Equal),
            Comparison::LessThan if ordered => Some(Comparison::GreaterThanOrEqual),
            Comparison::LessThanOrEqual if ordered => Some(Comparison::GreaterThan),
            Comparison::GreaterThan if ordered => Some(Comparison::LessThanOrEqual),
            Comparison::GreaterThanOrEqual if ordered => Some(Comparison::LessThan),
            Comparison::LessThan => Some(Comparison::GreaterThanOrEqualOrUnordered),
            Comparison::LessThanOrEqual => Some(Comparison::GreaterThanOrUnordered),
            Comparison::GreaterThanOrUnordered => Some(Comparison::LessThanOrEqual),
            Comparison::GreaterThanOrEqualOrUnordered => Some(Comparison::LessThan),
            _ => None,
        }
    }

    fn binary(
        &mut self,
        operator: Operator,
        left: Expression,
        right: Expression,
        monotype: MonotypeId,
    ) -> Expression {
        match operator {
            Operator::BooleanAnd => match (boolean(&left), boolean(&right)) {
                (Some(true), _) => right,
                (_, Some(true)) | (Some(false), _) => left,
                (_, Some(false)) if is_discardable(&left) => right,
                _ => operation(operator, vec![left, right], monotype),
            },
            Operator::BooleanOr => match (boolean(&left), boolean(&right)) {
                (Some(false), _) => right,
                (_, Some(false)) | (Some(true), _) => left,
                (_, Some(true)) if is_discardable(&left) => right,
                _ => operation(operator, vec![left, right], monotype),
            },
            Operator::IntAdd | Operator::StringAppend => associate(operator, left, right, monotype),
            _ => operation(operator, vec![left, right], monotype),
        }
    }
}

/// Addition and appending are associative, so literals that meet once
/// the nesting is ignored combine: `(x <> "a") <> "b"` is `x <> "ab"`.
/// Addition is also commutative, so all its literals combine: `(1 + x) + 2`
/// is `x + 3`. A zero or an empty string drops out.
fn associate(
    operator: Operator,
    left: Expression,
    right: Expression,
    monotype: MonotypeId,
) -> Expression {
    if is_identity(&left) {
        return right;
    }
    if is_identity(&right) {
        return left;
    }
    let commutative = operator == Operator::IntAdd;
    let mut operands = vec![];
    flatten(operator, left, &mut operands);
    flatten(operator, right, &mut operands);
    if commutative && operands.iter().filter(|operand| is_literal(operand)).count() > 1 {
        let (literals, mut operands): (Vec<_>, Vec<_>) = operands.into_iter().partition(is_literal);
        operands.extend(combine_literals(operator, literals, monotype));
        return nest(operator, operands, monotype);
    }
    let mut combined: Vec<Expression> = Vec::with_capacity(operands.len());
    for operand in operands {
        match combined.pop() {
            Some(previous) if is_literal(&previous) && is_literal(&operand) => {
                combined.extend(combine_literals(operator, vec![previous, operand], monotype));
            }
            Some(previous) => combined.extend([previous, operand]),
            None => combined.push(operand),
        }
    }
    nest(operator, combined, monotype)
}

/// The operands of a chain of one operator, in order.
fn flatten(operator: Operator, expression: Expression, operands: &mut Vec<Expression>) {
    match expression.kind {
        ExpressionKind::Foreign { foreign: Foreign::Operator(inner), arguments }
            if *inner == operator =>
        {
            for argument in arguments {
                flatten(operator, argument, operands);
            }
        }
        kind => operands.push(Expression::new(kind, expression.monotype)),
    }
}

/// The literals evaluated into one, or left apart when that is not exact.
fn combine_literals(
    operator: Operator,
    literals: Vec<Expression>,
    monotype: MonotypeId,
) -> Vec<Expression> {
    let mut literals = literals.into_iter();
    let Some(first) = literals.next() else { return vec![] };
    let mut kept = vec![first];
    for literal in literals {
        let previous = kept.pop().expect("invariant violated: a literal was kept");
        let pair = [previous, literal];
        match evaluate(Foreign::Operator(operator), &pair) {
            Some(value) => kept.push(Expression::new(ExpressionKind::Literal(value), monotype)),
            None => kept.extend(pair),
        }
    }
    kept
}

/// A left-nested chain of one operator, as the source writes `a + b + c`.
fn nest(operator: Operator, operands: Vec<Expression>, monotype: MonotypeId) -> Expression {
    let mut operands = operands.into_iter();
    let first = operands.next().expect("invariant violated: an operation has operands");
    operands.fold(first, |left, right| {
        if is_identity(&right) {
            return left;
        }
        operation(operator, vec![left, right], monotype)
    })
}

fn operation(operator: Operator, arguments: Vec<Expression>, monotype: MonotypeId) -> Expression {
    let foreign = Foreign::Operator(operator).interned();
    Expression::new(ExpressionKind::Foreign { foreign, arguments }, monotype)
}

fn boolean(expression: &Expression) -> Option<bool> {
    match expression.kind {
        ExpressionKind::Literal(Literal::Boolean(value)) => Some(value),
        _ => None,
    }
}

fn boolean_literal(value: bool, monotype: MonotypeId) -> Expression {
    Expression::new(ExpressionKind::Literal(Literal::Boolean(value)), monotype)
}

fn is_literal(expression: &Expression) -> bool {
    matches!(expression.kind, ExpressionKind::Literal(_))
}

fn is_identity(expression: &Expression) -> bool {
    match &expression.kind {
        ExpressionKind::Literal(Literal::Int(value)) => *value == 0,
        ExpressionKind::Literal(Literal::String(value)) => value.is_empty(),
        _ => false,
    }
}

/// The literal an operation on literals evaluates to, when it has one that
/// the generated Go reproduces exactly.
fn evaluate(foreign: Foreign, arguments: &[Expression]) -> Option<Literal> {
    let mut literals = Vec::with_capacity(arguments.len());
    for argument in arguments {
        let ExpressionKind::Literal(literal) = &argument.kind else { return None };
        literals.push(Value::of(literal)?);
    }
    let result = match (foreign, literals.as_slice()) {
        (foreign, [Value::Int(x), Value::Int(y)]) if foreign.calls(foreign::INT_DIVIDE) => {
            Value::Int(divide(*x, *y)?)
        }
        (foreign, [Value::Int(x), Value::Int(y)]) if foreign.calls(foreign::INT_MODULO) => {
            Value::Int(modulo(*x, *y))
        }
        (Foreign::Operator(operator), [operand]) => unary(operator, operand)?,
        (Foreign::Operator(Operator::Compare(comparison)), [left, right]) => {
            Value::Boolean(compare(comparison, left, right)?)
        }
        (Foreign::Operator(operator), [left, right]) => binary(operator, left, right)?,
        _ => return None,
    };
    Some(result.literal())
}

/// A literal as the value JavaScript computes with.
#[derive(Clone)]
enum Value<'l> {
    Int(i32),
    Number(f64),
    Boolean(bool),
    Char(char),
    String(&'l str),
    Owned(String),
}

impl<'l> Value<'l> {
    fn of(literal: &'l Literal) -> Option<Value<'l>> {
        Some(match literal {
            // The one Int literal outside the range, 2147483648, is negated:
            // `-2147483648` is `negate 2147483648`, and both wrap alike.
            Literal::Int(value) => Value::Int(*value as i32),
            Literal::Number(value) => Value::Number(value.parse().ok()?),
            Literal::Boolean(value) => Value::Boolean(*value),
            Literal::Char(value) => Value::Char(*value),
            // Folding works on Rust strings, which cannot hold a lone surrogate.
            Literal::Utf16(_) => return None,
            Literal::String(value) => Value::String(value),
        })
    }

    fn literal(self) -> Literal {
        match self {
            Value::Int(value) => Literal::Int(i64::from(value)),
            // Debug formatting is the shortest text that parses back to the
            // same double, `-0.0` and `NaN` included.
            Value::Number(value) => Literal::Number(format!("{value:?}").into()),
            Value::Boolean(value) => Literal::Boolean(value),
            Value::Char(value) => Literal::Char(value),
            Value::String(value) => Literal::String(value.to_string()),
            Value::Owned(value) => Literal::String(value),
        }
    }

    fn text(&self) -> Option<&str> {
        match self {
            Value::String(value) => Some(value),
            Value::Owned(value) => Some(value),
            _ => None,
        }
    }
}

fn unary<'l>(operator: Operator, operand: &Value<'l>) -> Option<Value<'l>> {
    Some(match (operator, operand) {
        (Operator::IntNegate, Value::Int(x)) => Value::Int(x.wrapping_neg()),
        (Operator::IntComplement, Value::Int(x)) => Value::Int(!x),
        (Operator::IntToNumber, Value::Int(x)) => Value::Number(f64::from(*x)),
        (Operator::NumberNegate, Value::Number(x)) => Value::Number(-x),
        (Operator::BooleanNot, Value::Boolean(x)) => Value::Boolean(!x),
        _ => return None,
    })
}

fn binary<'l>(operator: Operator, left: &Value<'l>, right: &Value<'l>) -> Option<Value<'l>> {
    Some(match (operator, left, right) {
        (Operator::IntAdd, Value::Int(x), Value::Int(y)) => Value::Int(x.wrapping_add(*y)),
        (Operator::IntSubtract, Value::Int(x), Value::Int(y)) => Value::Int(x.wrapping_sub(*y)),
        (Operator::IntMultiply, Value::Int(x), Value::Int(y)) => Value::Int(x.wrapping_mul(*y)),
        (
            Operator::IntAnd
            | Operator::IntOr
            | Operator::IntXor
            | Operator::IntShiftLeft
            | Operator::IntShiftRight
            | Operator::IntZeroFillShiftRight,
            Value::Int(x),
            Value::Int(y),
        ) => Value::Int(i32::try_from(crate::emit::fold_bitwise(operator, *x, *y)).ok()?),
        (Operator::NumberAdd, Value::Number(x), Value::Number(y)) => Value::Number(x + y),
        (Operator::NumberSubtract, Value::Number(x), Value::Number(y)) => Value::Number(x - y),
        (Operator::NumberMultiply, Value::Number(x), Value::Number(y)) => Value::Number(x * y),
        (Operator::NumberDivide, Value::Number(x), Value::Number(y)) => Value::Number(x / y),
        (Operator::BooleanAnd, Value::Boolean(x), Value::Boolean(y)) => Value::Boolean(*x && *y),
        (Operator::BooleanOr, Value::Boolean(x), Value::Boolean(y)) => Value::Boolean(*x || *y),
        (Operator::StringAppend, left, right) => {
            Value::Owned([left.text()?, right.text()?].concat())
        }
        _ => return None,
    })
}

/// `x * y | 0`: the product is a double, exact up to 2^53 and rounded beyond.
/// The prelude's `intDiv`, Euclidean division with zero for a zero divisor.
/// `minBound / -1` leaves the Int range in JavaScript and stays unfolded.
fn divide(x: i32, y: i32) -> Option<i32> {
    if y == 0 {
        return Some(0);
    }
    i32::try_from(i64::from(x).div_euclid(i64::from(y))).ok()
}

/// The prelude's `intMod`, never negative, with zero for a zero divisor.
fn modulo(x: i32, y: i32) -> i32 {
    if y == 0 {
        return 0;
    }
    i64::from(x).rem_euclid(i64::from(y)) as i32
}

#[allow(clippy::neg_cmp_op_on_partial_ord)]
fn compare(comparison: Comparison, left: &Value<'_>, right: &Value<'_>) -> Option<bool> {
    if let (Value::Number(x), Value::Number(y)) = (left, right) {
        // IEEE comparisons, under which NaN is unordered and -0 equals 0.
        return Some(match comparison {
            Comparison::Equal => x == y,
            Comparison::NotEqual => x != y,
            Comparison::LessThan => x < y,
            Comparison::LessThanOrEqual => x <= y,
            Comparison::GreaterThan => x > y,
            Comparison::GreaterThanOrEqual => x >= y,
            Comparison::GreaterThanOrUnordered => !(x <= y),
            Comparison::GreaterThanOrEqualOrUnordered => !(x < y),
        });
    }
    let ordering = match (left, right) {
        (Value::Int(x), Value::Int(y)) => x.cmp(y),
        (Value::Boolean(x), Value::Boolean(y)) => x.cmp(y),
        (Value::Char(x), Value::Char(y)) => utf16_order(&x.to_string(), &y.to_string()),
        (left, right) => utf16_order(left.text()?, right.text()?),
    };
    Some(match comparison {
        Comparison::Equal => ordering == Ordering::Equal,
        Comparison::NotEqual => ordering != Ordering::Equal,
        Comparison::LessThan => ordering == Ordering::Less,
        Comparison::LessThanOrEqual => ordering != Ordering::Greater,
        Comparison::GreaterThan | Comparison::GreaterThanOrUnordered => {
            ordering == Ordering::Greater
        }
        Comparison::GreaterThanOrEqual | Comparison::GreaterThanOrEqualOrUnordered => {
            ordering != Ordering::Less
        }
    })
}

fn utf16_order(left: &str, right: &str) -> Ordering {
    left.encode_utf16().cmp(right.encode_utf16())
}
