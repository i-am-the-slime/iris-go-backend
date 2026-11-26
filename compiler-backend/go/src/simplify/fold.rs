//! Operators over literals, evaluated at compile time exactly as JavaScript
//! evaluates them at run time: `Int` wraps like `|0`, `Number` is IEEE double
//! arithmetic, and strings compare by UTF-16 code units. Folding exposes the
//! conditions that inlining makes constant, such as an index check against a
//! literal index, so that the choices they guard disappear.

use std::cmp::Ordering;

use super::Simplifier;
use crate::foreign::{self, Comparison, Foreign, Operator};
use crate::monomorphic::{
    Alternative, Expression, ExpressionKind, Guarded, Literal, Pattern, PatternKind,
};
use crate::monotype::{Monotype, MonotypeId};
use crate::primitives::{Int64Operation, Int64Value};
use crate::purity::is_discardable;

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

    /// A Long operation, worked out when its operands are constants, so that
    /// a `let` of one inlines and the zero test of a constant divisor goes.
    pub(super) fn int64_operation(
        &mut self,
        foreign: &'static Foreign,
        arguments: Vec<Expression>,
        monotype: MonotypeId,
    ) -> Expression {
        let Foreign::Int64 { operation, signedness } = *foreign else {
            unreachable!("invariant violated: a Long operation is an Int64 foreign")
        };
        let operands: Option<Vec<i64>> = match (operation, arguments.as_slice()) {
            // `fromInt_ i flag`'s flag is the signedness the foreign already has.
            (Int64Operation::FromInt, [integer, flags @ ..]) => match integer.kind {
                ExpressionKind::Literal(Literal::Int(value))
                    if flags.iter().all(is_discardable) =>
                {
                    Some(vec![value])
                }
                _ => None,
            },
            _ => arguments.iter().map(long_constant).collect(),
        };
        let value = operands.and_then(|operands| operation.evaluate(signedness, &operands));
        let kind = match value {
            Some(Int64Value::Long(bits)) => {
                let operation = Int64Operation::Constant(bits);
                let foreign = Foreign::Int64 { operation, signedness }.interned();
                ExpressionKind::Foreign { foreign, arguments: vec![] }
            }
            Some(Int64Value::Boolean(value)) => ExpressionKind::Literal(Literal::Boolean(value)),
            Some(Int64Value::Int(value)) => ExpressionKind::Literal(Literal::Int(i64::from(value))),
            Some(Int64Value::Number(value)) => {
                ExpressionKind::Literal(Literal::Number(format!("{value:?}").into()))
            }
            None => ExpressionKind::Foreign { foreign, arguments },
        };
        Expression::new(kind, monotype)
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
        // `if a then x else if b then x else y` is `if a || b then x else y`; a boolean `x` is
        // left to `plain_choice`, which writes the whole choice as one condition.
        if shares_branch_with_next(&condition, &then, &otherwise)
            && let ExpressionKind::If { condition: next, otherwise: rest, .. } = &otherwise.kind
        {
            let condition_monotype = condition.monotype;
            let next = (**next).clone();
            let either = self.binary(Operator::BooleanOr, condition, next, condition_monotype);
            let rest = (**rest).clone();
            return self.boolean_choice(either, then, rest, monotype);
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
        if then == otherwise && is_discardable(&condition) {
            return then;
        }
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
            Operator::IntMultiply if is_int(&right, 1) => left,
            Operator::IntMultiply if is_int(&left, 1) => right,
            Operator::IntSubtract if is_int(&right, 0) => left,
            // `b == false` is `not b`, which turns a comparison around.
            Operator::Compare(comparison @ (Comparison::Equal | Comparison::NotEqual))
                if let Some((known, other)) = match (boolean(&left), boolean(&right)) {
                    (Some(known), None) => Some((known, right.clone())),
                    (None, Some(known)) => Some((known, left.clone())),
                    _ => None,
                } =>
            {
                match known == (comparison == Comparison::Equal) {
                    true => other,
                    false => self.not(other, monotype),
                }
            }
            Operator::Compare(comparison) => {
                match self.constructor_test(comparison, &left, &right, monotype) {
                    Some(tested) => tested,
                    None => operation(operator, vec![left, right], monotype),
                }
            }
            _ => operation(operator, vec![left, right], monotype),
        }
    }

    /// A value of an enumeration compared with a constructor, as `enumeration_case` writes
    /// `eq` once inlined: two constructors fold, and a choice of constructors is a case of it,
    /// whose alternatives then choose by what chose the constructor: `compare x y == GT` is
    /// `x > y`.
    fn constructor_test(
        &mut self,
        comparison: Comparison,
        left: &Expression,
        right: &Expression,
        monotype: MonotypeId,
    ) -> Option<Expression> {
        let equal = comparison == Comparison::Equal;
        let constructor = |expression: &Expression| match &expression.kind {
            ExpressionKind::Construct { data, constructor, arguments } if arguments.is_empty() => {
                Some((data.clone(), *constructor))
            }
            _ => None,
        };
        let is_choice = |expression: &Expression| {
            matches!(
                expression.kind,
                ExpressionKind::If { .. }
                    | ExpressionKind::Case { .. }
                    | ExpressionKind::Let { .. }
            )
        };
        let (chosen, (data, index)) = match (constructor(left), constructor(right)) {
            (Some((_, first)), Some((_, second))) => {
                let ordering = first.cmp(&second);
                let holds = match comparison {
                    Comparison::Equal => ordering.is_eq(),
                    Comparison::NotEqual => ordering.is_ne(),
                    Comparison::LessThan => ordering.is_lt(),
                    Comparison::LessThanOrEqual => ordering.is_le(),
                    Comparison::GreaterThan | Comparison::GreaterThanOrUnordered => {
                        ordering.is_gt()
                    }
                    Comparison::GreaterThanOrEqual | Comparison::GreaterThanOrEqualOrUnordered => {
                        ordering.is_ge()
                    }
                };
                return Some(boolean_literal(holds, monotype));
            }
            _ if !matches!(comparison, Comparison::Equal | Comparison::NotEqual) => return None,
            (None, Some(tested)) if is_choice(left) => (left.clone(), tested),
            (Some(tested), None) if is_choice(right) => (right.clone(), tested),
            _ => return None,
        };
        let pattern = |kind| Pattern { kind, monotype: chosen.monotype };
        let tested = PatternKind::Constructor { data, constructor: index, arguments: vec![] };
        let alternative = |pattern, outcome| Alternative {
            patterns: vec![pattern],
            body: Guarded::Unconditional(boolean_literal(outcome, monotype)),
            position: None,
        };
        let alternatives = vec![
            alternative(pattern(tested), equal),
            alternative(pattern(PatternKind::Wildcard), !equal),
        ];
        let kind = ExpressionKind::Case { scrutinees: vec![chosen], alternatives };
        Some(self.expression(Expression::new(kind, monotype)))
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

/// The bits of a constant Long.
fn long_constant(expression: &Expression) -> Option<i64> {
    match &expression.kind {
        ExpressionKind::Foreign {
            foreign: Foreign::Int64 { operation: Int64Operation::Constant(bits), .. },
            ..
        } => Some(*bits),
        _ => None,
    }
}

/// Whether a choice's `else` is a choice whose `then` is the same, so that the two conditions
/// can join under `||`. Not for a boolean `then`, which `plain_choice` writes as one condition
/// instead, nor for two comparisons of the same values, which say more as one comparison.
pub(super) fn shares_branch_with_next(
    condition: &Expression,
    then: &Expression,
    otherwise: &Expression,
) -> bool {
    let ExpressionKind::If { condition: next, then: next_then, .. } = &otherwise.kind else {
        return false;
    };
    boolean(then).is_none() && **next_then == *then && !compare_same_values(condition, next)
}

fn compare_same_values(left: &Expression, right: &Expression) -> bool {
    let operands = |expression: &Expression| match &expression.kind {
        ExpressionKind::Foreign {
            foreign:
                Foreign::Operator(Operator::Compare(_))
                | Foreign::Int64 { operation: Int64Operation::Compare(_), .. },
            arguments,
        } if arguments.len() == 2 => Some((arguments[0].clone(), arguments[1].clone())),
        _ => None,
    };
    match (operands(left), operands(right)) {
        (Some((a, b)), Some((c, d))) => (a == c && b == d) || (a == d && b == c),
        _ => false,
    }
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
        (foreign, [Value::Number(x)]) if foreign.calls(foreign::SHOW_NUMBER) => {
            Value::Owned(show_number(*x))
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
        ) => Value::Int(i32::try_from(crate::numeric::fold_bitwise(operator, *x, *y)).ok()?),
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

/// `show` of a Number: JavaScript's `toString`, with `.0` after a whole number it writes
/// without an exponent, as purescript-prelude's `showNumberImpl` does.
fn show_number(value: f64) -> String {
    if value.is_nan() {
        return "NaN".into();
    }
    if value.is_infinite() {
        return if value < 0.0 { "-Infinity".into() } else { "Infinity".into() };
    }
    if value == 0.0 {
        return "0.0".into();
    }
    let sign = if value < 0.0 { "-" } else { "" };
    // Rust's exponent form spells the shortest digits that read back as the same double.
    let scientific = format!("{:e}", value.abs());
    let (mantissa, exponent) = scientific.split_once('e').expect("an exponent");
    let digits: String = mantissa.chars().filter(char::is_ascii_digit).collect();
    let point = exponent.parse::<i32>().expect("a decimal exponent") + 1;
    let count = digits.len() as i32;
    let written = if count <= point && point <= 21 {
        format!("{digits}{}.0", "0".repeat((point - count) as usize))
    } else if 0 < point && point <= 21 {
        let (whole, fraction) = digits.split_at(point as usize);
        format!("{whole}.{fraction}")
    } else if -6 < point && point <= 0 {
        format!("0.{}{digits}", "0".repeat((-point) as usize))
    } else {
        let (first, rest) = digits.split_at(1);
        let rest = if rest.is_empty() { String::new() } else { format!(".{rest}") };
        let exponent = point - 1;
        let exponent_sign = if exponent < 0 { '-' } else { '+' };
        format!("{first}{rest}e{exponent_sign}{}", exponent.abs())
    };
    format!("{sign}{written}")
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

fn is_int(expression: &Expression, value: i64) -> bool {
    matches!(expression.kind, ExpressionKind::Literal(Literal::Int(literal)) if literal == value)
}

#[cfg(test)]
mod tests {
    use super::show_number;

    #[test]
    fn numbers_show_as_javascript_writes_them() {
        assert_eq!(show_number(1.5), "1.5");
        assert_eq!(show_number(-2.0), "-2.0");
        assert_eq!(show_number(-0.0), "0.0");
        assert_eq!(show_number(100.0), "100.0");
        assert_eq!(show_number(0.1 + 0.2), "0.30000000000000004");
        assert_eq!(show_number(0.000001), "0.000001");
        assert_eq!(show_number(1.5e-7), "1.5e-7");
        assert_eq!(show_number(123456789012345680000.0), "123456789012345680000.0");
        assert_eq!(show_number(1e21), "1e+21");
        assert_eq!(show_number(-1.25e300), "-1.25e+300");
        assert_eq!(show_number(f64::INFINITY), "Infinity");
        assert_eq!(show_number(f64::NEG_INFINITY), "-Infinity");
        assert_eq!(show_number(f64::NAN), "NaN");
    }
}
