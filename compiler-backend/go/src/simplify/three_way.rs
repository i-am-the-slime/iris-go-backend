//! A case of a three-way comparison is a choice by comparisons of what it
//! compares. purescript-int64's `compare (Long' x) (Long' y)` is
//! `case compare_ x y of 0 -> EQ; n | n > 0 -> GT; _ -> LT`, which `max`,
//! `min`, `<` and every other member of `Ord` meet once inlined; where the
//! Go type of `x` and `y` orders as PureScript does, the case is `x < y`,
//! `x == y` and `x > y`:
//!
//! ```go
//! if x >= y { return x }
//! return y
//! ```
//!
//! Each alternative catches the outcomes (less, equal, greater) its pattern
//! and guards admit and the earlier ones left; alternatives with the same body
//! join, and each choice tests the outcomes of its alternative with the one
//! comparison that tells them from those still possible there. Number's order
//! is not Go's for NaN, nor String's (UTF-16 code units, not UTF-8 bytes), so
//! their three-way comparisons stay calls.

use super::Simplifier;
use crate::foreign::{Comparison, Foreign, Operator};
use crate::mono::{
    Alternative, Expression, ExpressionKind, Guard, Guarded, Literal, LocalId, SourcePosition,
};
use crate::monotype::{Monotype, MonotypeId};
use crate::primitives::{Int64Operation, Signedness};
use crate::purity::occurrences;

type OutcomeBranch = (Outcomes, Expression, Option<SourcePosition>);

/// A set of outcomes of a three-way comparison.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Outcomes(u8);

const LESS: Outcomes = Outcomes(1);
const EQUAL: Outcomes = Outcomes(2);
const GREATER: Outcomes = Outcomes(4);
const NONE: Outcomes = Outcomes(0);
const ALL: Outcomes = Outcomes(7);

impl Outcomes {
    fn and(self, other: Outcomes) -> Outcomes {
        Outcomes(self.0 & other.0)
    }

    fn or(self, other: Outcomes) -> Outcomes {
        Outcomes(self.0 | other.0)
    }

    fn without(self, other: Outcomes) -> Outcomes {
        Outcomes(self.0 & !other.0)
    }

    /// The outcomes with the compared values swapped.
    fn swapped(self) -> Outcomes {
        let mut swapped = self.and(EQUAL);
        if self.and(LESS) != NONE {
            swapped = swapped.or(GREATER);
        }
        if self.and(GREATER) != NONE {
            swapped = swapped.or(LESS);
        }
        swapped
    }

    /// The outcomes whose result, -1, 0 or 1, the comparison with `k` admits.
    fn compared(comparison: Comparison, k: i64, result_first: bool) -> Outcomes {
        [(LESS, -1), (EQUAL, 0), (GREATER, 1)]
            .into_iter()
            .filter(|(_, result)| {
                let (left, right) = if result_first { (*result, k) } else { (k, *result) };
                holds(comparison, left, right)
            })
            .fold(NONE, |outcomes, (outcome, _)| outcomes.or(outcome))
    }

    /// The outcomes of a comparison of the compared values.
    fn of(comparison: Comparison) -> Outcomes {
        match comparison {
            Comparison::Equal => EQUAL,
            Comparison::NotEqual => LESS.or(GREATER),
            Comparison::LessThan => LESS,
            Comparison::LessThanOrEqual => LESS.or(EQUAL),
            Comparison::GreaterThan | Comparison::GreaterThanOrUnordered => GREATER,
            Comparison::GreaterThanOrEqual | Comparison::GreaterThanOrEqualOrUnordered => {
                EQUAL.or(GREATER)
            }
        }
    }
}

fn holds(comparison: Comparison, left: i64, right: i64) -> bool {
    match comparison {
        Comparison::Equal => left == right,
        Comparison::NotEqual => left != right,
        Comparison::LessThan => left < right,
        Comparison::LessThanOrEqual => left <= right,
        Comparison::GreaterThan | Comparison::GreaterThanOrUnordered => left > right,
        Comparison::GreaterThanOrEqual | Comparison::GreaterThanOrEqualOrUnordered => left >= right,
    }
}

/// How the compared values compare natively: Go's operators on Ints, Chars
/// and the Longs of either signedness.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Native {
    Operator,
    Long(Signedness),
}

impl Simplifier<'_> {
    /// The case of a three-way comparison as choices by native comparisons,
    /// when every alternative tests only its outcome.
    pub(super) fn three_way_case(
        &mut self,
        scrutinee: &Expression,
        alternatives: &[Alternative],
        monotype: MonotypeId,
    ) -> Option<Expression> {
        let ExpressionKind::Foreign { foreign: Foreign::Call { boundary, .. }, arguments } =
            &scrutinee.kind
        else {
            return None;
        };
        if !boundary.three_way {
            return None;
        }
        let native = self.native_order(arguments[0].monotype)?;
        let branches = outcome_branches(alternatives)?;
        let [left, right] = <[Expression; 2]>::try_from(arguments.clone()).ok()?;
        let mut bindings = vec![];
        let left = self.shared_operand(left, "compared", &mut bindings);
        let right = self.shared_operand(right, "compared", &mut bindings);
        let boolean = self.monotypes.intern(Monotype::Boolean);
        let chosen = self.choose(&branches, ALL, native, &left, &right, boolean, monotype);
        if bindings.is_empty() {
            return Some(chosen);
        }
        Some(Expression::new(ExpressionKind::Let { bindings, body: Box::new(chosen) }, monotype))
    }

    /// `if a == b then x else if a > b then x else y` as `if a >= b then x
    /// else y`: a chain of choices by comparisons of the same two values,
    /// with the choices of the same body joined, when that drops a choice.
    pub(super) fn joined_comparisons(
        &mut self,
        condition: &Expression,
        then: &Expression,
        otherwise: &Expression,
        monotype: MonotypeId,
    ) -> Option<Expression> {
        let (comparison, native, left, right) = self.native_comparison(condition)?;
        let mut branches: Vec<OutcomeBranch> = vec![];
        let mut choices = 0;
        let mut possible = ALL;
        let mut add = |outcomes: Outcomes, body: &Expression| {
            choices += 1;
            if outcomes == NONE {
                return;
            }
            match branches.iter_mut().find(|(_, existing, _)| existing == body) {
                Some((joined, _, _)) => *joined = joined.or(outcomes),
                None => branches.push((outcomes, body.clone(), None)),
            }
        };
        let (mut comparison, mut then, mut otherwise, mut swapped) =
            (comparison, then, otherwise, false);
        loop {
            let outcomes = Outcomes::of(comparison);
            let outcomes = if swapped { outcomes.swapped() } else { outcomes };
            let outcomes = outcomes.and(possible);
            add(outcomes, then);
            possible = possible.without(outcomes);
            let ExpressionKind::If { condition, then: next_then, otherwise: next_otherwise } =
                &otherwise.kind
            else {
                break;
            };
            let Some((next, next_native, next_left, next_right)) =
                self.native_comparison(condition)
            else {
                break;
            };
            swapped = match (
                next_left == left && next_right == right,
                next_left == right && next_right == left,
            ) {
                _ if next_native != native => break,
                (true, _) => false,
                (_, true) => true,
                _ => break,
            };
            (comparison, then, otherwise) = (next, next_then, next_otherwise);
        }
        add(possible, otherwise);
        if branches.len() == choices {
            return None;
        }
        let boolean = self.monotypes.intern(Monotype::Boolean);
        let (left, right) = (left.clone(), right.clone());
        Some(self.choose(&branches, ALL, native, &left, &right, boolean, monotype))
    }

    /// A comparison of two values by Go's operators on a type they order as PureScript does.
    fn native_comparison<'e>(
        &self,
        condition: &'e Expression,
    ) -> Option<(Comparison, Native, &'e Expression, &'e Expression)> {
        let ExpressionKind::Foreign { foreign, arguments } = &condition.kind else { return None };
        let [left, right] = arguments.as_slice() else { return None };
        let (comparison, native) = match foreign {
            Foreign::Operator(Operator::Compare(comparison))
                if self.native_order(left.monotype) == Some(Native::Operator) =>
            {
                (*comparison, Native::Operator)
            }
            Foreign::Int64 { operation: Int64Operation::Compare(comparison), signedness } => {
                (*comparison, Native::Long(*signedness))
            }
            _ => return None,
        };
        Some((comparison, native, left, right))
    }

    fn native_order(&self, operand: MonotypeId) -> Option<Native> {
        match self.monotypes.get(operand) {
            Monotype::Int | Monotype::Char => Some(Native::Operator),
            Monotype::Int64 => Some(Native::Long(Signedness::Signed)),
            Monotype::UInt64 => Some(Native::Long(Signedness::Unsigned)),
            _ => None,
        }
    }

    /// `if <first branch's outcomes> then … else …` down the branches, each
    /// test telling its outcomes from those still `possible`.
    #[allow(clippy::too_many_arguments)]
    fn choose(
        &mut self,
        branches: &[OutcomeBranch],
        possible: Outcomes,
        native: Native,
        left: &Expression,
        right: &Expression,
        boolean: MonotypeId,
        monotype: MonotypeId,
    ) -> Expression {
        if let Some(outcome) = constant_outcome(native, left, right) {
            let chosen = branches.iter().find(|(outcomes, _, _)| outcomes.and(outcome) != NONE);
            let (_, body, _) =
                chosen.expect("invariant violated: the branches cover every outcome");
            return body.clone();
        }
        let [(outcomes, body, position), rest @ ..] = branches else {
            unreachable!("invariant violated: a three-way case has a branch")
        };
        if rest.is_empty() {
            return body.clone();
        }
        let comparison = distinguishing(*outcomes, possible);
        let foreign = match native {
            Native::Operator => Foreign::Operator(Operator::Compare(comparison)),
            Native::Long(signedness) => {
                Foreign::Int64 { operation: Int64Operation::Compare(comparison), signedness }
            }
        };
        let arguments = vec![left.clone(), right.clone()];
        let condition = ExpressionKind::Foreign { foreign: foreign.interned(), arguments };
        let condition = Expression::new(condition, boolean).located(*position);
        let possible = possible.without(*outcomes);
        let otherwise = self.choose(rest, possible, native, left, right, boolean, monotype);
        self.plain_choice(condition, body.clone(), otherwise, monotype)
    }
}

/// A comparison of two Long constants, folded.
pub(super) fn constant_comparison(foreign: &Foreign, arguments: &[Expression]) -> Option<bool> {
    let Foreign::Int64 { operation: Int64Operation::Compare(comparison), signedness } = foreign
    else {
        return None;
    };
    let [left, right] = arguments else { return None };
    let outcome = constant_outcome(Native::Long(*signedness), left, right)?;
    Some(Outcomes::of(*comparison).and(outcome) != NONE)
}

/// The outcome of comparing two constants.
fn constant_outcome(native: Native, left: &Expression, right: &Expression) -> Option<Outcomes> {
    let ordering = match native {
        Native::Operator => match (&left.kind, &right.kind) {
            (
                ExpressionKind::Literal(Literal::Int(x)),
                ExpressionKind::Literal(Literal::Int(y)),
            ) => x.cmp(y),
            (
                ExpressionKind::Literal(Literal::Char(x)),
                ExpressionKind::Literal(Literal::Char(y)),
            ) => x.cmp(y),
            _ => return None,
        },
        Native::Long(signedness) => {
            let (x, y) = (long_constant(left)?, long_constant(right)?);
            match signedness {
                Signedness::Signed => x.cmp(&y),
                Signedness::Unsigned => (x as u64).cmp(&(y as u64)),
            }
        }
    };
    Some(match ordering {
        std::cmp::Ordering::Less => LESS,
        std::cmp::Ordering::Equal => EQUAL,
        std::cmp::Ordering::Greater => GREATER,
    })
}

/// The bits of a Long the expression spells as a constant.
fn long_constant(expression: &Expression) -> Option<i64> {
    match &expression.kind {
        ExpressionKind::Foreign {
            foreign: Foreign::Int64 { operation: Int64Operation::Constant(bits), .. },
            ..
        } => Some(*bits),
        ExpressionKind::Foreign {
            foreign: Foreign::Int64 { operation: Int64Operation::FromInt, .. },
            arguments,
        } => match arguments.first()?.kind {
            ExpressionKind::Literal(Literal::Int(value)) => Some(i64::from(value as i32)),
            _ => None,
        },
        _ => None,
    }
}

/// The comparison that holds for `outcomes` among those `possible`.
fn distinguishing(outcomes: Outcomes, possible: Outcomes) -> Comparison {
    [
        Comparison::LessThan,
        Comparison::GreaterThan,
        Comparison::Equal,
        Comparison::LessThanOrEqual,
        Comparison::GreaterThanOrEqual,
        Comparison::NotEqual,
    ]
    .into_iter()
    .find(|comparison| Outcomes::of(*comparison).and(possible) == outcomes)
    .expect("invariant violated: a branch's outcomes are some but not all of those possible")
}

/// The outcomes each body is chosen for, joined by body, when the patterns
/// and guards test nothing but the outcome and cover all of them.
fn outcome_branches(alternatives: &[Alternative]) -> Option<Vec<OutcomeBranch>> {
    let mut remaining = ALL;
    let mut branches: Vec<OutcomeBranch> = vec![];
    let mut catch = |outcomes: Outcomes,
                     body: &Expression,
                     binder: Option<LocalId>,
                     position: Option<SourcePosition>| {
        if binder.is_some_and(|binder| occurrences(body, binder).total > 0) {
            return None;
        }
        let caught = remaining.and(outcomes);
        remaining = remaining.without(caught);
        if caught == NONE {
            return Some(());
        }
        match branches.iter_mut().find(|(_, existing, _)| existing == body) {
            Some((joined, _, _)) => *joined = joined.or(caught),
            None => branches.push((caught, body.clone(), position)),
        }
        Some(())
    };
    for alternative in alternatives {
        let position = alternative.position;
        let [pattern] = alternative.patterns.as_slice() else { return None };
        let (matched, binder) = match &pattern.kind {
            crate::mono::PatternKind::Wildcard => (ALL, None),
            crate::mono::PatternKind::Variable(local) => (ALL, Some(local.id)),
            crate::mono::PatternKind::Literal(Literal::Int(k)) => {
                (Outcomes::compared(Comparison::Equal, *k, true), None)
            }
            _ => return None,
        };
        match &alternative.body {
            Guarded::Unconditional(body) => catch(matched, body, binder, position)?,
            Guarded::Guards(branches) => {
                for branch in branches {
                    let mut admitted = matched;
                    for guard in &branch.guards {
                        let Guard::Boolean(condition) = guard else { return None };
                        admitted = admitted.and(guarded_outcomes(condition, binder)?);
                    }
                    let position = match branch.guards.first() {
                        Some(guard) => guard.value().position,
                        None => position,
                    };
                    catch(admitted, &branch.body, binder, position)?;
                }
            }
        }
    }
    (remaining == NONE).then_some(branches)
}

/// The outcomes a guard admits, when it tests only the result bound to `binder`.
fn guarded_outcomes(condition: &Expression, binder: Option<LocalId>) -> Option<Outcomes> {
    let is_binder = |expression: &Expression| matches!(expression.kind, ExpressionKind::Local(id) if Some(id) == binder);
    match &condition.kind {
        ExpressionKind::Literal(Literal::Boolean(true)) => Some(ALL),
        ExpressionKind::Literal(Literal::Boolean(false)) => Some(NONE),
        ExpressionKind::Foreign { foreign: Foreign::Operator(operator), arguments } => {
            match (operator, arguments.as_slice()) {
                (Operator::Compare(comparison), [left, right]) => match (&left.kind, &right.kind) {
                    (_, ExpressionKind::Literal(Literal::Int(k))) if is_binder(left) => {
                        Some(Outcomes::compared(*comparison, *k, true))
                    }
                    (ExpressionKind::Literal(Literal::Int(k)), _) if is_binder(right) => {
                        Some(Outcomes::compared(*comparison, *k, false))
                    }
                    _ => None,
                },
                (Operator::BooleanNot, [operand]) => {
                    Some(ALL.without(guarded_outcomes(operand, binder)?))
                }
                (Operator::BooleanAnd, [left, right]) => {
                    Some(guarded_outcomes(left, binder)?.and(guarded_outcomes(right, binder)?))
                }
                (Operator::BooleanOr, [left, right]) => {
                    Some(guarded_outcomes(left, binder)?.or(guarded_outcomes(right, binder)?))
                }
                _ => None,
            }
        }
        _ => None,
    }
}
