use super::Simplifier;
use crate::foreign::{ARRAY_ALL, ARRAY_ANY, Foreign, Iteration, Operator};
use crate::monomorphic::traversal::mentions_local;
use crate::monomorphic::{
    Alternative, Binding, Expression, ExpressionKind, Guarded, GuardedBranch, Literal, LocalId,
};
use crate::monotype::{Monotype, MonotypeId};

impl Simplifier<'_> {
    pub(super) fn short_circuit(
        &mut self,
        foreign: &'static Foreign,
        arguments: Vec<Expression>,
        monotype: MonotypeId,
    ) -> Result<Expression, Vec<Expression>> {
        let Foreign::Call { boundary, .. } = foreign else { return Err(arguments) };
        let accumulator_position = match boundary.iteration {
            Some(Iteration::FoldLeft) => 0,
            Some(Iteration::FoldRight) => 1,
            _ => return Err(arguments),
        };
        let ExpressionKind::Lambda { parameters, body } = &arguments[0].kind else {
            return Err(arguments);
        };
        if parameters.len() != 2 || *self.monotypes.get(monotype) != Monotype::Boolean {
            return Err(arguments);
        }
        let accumulator = parameters[accumulator_position].id;
        let operators = [Operator::BooleanAnd, Operator::BooleanOr];
        let decision = operators.into_iter().find_map(|operator| {
            let condition = self.decided(body, accumulator, operator)?;
            Some((operator, condition))
        });
        let Some((operator, condition)) = decision else { return Err(arguments) };
        let [step, initial, array] = <[Expression; 3]>::try_from(arguments)
            .unwrap_or_else(|_| unreachable!("invariant violated: a fold has three arguments"));
        let ExpressionKind::Lambda { mut parameters, .. } = step.kind else {
            unreachable!("invariant violated: the step was just matched as a lambda")
        };
        let element = parameters.swap_remove(1 - accumulator_position);
        let predicate_type = self.monotypes.function(element.monotype, monotype);
        let body = Box::new(condition);
        let predicate = ExpressionKind::Lambda { parameters: vec![element], body };
        let predicate = Expression::new(predicate, predicate_type);
        let search = match operator {
            Operator::BooleanAnd => &ARRAY_ALL,
            _ => &ARRAY_ANY,
        };
        let searched = Expression::new(
            ExpressionKind::Foreign { foreign: search, arguments: vec![predicate, array] },
            monotype,
        );
        Ok(self.operator(Foreign::Operator(operator).interned(), vec![searched, initial], monotype))
    }

    fn decided(
        &mut self,
        expression: &Expression,
        accumulator: LocalId,
        operator: Operator,
    ) -> Option<Expression> {
        let monotype = expression.monotype;
        let deciding = operator == Operator::BooleanOr;
        if !mentions_local(expression, accumulator) {
            return match expression.kind {
                ExpressionKind::Literal(Literal::Boolean(value)) if value == deciding => {
                    Some(expression.clone())
                }
                ExpressionKind::Fail(_) => Some(expression.clone()),
                _ => None,
            };
        }
        match &expression.kind {
            ExpressionKind::Local(_) => Some(Expression::new(
                ExpressionKind::Literal(Literal::Boolean(!deciding)),
                monotype,
            )),
            ExpressionKind::Foreign { foreign: Foreign::Operator(inner), arguments }
                if *inner == operator =>
            {
                let [left, right] = arguments.as_slice() else { return None };
                let left_mentions = mentions_local(left, accumulator);
                let right_mentions = mentions_local(right, accumulator);
                let (left, right) = match (left_mentions, right_mentions) {
                    (false, true) => (left.clone(), self.decided(right, accumulator, operator)?),
                    (true, false) => (self.decided(left, accumulator, operator)?, right.clone()),
                    _ => return None,
                };
                Some(self.operator(
                    Foreign::Operator(operator).interned(),
                    vec![left, right],
                    monotype,
                ))
            }
            ExpressionKind::Let { bindings, body } => {
                if bindings.iter().any(|binding| mentions_local(&binding.value, accumulator)) {
                    return None;
                }
                let body = self.decided(body, accumulator, operator)?;
                let bindings: Vec<Binding> = bindings.clone();
                Some(Expression::new(
                    ExpressionKind::Let { bindings, body: Box::new(body) },
                    monotype,
                ))
            }
            ExpressionKind::If { condition, then, otherwise } => {
                if mentions_local(condition, accumulator) {
                    return None;
                }
                let then = self.decided(then, accumulator, operator)?;
                let otherwise = self.decided(otherwise, accumulator, operator)?;
                Some(self.boolean_choice((**condition).clone(), then, otherwise, monotype))
            }
            ExpressionKind::Case { scrutinees, alternatives } => {
                if scrutinees.iter().any(|scrutinee| mentions_local(scrutinee, accumulator)) {
                    return None;
                }
                let alternatives = alternatives.iter().map(|alternative| {
                    let body = self.decided_guarded(&alternative.body, accumulator, operator)?;
                    Some(Alternative { body, ..alternative.clone() })
                });
                let alternatives = alternatives.collect::<Option<Vec<Alternative>>>()?;
                let scrutinees = scrutinees.clone();
                Some(Expression::new(ExpressionKind::Case { scrutinees, alternatives }, monotype))
            }
            _ => None,
        }
    }

    fn decided_guarded(
        &mut self,
        guarded: &Guarded,
        accumulator: LocalId,
        operator: Operator,
    ) -> Option<Guarded> {
        match guarded {
            Guarded::Unconditional(body) => {
                Some(Guarded::Unconditional(self.decided(body, accumulator, operator)?))
            }
            Guarded::Guards(branches) => {
                let branches = branches.iter().map(|branch| {
                    if branch.guards.iter().any(|guard| mentions_local(guard.value(), accumulator))
                    {
                        return None;
                    }
                    let body = self.decided(&branch.body, accumulator, operator)?;
                    Some(GuardedBranch { guards: branch.guards.clone(), body })
                });
                let branches = branches.collect::<Option<Vec<GuardedBranch>>>()?;
                Some(Guarded::Guards(branches))
            }
        }
    }
}
