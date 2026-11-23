use super::Simplifier;
use super::choice::operation;
use super::short_circuit::mentions;
use crate::foreign::{Foreign, Iteration, Operator};
use crate::monomorphic::traversal::for_each_child_mut;
use crate::monomorphic::{
    Alternative, Binding, Expression, ExpressionKind, Guarded, GuardedBranch, Literal, Local,
    LocalId, Results,
};
use crate::monotype::{Monotype, MonotypeId};

struct Accumulation {
    initial: Expression,
    array: Expression,
    element: Local,
    state: Local,
    step: Expression,
}

impl Simplifier<'_> {
    pub(super) fn each_with_index(
        &mut self,
        foreign: &Foreign,
        arguments: Vec<Expression>,
        monotype: MonotypeId,
    ) -> Expression {
        let [first, second] = <[Expression; 2]>::try_from(arguments).unwrap_or_else(|_| {
            unreachable!("invariant violated: an indexed traversal has two arguments")
        });
        let (array, function) = match foreign {
            Foreign::EffectTraverseArrayWithIndex => (second, first),
            _ => (first, second),
        };
        let element = self.element_monotype(array.monotype);
        let integer = self.monotypes.intern(Monotype::Int);
        let array_local = self.named_local("array", array.monotype);
        let index = self.named_local("index", integer);

        let length = operation(Operator::ArrayLength, vec![array_local.expression()], integer);
        let current = vec![array_local.expression(), index.expression()];
        let current = operation(Operator::ArrayIndex, current, element);
        let step = self.monotypes.result_after(function.monotype, 2);
        let body = self.apply(function, vec![index.expression(), current], step);
        let action = self.monotypes.function(integer, step);
        let action = Expression::new(
            ExpressionKind::Lambda { parameters: vec![index], body: Box::new(body) },
            action,
        );
        let start = Expression::new(ExpressionKind::Literal(Literal::Int(0)), integer);
        let counted = ExpressionKind::Foreign {
            foreign: &Foreign::EffectFor,
            arguments: vec![start, length, action],
        };
        let counted = Expression::new(counted, monotype);
        self.let_bindings(vec![Binding { local: array_local, value: array }], counted)
    }

    pub(super) fn fold_array(
        &mut self,
        arguments: Vec<Expression>,
        monotype: MonotypeId,
    ) -> Expression {
        let [function, initial, array] = <[Expression; 3]>::try_from(arguments)
            .unwrap_or_else(|_| unreachable!("invariant violated: foldM has three arguments"));
        let element = self.element_monotype(array.monotype);
        let element = self.named_local(&self.monotypes.value_name(element), element);
        let state = self.named_local("state", initial.monotype);
        let step = vec![state.expression(), element.expression()];
        let step = self.apply(function, step, monotype);
        let initial = Expression::new(ExpressionKind::EffectPure(Box::new(initial)), monotype);
        self.accumulate(Accumulation { initial, array, element, state, step }, monotype)
    }

    pub(super) fn sequenced_fold(
        &mut self,
        foreign: &'static Foreign,
        arguments: Vec<Expression>,
        monotype: MonotypeId,
    ) -> Result<Expression, Vec<Expression>> {
        let Foreign::Call { boundary, .. } = foreign else { return Err(arguments) };
        let Some(iteration @ (Iteration::FoldLeft | Iteration::FoldRight)) = boundary.iteration
        else {
            return Err(arguments);
        };
        let Monotype::Effect(result) = *self.monotypes.get(monotype) else {
            return Err(arguments);
        };
        if !matches!(self.monotypes.get(arguments[2].monotype), Monotype::Array(_)) {
            return Err(arguments);
        }
        let ExpressionKind::Lambda { parameters, body } = &arguments[0].kind else {
            return Err(arguments);
        };
        let [first, second] = parameters.as_slice() else { return Err(arguments) };
        match iteration {
            Iteration::FoldRight => {
                if *self.monotypes.get(result) != Monotype::Unit {
                    return Err(arguments);
                }
                let finished = ExpressionKind::EffectPure(Box::new(Expression::new(
                    ExpressionKind::Unit,
                    result,
                )));
                let finished = Expression::new(finished, monotype);
                let Some(body) = performed_before(body, second.id, &finished) else {
                    return Err(arguments);
                };
                let element = first.clone();
                let [_, initial, array] =
                    <[Expression; 3]>::try_from(arguments).unwrap_or_else(|_| {
                        unreachable!("invariant violated: a fold has three arguments")
                    });
                let each = ExpressionKind::EffectEach {
                    array: Box::new(array),
                    element,
                    body: Box::new(body),
                    results: Results::Discarded,
                };
                let each = Expression::new(each, monotype);
                let ignored = self.named_local("performed", result);
                Ok(self.effect_bind(each, ignored, initial, monotype))
            }
            _ => {
                let ExpressionKind::EffectBind { action, local, body: step } = &body.kind else {
                    return Err(arguments);
                };
                let performs_accumulator =
                    matches!(action.kind, ExpressionKind::Local(id) if id == first.id);
                if !performs_accumulator || mentions(step, first.id) {
                    return Err(arguments);
                }
                let (element, state, step) = (second.clone(), local.clone(), (**step).clone());
                let [_, initial, array] =
                    <[Expression; 3]>::try_from(arguments).unwrap_or_else(|_| {
                        unreachable!("invariant violated: a fold has three arguments")
                    });
                let accumulation = Accumulation { initial, array, element, state, step };
                Ok(self.accumulate(accumulation, monotype))
            }
        }
    }

    pub(super) fn sequence_folds(&mut self, expression: &mut Expression) {
        for_each_child_mut(expression, &mut |child| self.sequence_folds(child));
        let ExpressionKind::Foreign { foreign, .. } = expression.kind else { return };
        if !matches!(foreign, Foreign::Call { boundary, .. } if boundary.iteration.is_some()) {
            return;
        }
        let (monotype, position) = (expression.monotype, expression.position);
        let ExpressionKind::Foreign { arguments, .. } =
            std::mem::replace(&mut expression.kind, ExpressionKind::Unit)
        else {
            unreachable!("invariant violated: the expression was just matched as a foreign")
        };
        *expression = match self.sequenced_fold(foreign, arguments, monotype) {
            Ok(looped) => looped.located(position),
            Err(arguments) => {
                let kind = ExpressionKind::Foreign { foreign, arguments };
                Expression::new(kind, monotype).located(position)
            }
        };
    }

    fn accumulate(&mut self, accumulation: Accumulation, monotype: MonotypeId) -> Expression {
        let Accumulation { initial, array, element, state, step } = accumulation;
        let unit = self.monotypes.intern(Monotype::Unit);
        let performed_unit = self.monotypes.intern(Monotype::Effect(unit));
        let finished = self.named_local("finished", unit);
        if state.monotype == unit {
            let started = self.named_local("started", unit);
            let nothing = Expression::new(ExpressionKind::Unit, unit);
            let body = vec![Binding { local: state, value: nothing.clone() }];
            let body = self.let_bindings(body, step);
            let each = ExpressionKind::EffectEach {
                array: Box::new(array),
                element,
                body: Box::new(body),
                results: Results::Discarded,
            };
            let each = Expression::new(each, performed_unit);
            let done = Expression::new(ExpressionKind::EffectPure(Box::new(nothing)), monotype);
            let looped = self.effect_bind(each, finished, done, monotype);
            return self.effect_bind(initial, started, looped, monotype);
        }
        let reference = self.monotypes.intern(Monotype::Reference(state.monotype));
        let created = self.monotypes.intern(Monotype::Effect(reference));

        let accumulator = self.named_local("accumulator", reference);
        let next = self.named_local("next", state.monotype);
        let start = self.named_local("start", state.monotype);

        let read = self.read_reference(&accumulator, monotype);
        let written = ExpressionKind::Foreign {
            foreign: &Foreign::ReferenceWrite,
            arguments: vec![next.expression(), accumulator.expression()],
        };
        let written = Expression::new(written, performed_unit);
        let body = self.effect_bind(step, next, written, performed_unit);
        let body = self.effect_bind(read, state, body, performed_unit);
        let each = ExpressionKind::EffectEach {
            array: Box::new(array),
            element,
            body: Box::new(body),
            results: Results::Discarded,
        };
        let each = Expression::new(each, performed_unit);
        let result = self.read_reference(&accumulator, monotype);
        let folded = self.effect_bind(each, finished, result, monotype);
        let create = ExpressionKind::Foreign {
            foreign: &Foreign::ReferenceNew,
            arguments: vec![start.expression()],
        };
        let create = Expression::new(create, created);
        let create = self.effect_bind(initial, start, create, created);
        self.effect_bind(create, accumulator, folded, monotype)
    }

    fn element_monotype(&self, array: MonotypeId) -> MonotypeId {
        match self.monotypes.get(array) {
            Monotype::Array(element) => *element,
            _ => unreachable!("invariant violated: an array traversal traverses an array"),
        }
    }

    fn read_reference(&self, reference: &Local, monotype: MonotypeId) -> Expression {
        let read = ExpressionKind::Foreign {
            foreign: &Foreign::ReferenceRead,
            arguments: vec![reference.expression()],
        };
        Expression::new(read, monotype)
    }
}

fn performed_before(
    expression: &Expression,
    continuation: LocalId,
    finished: &Expression,
) -> Option<Expression> {
    let kind = match &expression.kind {
        ExpressionKind::Local(id) if *id == continuation => return Some(finished.clone()),
        ExpressionKind::EffectBind { action, body, .. }
            if matches!(action.kind, ExpressionKind::Local(id) if id == continuation)
                && matches!(&body.kind, ExpressionKind::EffectPure(value)
                    if matches!(value.kind, ExpressionKind::Unit | ExpressionKind::Local(_))) =>
        {
            return Some(finished.clone());
        }
        ExpressionKind::EffectBind { action, local, body } if !mentions(action, continuation) => {
            ExpressionKind::EffectBind {
                action: action.clone(),
                local: local.clone(),
                body: Box::new(performed_before(body, continuation, finished)?),
            }
        }
        ExpressionKind::Let { bindings, body }
            if !bindings.iter().any(|binding| mentions(&binding.value, continuation)) =>
        {
            ExpressionKind::Let {
                bindings: bindings.clone(),
                body: Box::new(performed_before(body, continuation, finished)?),
            }
        }
        ExpressionKind::If { condition, then, otherwise } if !mentions(condition, continuation) => {
            ExpressionKind::If {
                condition: condition.clone(),
                then: Box::new(performed_before(then, continuation, finished)?),
                otherwise: Box::new(performed_before(otherwise, continuation, finished)?),
            }
        }
        ExpressionKind::Case { scrutinees, alternatives }
            if !scrutinees.iter().any(|scrutinee| mentions(scrutinee, continuation)) =>
        {
            let alternatives = alternatives
                .iter()
                .map(|alternative| {
                    let body = guarded_before(&alternative.body, continuation, finished)?;
                    Some(Alternative { body, ..alternative.clone() })
                })
                .collect::<Option<Vec<Alternative>>>()?;
            ExpressionKind::Case { scrutinees: scrutinees.clone(), alternatives }
        }
        _ => return None,
    };
    Some(Expression::new(kind, expression.monotype).located(expression.position))
}

fn guarded_before(
    guarded: &Guarded,
    continuation: LocalId,
    finished: &Expression,
) -> Option<Guarded> {
    match guarded {
        Guarded::Unconditional(body) => {
            Some(Guarded::Unconditional(performed_before(body, continuation, finished)?))
        }
        Guarded::Guards(branches) => {
            let branches = branches
                .iter()
                .map(|branch| {
                    if branch.guards.iter().any(|guard| mentions(guard.value(), continuation)) {
                        return None;
                    }
                    let body = performed_before(&branch.body, continuation, finished)?;
                    Some(GuardedBranch { guards: branch.guards.clone(), body })
                })
                .collect::<Option<Vec<GuardedBranch>>>()?;
            Some(Guarded::Guards(branches))
        }
    }
}
