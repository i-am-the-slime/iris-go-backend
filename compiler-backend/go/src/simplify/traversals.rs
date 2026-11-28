use rustc_hash::FxHashSet;

use super::Simplifier;
use super::choice::operation;
use super::constants::int;
use crate::foreign::{Comparison, Foreign, Iteration, Operator};
use crate::monomorphic::traversal::{for_each_child_mut, mentions_local};
use crate::monomorphic::{
    Alternative, Binding, Expression, ExpressionKind, Guarded, GuardedBranch, Literal, Local,
    LocalId, Pattern, PatternKind, Results,
};
use crate::monotype::{DataType, Monotype, MonotypeId};

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
        if iteration == Iteration::FoldLeft
            && matches!(self.monotypes.get(monotype), Monotype::Function(..))
        {
            return self.reader_fold(arguments, monotype);
        }
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
                let arguments = <[Expression; 3]>::try_from(arguments);
                let [_, initial, array] = arguments.unwrap_or_else(|_| {
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
                let ExpressionKind::Local(performed) = action.kind else { return Err(arguments) };
                if performed != first.id || mentions_local(step, first.id) {
                    return Err(arguments);
                }
                let (element, state, step) = (second.clone(), local.clone(), (**step).clone());
                let arguments = <[Expression; 3]>::try_from(arguments);
                let [_, initial, array] = arguments.unwrap_or_else(|_| {
                    unreachable!("invariant violated: a fold has three arguments")
                });
                let accumulation = Accumulation { initial, array, element, state, step };
                Ok(self.accumulate(accumulation, monotype))
            }
        }
    }

    /// A left fold whose accumulator is an action that reads a value first, as `traverse` in a
    /// reader over Effect builds, `\acc x r -> do s <- acc r; …`: one loop that runs the
    /// starting action with the value read and then each step on what the last one gave, instead
    /// of a closure for each element that calls the one before it.
    fn reader_fold(
        &mut self,
        arguments: Vec<Expression>,
        monotype: MonotypeId,
    ) -> Result<Expression, Vec<Expression>> {
        let Some((_, performed)) = self.monotypes.function_parts(monotype) else {
            return Err(arguments);
        };
        if !matches!(self.monotypes.get(performed), Monotype::Effect(_))
            || !matches!(self.monotypes.get(arguments[2].monotype), Monotype::Array(_))
        {
            return Err(arguments);
        }
        let Some((accumulator, element, read, body)) = reader_step(&arguments[0]) else {
            return Err(arguments);
        };
        let (leading, body) = leading_bindings(body);
        let ExpressionKind::EffectBind { action, local, body: step } = &body.kind else {
            return Err(arguments);
        };
        if leading.iter().any(|binding| mentions_local(&binding.value, accumulator)) {
            return Err(arguments);
        }
        let reads_accumulator = matches!(&action.kind, ExpressionKind::Apply { function, arguments }
            if matches!(function.kind, ExpressionKind::Local(id) if id == accumulator)
                && matches!(arguments.as_slice(), [argument] if matches!(argument.kind, ExpressionKind::Local(id) if id == read.id)));
        if !reads_accumulator || mentions_local(step, accumulator) {
            return Err(arguments);
        }
        let with_leading = |step: Expression| match leading.is_empty() {
            true => step,
            false => {
                let monotype = step.monotype;
                let kind = ExpressionKind::Let { bindings: leading.clone(), body: Box::new(step) };
                Expression::new(kind, monotype)
            }
        };
        if self.fuel > 0 && calls_unknown(&with_leading((**step).clone()), &self.appenders) {
            return Err(arguments);
        }
        let (element, read, state, step) = (element, read, local.clone(), (**step).clone());
        let [_, initial, array] = <[Expression; 3]>::try_from(arguments)
            .unwrap_or_else(|_| unreachable!("invariant violated: a fold has three arguments"));
        let initial = self.apply(initial, vec![read.expression()], performed);
        let looped = match propagated_failure(&step, state.id) {
            Some(mut propagation) => {
                propagation.step = with_leading(propagation.step);
                let accumulation = Accumulation { initial, array, element, state, step };
                self.failing_fold(accumulation, propagation, performed)
            }
            None => {
                let step = with_leading(step);
                let accumulation = Accumulation { initial, array, element, state, step };
                self.accumulate(accumulation, performed)
            }
        };
        let kind = ExpressionKind::Lambda { parameters: vec![read], body: Box::new(looped) };
        Ok(Expression::new(kind, monotype))
    }

    /// A fold whose step passes a failure on untouched, `case s of Left e -> pure (Left e); Right
    /// v -> …`, as a loop over the elements that carries only the value and stops at the first
    /// failure, so that no later element is looked at once one has failed. The appender the
    /// traversal threads is a plain `snoc` of the value the loop owns.
    fn failing_fold(
        &mut self,
        accumulation: Accumulation,
        propagation: Propagation,
        performed: MonotypeId,
    ) -> Expression {
        let Accumulation { initial, array, element, state, .. } = accumulation;
        let Propagation { failed, succeeded, value, mut step } = propagation;
        let integer = self.monotypes.intern(Monotype::Int);
        let boolean = self.monotypes.intern(Monotype::Boolean);
        let literal = |value| int(value, integer);
        snoc_appends(&mut step, &self.appenders, value.id);
        let pure_step = without_effects(&step, state.monotype);
        let is_pure = pure_step.is_some();
        let looped = if is_pure { state.monotype } else { performed };
        let returned = |value: Expression| match is_pure {
            true => value,
            false => Expression::new(ExpressionKind::EffectPure(Box::new(value)), performed),
        };
        let elements = self.named_local("elements", array.monotype);
        let index = self.named_local("index", integer);
        let loop_monotype = self.monotypes.function(value.monotype, looped);
        let loop_monotype = self.monotypes.function(integer, loop_monotype);
        let looping = self.named_local("from", loop_monotype);
        let continued = |index: Expression, carried: &Local| {
            let kind = ExpressionKind::Apply {
                function: Box::new(looping.expression()),
                arguments: vec![index, carried.expression()],
            };
            Expression::new(kind, looped)
        };

        let following = operation(Operator::IntAdd, vec![index.expression(), literal(1)], integer);
        let next = self.named_local(&state.name, state.monotype);
        let next_value = self.named_local(&value.name, value.monotype);
        let carried_on = continued(following, &next_value);
        let carried_on =
            self.unless_failed(&next, &failed, &succeeded, next_value, carried_on, &returned);
        let current = vec![elements.expression(), index.expression()];
        let current = operation(Operator::ArrayIndex, current, element.monotype);
        let element = Binding { local: element, value: current };
        let stepped = match pure_step {
            Some(step) => {
                let step = ExpressionKind::Let { bindings: vec![element], body: Box::new(step) };
                let next = Binding { local: next, value: Expression::new(step, state.monotype) };
                ExpressionKind::Let { bindings: vec![next], body: Box::new(carried_on) }
            }
            None => {
                let step = ExpressionKind::Let { bindings: vec![element], body: Box::new(step) };
                ExpressionKind::EffectBind {
                    action: Box::new(Expression::new(step, performed)),
                    local: next,
                    body: Box::new(carried_on),
                }
            }
        };
        let length = operation(Operator::ArrayLength, vec![elements.expression()], integer);
        let within = vec![index.expression(), length];
        let within = operation(Operator::Compare(Comparison::LessThan), within, boolean);
        let finished = returned(succeeded.built(value.expression(), state.monotype));
        let body = ExpressionKind::If {
            condition: Box::new(within),
            then: Box::new(Expression::new(stepped, looped)),
            otherwise: Box::new(finished),
        };
        let lambda = ExpressionKind::Lambda {
            parameters: vec![index, value.clone()],
            body: Box::new(Expression::new(body, looped)),
        };
        let lambda = Expression::new(lambda, loop_monotype);

        let started = self.named_local(&state.name, state.monotype);
        let start_value = self.named_local(&value.name, value.monotype);
        let start = continued(literal(0), &start_value);
        let start = match is_pure {
            true => Expression::new(ExpressionKind::EffectPure(Box::new(start)), performed),
            false => start,
        };
        let performed_pure = |value: Expression| {
            Expression::new(ExpressionKind::EffectPure(Box::new(value)), performed)
        };
        let start =
            self.unless_failed(&started, &failed, &succeeded, start_value, start, &performed_pure);
        let start = ExpressionKind::EffectBind {
            action: Box::new(initial),
            local: started,
            body: Box::new(start),
        };
        let looped = ExpressionKind::Let {
            bindings: vec![Binding { local: looping, value: lambda }],
            body: Box::new(Expression::new(start, performed)),
        };
        let looped = ExpressionKind::Let {
            bindings: vec![Binding { local: elements, value: array }],
            body: Box::new(Expression::new(looped, performed)),
        };
        let fuel = std::mem::replace(&mut self.fuel, super::INLINE_FUEL);
        let looped = self.expression(Expression::new(looped, performed));
        self.fuel = fuel;
        looped
    }

    /// `case state of failed e -> returned (failed e); succeeded value -> carried_on`.
    fn unless_failed(
        &mut self,
        state: &Local,
        failed: &Constructed,
        succeeded: &Constructed,
        value: Local,
        carried_on: Expression,
        returned: &dyn Fn(Expression) -> Expression,
    ) -> Expression {
        let monotype = carried_on.monotype;
        let problem = self.named_local("problem", failed.field);
        let passed_on = returned(failed.built(problem.expression(), state.monotype));
        let alternatives = vec![
            Alternative {
                patterns: vec![failed.pattern(problem, state.monotype)],
                body: Guarded::Unconditional(passed_on),
                position: None,
            },
            Alternative {
                patterns: vec![succeeded.pattern(value, state.monotype)],
                body: Guarded::Unconditional(carried_on),
                position: None,
            },
        ];
        let kind = ExpressionKind::Case { scrutinees: vec![state.expression()], alternatives };
        Expression::new(kind, monotype)
    }

    /// A reader fold that became a loop, applied to the value it reads, as the loop on that value.
    fn apply_sequenced_reader(&mut self, expression: &mut Expression) {
        let ExpressionKind::Apply { function, .. } = &expression.kind else { return };
        if !matches!(function.kind, ExpressionKind::Lambda { .. }) {
            return;
        }
        let (monotype, position) = (expression.monotype, expression.position);
        let kind = std::mem::replace(&mut expression.kind, ExpressionKind::Unit);
        let ExpressionKind::Apply { function, arguments } = kind else {
            unreachable!("invariant violated: the expression was just matched as an application")
        };
        let fuel = std::mem::replace(&mut self.fuel, 1);
        *expression = self.apply(*function, arguments, monotype).located(position);
        self.fuel = fuel;
    }

    pub(super) fn sequence_folds(&mut self, expression: &mut Expression) {
        let applies_action = matches!(&expression.kind, ExpressionKind::Apply { function, .. }
            if !matches!(function.kind, ExpressionKind::Lambda { .. }));
        for_each_child_mut(expression, &mut |child| self.sequence_folds(child));
        if applies_action {
            self.apply_sequenced_reader(expression);
            return;
        }
        if let ExpressionKind::Foreign { foreign, arguments } = &mut expression.kind
            && matches!(foreign, Foreign::RunEffect)
            && let [performed] = arguments.as_mut_slice()
            && let ExpressionKind::EffectPure(value) = &mut performed.kind
        {
            let monotype = value.monotype;
            let placeholder = Expression::new(ExpressionKind::Unit, monotype);
            let value = std::mem::replace(&mut **value, placeholder);
            *expression = value;
            return;
        }
        if let ExpressionKind::EffectBind { action, local, body } = &mut expression.kind
            && matches!(action.kind, ExpressionKind::Foreign { foreign, .. } if *foreign == crate::foreign::APPENDER)
            && !mentions_local(body, local.id)
        {
            let monotype = body.monotype;
            let placeholder = Expression::new(ExpressionKind::Unit, monotype);
            let body = std::mem::replace(&mut **body, placeholder);
            *expression = body;
            return;
        }
        let ExpressionKind::Foreign { foreign, .. } = expression.kind else { return };
        if !matches!(foreign, Foreign::Call { boundary, .. } if boundary.iteration.is_some()) {
            return;
        }
        let (monotype, position) = (expression.monotype, expression.position);
        let kind = std::mem::replace(&mut expression.kind, ExpressionKind::Unit);
        let ExpressionKind::Foreign { arguments, .. } = kind else {
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

        let read = read_reference(&accumulator, monotype);
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
        let result = read_reference(&accumulator, monotype);
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
}

fn read_reference(reference: &Local, monotype: MonotypeId) -> Expression {
    let read = ExpressionKind::Foreign {
        foreign: &Foreign::ReferenceRead,
        arguments: vec![reference.expression()],
    };
    Expression::new(read, monotype)
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
        ExpressionKind::EffectBind { action, local, body }
            if !mentions_local(action, continuation) =>
        {
            ExpressionKind::EffectBind {
                action: action.clone(),
                local: local.clone(),
                body: Box::new(performed_before(body, continuation, finished)?),
            }
        }
        ExpressionKind::Let { bindings, body }
            if !bindings.iter().any(|binding| mentions_local(&binding.value, continuation)) =>
        {
            ExpressionKind::Let {
                bindings: bindings.clone(),
                body: Box::new(performed_before(body, continuation, finished)?),
            }
        }
        ExpressionKind::If { condition, then, otherwise }
            if !mentions_local(condition, continuation) =>
        {
            ExpressionKind::If {
                condition: condition.clone(),
                then: Box::new(performed_before(then, continuation, finished)?),
                otherwise: Box::new(performed_before(otherwise, continuation, finished)?),
            }
        }
        ExpressionKind::Case { scrutinees, alternatives }
            if !scrutinees.iter().any(|scrutinee| mentions_local(scrutinee, continuation)) =>
        {
            let alternatives = alternatives.iter().map(|alternative| {
                let body = guarded_before(&alternative.body, continuation, finished)?;
                Some(Alternative { body, ..alternative.clone() })
            });
            let alternatives = alternatives.collect::<Option<Vec<Alternative>>>()?;
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
            let branches = branches.iter().map(|branch| {
                if branch.guards.iter().any(|guard| mentions_local(guard.value(), continuation)) {
                    return None;
                }
                let body = performed_before(&branch.body, continuation, finished)?;
                Some(GuardedBranch { guards: branch.guards.clone(), body })
            });
            let branches = branches.collect::<Option<Vec<GuardedBranch>>>()?;
            Some(Guarded::Guards(branches))
        }
    }
}

/// The accumulator, element and read value of a reader fold's step, `\acc x r -> body` or
/// `\acc x -> \r -> body`, with its body.
fn reader_step(step: &Expression) -> Option<(LocalId, Local, Local, &Expression)> {
    let ExpressionKind::Lambda { parameters, body } = &step.kind else { return None };
    match (parameters.as_slice(), &body.kind) {
        ([accumulator, element, read], _) => {
            Some((accumulator.id, element.clone(), read.clone(), &**body))
        }
        ([accumulator, element], ExpressionKind::Lambda { parameters, body }) => {
            let [read] = parameters.as_slice() else { return None };
            Some((accumulator.id, element.clone(), read.clone(), &**body))
        }
        _ => None,
    }
}

/// A constructor of one field, as a fold's state is built and matched with.
struct Constructed {
    data: DataType,
    constructor: usize,
    field: MonotypeId,
}

impl Constructed {
    fn built(&self, field: Expression, monotype: MonotypeId) -> Expression {
        let kind = ExpressionKind::Construct {
            data: self.data.clone(),
            constructor: self.constructor,
            arguments: vec![field],
        };
        Expression::new(kind, monotype)
    }

    fn pattern(&self, local: Local, monotype: MonotypeId) -> Pattern {
        let field = Pattern { kind: PatternKind::Variable(local), monotype: self.field };
        let kind = PatternKind::Constructor {
            data: self.data.clone(),
            constructor: self.constructor,
            arguments: vec![field],
        };
        Pattern { kind, monotype }
    }
}

/// A fold step that passes the failure it is given on, and what it does with the value of
/// the other constructor.
struct Propagation {
    failed: Constructed,
    succeeded: Constructed,
    value: Local,
    step: Expression,
}

/// The step `case state of failed e -> pure (failed e); succeeded value -> step`.
fn propagated_failure(step: &Expression, state: LocalId) -> Option<Propagation> {
    let ExpressionKind::Case { scrutinees, alternatives } = &step.kind else { return None };
    let ([scrutinee], [first, second]) = (scrutinees.as_slice(), alternatives.as_slice()) else {
        return None;
    };
    if !matches!(scrutinee.kind, ExpressionKind::Local(id) if id == state) {
        return None;
    }
    let passes_on = |constructed: &Constructed, local: &Local, body: &Expression| {
        let ExpressionKind::EffectPure(value) = &body.kind else { return false };
        matches!(&value.kind, ExpressionKind::Construct { data, constructor, arguments }
            if *data == constructed.data && *constructor == constructed.constructor
                && matches!(arguments.as_slice(), [argument] if matches!(argument.kind, ExpressionKind::Local(id) if id == local.id)))
    };
    let (first, second) = (single_field(first)?, single_field(second)?);
    let ((failed, _, _), (succeeded, value, step)) = if passes_on(&first.0, &first.1, first.2) {
        (first, second)
    } else if passes_on(&second.0, &second.1, second.2) {
        (second, first)
    } else {
        return None;
    };
    if mentions_local(step, state) {
        return None;
    }
    Some(Propagation { failed, succeeded, value, step: step.clone() })
}

/// An alternative that matches one constructor and binds its one field, with its body.
fn single_field(alternative: &Alternative) -> Option<(Constructed, Local, &Expression)> {
    let [pattern] = alternative.patterns.as_slice() else { return None };
    let PatternKind::Constructor { data, constructor, arguments } = &pattern.kind else {
        return None;
    };
    let [Pattern { kind: PatternKind::Variable(local), monotype }] = arguments.as_slice() else {
        return None;
    };
    let Guarded::Unconditional(body) = &alternative.body else { return None };
    let constructor = *constructor;
    let constructed = Constructed { data: data.clone(), constructor, field: *monotype };
    Some((constructed, local.clone(), body))
}
/// The step with the appender a traversal threads, `append values x`, as `snoc values x`: the
/// loop owns the values it carries, so the append extends them in place.
fn snoc_appends(expression: &mut Expression, appenders: &FxHashSet<LocalId>, carried: LocalId) {
    for_each_child_mut(expression, &mut |child| snoc_appends(child, appenders, carried));
    let ExpressionKind::Apply { function, arguments } = &expression.kind else { return };
    let is_appender = |expression: &Expression| matches!(expression.kind, ExpressionKind::Local(id) if appenders.contains(&id));
    let (values, element) = match (&function.kind, arguments.as_slice()) {
        (_, [values, element]) if is_appender(function) => (values, element),
        (ExpressionKind::Apply { function: inner, arguments: values }, [element])
            if is_appender(inner) && values.len() == 1 =>
        {
            (&values[0], element)
        }
        _ => return,
    };
    if !matches!(values.kind, ExpressionKind::Local(id) if id == carried) {
        return;
    }
    let arguments = vec![values.clone(), element.clone()];
    let kind = ExpressionKind::Foreign { foreign: &Foreign::Snoc, arguments };
    *expression = Expression::new(kind, expression.monotype).replacing(expression.position);
}

/// The value a step that performs nothing gives, `case s of … -> pure x` as `case s of … -> x`.
fn without_effects(expression: &Expression, monotype: MonotypeId) -> Option<Expression> {
    let kind = match &expression.kind {
        ExpressionKind::EffectPure(value) => return Some((**value).clone()),
        ExpressionKind::Let { bindings, body } => ExpressionKind::Let {
            bindings: bindings.clone(),
            body: Box::new(without_effects(body, monotype)?),
        },
        ExpressionKind::If { condition, then, otherwise } => ExpressionKind::If {
            condition: condition.clone(),
            then: Box::new(without_effects(then, monotype)?),
            otherwise: Box::new(without_effects(otherwise, monotype)?),
        },
        ExpressionKind::Case { scrutinees, alternatives } => {
            let alternatives = alternatives.iter().map(|alternative| {
                let Guarded::Unconditional(body) = &alternative.body else { return None };
                Some(Alternative {
                    patterns: alternative.patterns.clone(),
                    body: Guarded::Unconditional(without_effects(body, monotype)?),
                    position: alternative.position,
                })
            });
            let alternatives = alternatives.collect::<Option<Vec<_>>>()?;
            ExpressionKind::Case { scrutinees: scrutinees.clone(), alternatives }
        }
        _ => return None,
    };
    Some(Expression::new(kind, monotype).replacing(expression.position))
}

/// Whether the step calls a function it does not bind, as `traverse`'s own body calls the
/// function it is given: the fold waits until the function is known, which tells whether a step
/// performs anything.
fn calls_unknown(step: &Expression, appenders: &FxHashSet<LocalId>) -> bool {
    let mut bound = FxHashSet::default();
    crate::monomorphic::traversal::visit(step, &mut |node| match &node.kind {
        ExpressionKind::Lambda { parameters, .. } => {
            bound.extend(parameters.iter().map(|parameter| parameter.id));
        }
        ExpressionKind::Let { bindings, .. } => {
            bound.extend(bindings.iter().map(|binding| binding.local.id));
        }
        ExpressionKind::EffectBind { local, .. } => {
            bound.insert(local.id);
        }
        _ => {}
    });
    let mut calls = false;
    crate::monomorphic::traversal::visit(step, &mut |node| {
        let ExpressionKind::Apply { function, .. } = &node.kind else { return };
        calls |= matches!(function.kind, ExpressionKind::Local(id)
            if !bound.contains(&id) && !appenders.contains(&id));
    });
    calls
}

/// The pure bindings a step makes before it performs anything, `let a = f x in do …`, and what
/// follows them.
fn leading_bindings(body: &Expression) -> (Vec<Binding>, &Expression) {
    let mut leading = vec![];
    let mut body = body;
    while let ExpressionKind::Let { bindings, body: inner } = &body.kind {
        leading.extend(bindings.iter().cloned());
        body = inner;
    }
    (leading, body)
}
