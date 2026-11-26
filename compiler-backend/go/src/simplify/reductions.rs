use rustc_hash::FxHashMap;

use super::Simplifier;
use super::choice::operation;
use super::short_circuit::mentions;
use crate::foreign::{self, Comparison, Foreign, Iteration, Operator};
use crate::monomorphic::{
    Binding, Expression, ExpressionKind, Guarded, Literal, Local, LocalId, PatternKind,
};
use crate::monotype::{Monotype, MonotypeId};
use crate::purity::is_within_size;

const COPIED_CALLBACK_SIZE: usize = 160;

struct Seeded {
    nothing: usize,
    just: usize,
    previous: Local,
    element: Local,
    chosen: Expression,
}

impl Simplifier<'_> {
    pub(super) fn reduction(
        &mut self,
        foreign: &'static Foreign,
        arguments: Vec<Expression>,
        monotype: MonotypeId,
    ) -> Result<Expression, Vec<Expression>> {
        if let Foreign::Operator(Operator::ArrayLength) = foreign {
            return self.counted(arguments, monotype);
        }
        let Foreign::Call { boundary, .. } = foreign else { return Err(arguments) };
        if boundary.iteration.is_some_and(|iteration| iteration != Iteration::ZipWith) {
            let arguments = match self.distributed(foreign, arguments, monotype) {
                Ok(distributed) => return Ok(distributed),
                Err(arguments) => arguments,
            };
            return self.reduced_iteration(foreign, boundary.iteration, arguments, monotype);
        }
        Err(arguments)
    }

    /// Whether a map's callback returns the elements of an array literal as they are, through a
    /// newtype's coercion at most: `map (un FilePath) [ directory, name ]` is the literal coerced.
    /// The literal is new either way; an array that might be shared stays copied, as
    /// `unsafeRefEq` tells a mapped array from its source.
    fn maps_identity(&self, arguments: &[Expression]) -> bool {
        let [callback, array] = arguments else { return false };
        if !matches!(array.kind, ExpressionKind::Array(_)) {
            return false;
        }
        let (parameters, body) = match &callback.kind {
            ExpressionKind::Lambda { parameters, body } => (parameters.as_slice(), body.as_ref()),
            ExpressionKind::Function(id) => match self.functions[id.0 as usize].as_ref() {
                Some(function) => (function.parameters.as_slice(), &function.body),
                None => return false,
            },
            _ => return false,
        };
        let [parameter] = parameters else { return false };
        // A coercion to another representation, `unsafeToForeign`'s, converts each element.
        if !self.monotypes.same_without_causes(parameter.monotype, body.monotype) {
            return false;
        }
        let mut body = body;
        while let ExpressionKind::Coerce(value) = &body.kind {
            body = value;
        }
        matches!(body.kind, ExpressionKind::Local(local) if local == parameter.id)
    }

    fn reduced_iteration(
        &mut self,
        foreign: &'static Foreign,
        iteration: Option<Iteration>,
        arguments: Vec<Expression>,
        monotype: MonotypeId,
    ) -> Result<Expression, Vec<Expression>> {
        match iteration {
            Some(Iteration::FoldLeft) => self.seeded_choice(arguments, monotype),
            Some(Iteration::FoldRight) => self.leftward(arguments, monotype),
            Some(Iteration::Map) if self.maps_identity(&arguments) => {
                let array = arguments
                    .into_iter()
                    .nth(1)
                    .expect("invariant violated: map has two arguments");
                Ok(self.coerce(array, monotype))
            }
            Some(Iteration::Map) => self.positional(foreign, arguments, monotype),
            _ => Err(arguments),
        }
    }

    fn distributed(
        &mut self,
        consumer: &'static Foreign,
        mut arguments: Vec<Expression>,
        monotype: MonotypeId,
    ) -> Result<Expression, Vec<Expression>> {
        let Some((array, rest)) = arguments.split_last() else { return Err(arguments) };
        let copyable = rest.iter().all(|argument| is_within_size(argument, COPIED_CALLBACK_SIZE));
        if !copyable || !is_positional_choice(array) {
            return Err(arguments);
        }
        let array = arguments.pop().expect("invariant violated: the array was just matched");
        let ExpressionKind::If { condition, then, otherwise } = array.kind else {
            unreachable!("invariant violated: the array was just matched as a choice")
        };
        let mut copied = arguments.clone();
        for argument in &mut copied {
            self.rename(argument, &mut FxHashMap::default());
        }
        copied.push(*then);
        arguments.push(*otherwise);
        let then = self.foreign(consumer, copied, monotype);
        let otherwise = self.foreign(consumer, arguments, monotype);
        let chosen =
            ExpressionKind::If { condition, then: Box::new(then), otherwise: Box::new(otherwise) };
        Ok(Expression::new(chosen, monotype))
    }

    fn positional(
        &mut self,
        map: &'static Foreign,
        arguments: Vec<Expression>,
        monotype: MonotypeId,
    ) -> Result<Expression, Vec<Expression>> {
        let [callback, range] = arguments.as_slice() else { return Err(arguments) };
        let Some(array) = positions_of(range) else { return Err(arguments) };
        let single = matches!(&callback.kind, ExpressionKind::Lambda { parameters, .. } if parameters.len() == 1);
        let Monotype::Array(element) = *self.monotypes.get(array.monotype) else {
            return Err(arguments);
        };
        if !single || !is_within_size(callback, COPIED_CALLBACK_SIZE) {
            return Err(arguments);
        }
        let array = array.clone();
        let [callback, range] = <[Expression; 2]>::try_from(arguments)
            .unwrap_or_else(|_| unreachable!("invariant violated: map has two arguments"));
        let integer = self.monotypes.intern(Monotype::Int);
        let boolean = self.monotypes.intern(Monotype::Boolean);
        let literal = |value| {
            let kind = ExpressionKind::Literal(Literal::Int(value));
            Expression::new(kind, integer)
        };
        let mut copied = callback.clone();
        self.rename(&mut copied, &mut FxHashMap::default());
        let both = ExpressionKind::Array(vec![literal(0), literal(-1)]);
        let both = Expression::new(both, range.monotype);
        let both = ExpressionKind::Foreign { foreign: map, arguments: vec![copied, both] };
        let ExpressionKind::Lambda { mut parameters, body } = callback.kind else {
            unreachable!("invariant violated: the callback was just matched as a lambda")
        };
        let ignored = self.named_local("ignored", element);
        let produced = body.monotype;
        parameters.push(ignored);
        let indexed = self.monotypes.function(element, produced);
        let indexed = self.monotypes.function(integer, indexed);
        let indexed = Expression::new(ExpressionKind::Lambda { parameters, body }, indexed);
        let every = ExpressionKind::Foreign {
            foreign: &foreign::ARRAY_MAP_WITH_INDEX,
            arguments: vec![indexed, array.clone()],
        };
        let length = operation(Operator::ArrayLength, vec![array], integer);
        let empty = vec![length, literal(0)];
        let empty = operation(Operator::Compare(Comparison::Equal), empty, boolean);
        let chosen = ExpressionKind::If {
            condition: Box::new(empty),
            then: Box::new(Expression::new(both, monotype)),
            otherwise: Box::new(Expression::new(every, monotype)),
        };
        Ok(Expression::new(chosen, monotype))
    }

    fn seeded_choice(
        &mut self,
        arguments: Vec<Expression>,
        monotype: MonotypeId,
    ) -> Result<Expression, Vec<Expression>> {
        let Some(seeded) = seeded(&arguments) else { return Err(arguments) };
        let Monotype::Array(element) = *self.monotypes.get(arguments[2].monotype) else {
            return Err(arguments);
        };
        if !matches!(self.monotypes.get(element), Monotype::Int | Monotype::Char) {
            return Err(arguments);
        }
        let [_, initial, array] = <[Expression; 3]>::try_from(arguments)
            .unwrap_or_else(|_| unreachable!("invariant violated: a fold has three arguments"));
        let ExpressionKind::Construct { data, .. } = initial.kind else {
            unreachable!("invariant violated: a seeded fold starts from a constructor")
        };
        let Seeded { nothing, just, previous, element: current, chosen } = seeded;
        let integer = self.monotypes.intern(Monotype::Int);
        let boolean = self.monotypes.intern(Monotype::Boolean);
        let array_local = self.named_local("array", array.monotype);
        let length = operation(Operator::ArrayLength, vec![array_local.expression()], integer);
        let zero = Expression::new(ExpressionKind::Literal(Literal::Int(0)), integer);
        let empty = operation(Operator::Compare(Comparison::Equal), vec![length, zero], boolean);
        let first = Expression::new(ExpressionKind::Literal(Literal::Int(0)), integer);
        let first = operation(Operator::ArrayIndex, vec![array_local.expression(), first], element);
        let choose = self.monotypes.function(current.monotype, element);
        let choose = self.monotypes.function(previous.monotype, choose);
        let choose = Expression::new(
            ExpressionKind::Lambda { parameters: vec![previous, current], body: Box::new(chosen) },
            choose,
        );
        let folded = ExpressionKind::Foreign {
            foreign: foreign::array_fold(),
            arguments: vec![choose, first, array_local.expression()],
        };
        let folded = Expression::new(folded, element);
        let nothing = ExpressionKind::Construct {
            data: data.clone(),
            constructor: nothing,
            arguments: vec![],
        };
        let found = ExpressionKind::Construct { data, constructor: just, arguments: vec![folded] };
        let chosen = ExpressionKind::If {
            condition: Box::new(empty),
            then: Box::new(Expression::new(nothing, monotype)),
            otherwise: Box::new(Expression::new(found, monotype)),
        };
        let chosen = Expression::new(chosen, monotype);
        Ok(self.let_bindings(vec![Binding { local: array_local, value: array }], chosen))
    }

    fn counted(
        &mut self,
        arguments: Vec<Expression>,
        monotype: MonotypeId,
    ) -> Result<Expression, Vec<Expression>> {
        let [array] = arguments.as_slice() else { return Err(arguments) };
        if self.is_empty_array(array) {
            return Ok(Expression::new(ExpressionKind::Literal(Literal::Int(0)), monotype));
        }
        let ExpressionKind::Foreign {
            foreign: Foreign::Call { boundary, .. },
            arguments: filtered,
        } = &array.kind
        else {
            return Err(arguments);
        };
        let [predicate, source] = filtered.as_slice() else { return Err(arguments) };
        let filters = boundary.iteration == Some(Iteration::Filter);
        let counts_ints = matches!(
            self.monotypes.get(source.monotype),
            Monotype::Array(element) if matches!(self.monotypes.get(*element), Monotype::Int)
        );
        let single = matches!(&predicate.kind, ExpressionKind::Lambda { parameters, .. } if parameters.len() == 1);
        if !(filters && counts_ints && single) {
            return Err(arguments);
        }
        let [array] = <[Expression; 1]>::try_from(arguments)
            .unwrap_or_else(|_| unreachable!("invariant violated: length has one argument"));
        let ExpressionKind::Foreign { arguments: filtered, .. } = array.kind else {
            unreachable!("invariant violated: the array was just matched as a filter")
        };
        let [predicate, source] = <[Expression; 2]>::try_from(filtered)
            .unwrap_or_else(|_| unreachable!("invariant violated: filter has two arguments"));
        let ExpressionKind::Lambda { mut parameters, body: condition } = predicate.kind else {
            unreachable!("invariant violated: the predicate was just matched as a lambda")
        };
        let element = parameters.remove(0);
        let count = self.named_local("count", monotype);
        let one = Expression::new(ExpressionKind::Literal(Literal::Int(1)), monotype);
        let zero = Expression::new(ExpressionKind::Literal(Literal::Int(0)), monotype);
        let counted =
            ExpressionKind::If { condition, then: Box::new(one), otherwise: Box::new(zero) };
        let counted = Expression::new(counted, monotype);
        let body = operation(Operator::IntAdd, vec![count.expression(), counted], monotype);
        let step_type = self.monotypes.function(element.monotype, monotype);
        let step_type = self.monotypes.function(monotype, step_type);
        let step =
            ExpressionKind::Lambda { parameters: vec![count, element], body: Box::new(body) };
        let initial = Expression::new(ExpressionKind::Literal(Literal::Int(0)), monotype);
        let folded = ExpressionKind::Foreign {
            foreign: foreign::array_fold(),
            arguments: vec![Expression::new(step, step_type), initial, source],
        };
        Ok(Expression::new(folded, monotype))
    }

    fn leftward(
        &mut self,
        arguments: Vec<Expression>,
        monotype: MonotypeId,
    ) -> Result<Expression, Vec<Expression>> {
        if !matches!(self.monotypes.get(monotype), Monotype::Int) {
            return Err(arguments);
        }
        let ExpressionKind::Lambda { parameters, body } = &arguments[0].kind else {
            return Err(arguments);
        };
        let [_, accumulator] = parameters.as_slice() else { return Err(arguments) };
        if !combines(body, accumulator.id) {
            return Err(arguments);
        }
        let [step, initial, array] = <[Expression; 3]>::try_from(arguments)
            .unwrap_or_else(|_| unreachable!("invariant violated: a fold has three arguments"));
        let ExpressionKind::Lambda { mut parameters, body } = step.kind else {
            unreachable!("invariant violated: the step was just matched as a lambda")
        };
        parameters.swap(0, 1);
        let step_type = self.monotypes.function(parameters[1].monotype, monotype);
        let step_type = self.monotypes.function(parameters[0].monotype, step_type);
        let step = Expression::new(ExpressionKind::Lambda { parameters, body }, step_type);
        let folded = ExpressionKind::Foreign {
            foreign: foreign::array_fold(),
            arguments: vec![step, initial, array],
        };
        Ok(Expression::new(folded, monotype))
    }
}

fn is_positional_choice(array: &Expression) -> bool {
    let ExpressionKind::If { condition, then, otherwise } = &array.kind else { return false };
    let ExpressionKind::Foreign { foreign: Foreign::Operator(operator), arguments } =
        &condition.kind
    else {
        return false;
    };
    let empty = matches!(operator, Operator::Compare(Comparison::Equal))
        && matches!(
            arguments.as_slice(),
            [length, zero]
                if matches!(length.kind, ExpressionKind::Foreign {
                    foreign: Foreign::Operator(Operator::ArrayLength),
                    ..
                }) && matches!(zero.kind, ExpressionKind::Literal(Literal::Int(0)))
        );
    let both = matches!(&then.kind, ExpressionKind::Foreign { arguments, .. }
        if matches!(arguments.as_slice(), [_, positions]
            if matches!(&positions.kind, ExpressionKind::Array(elements) if elements.len() == 2)));
    let every = matches!(&otherwise.kind, ExpressionKind::Foreign { foreign, .. }
        if foreign.calls(foreign::ARRAY_MAP_WITH_INDEX));
    empty && both && every
}

fn positions_of(range: &Expression) -> Option<&Expression> {
    let ExpressionKind::Foreign { foreign: Foreign::Range, arguments } = &range.kind else {
        return None;
    };
    let [first, last] = arguments.as_slice() else { return None };
    if !matches!(first.kind, ExpressionKind::Literal(Literal::Int(0))) {
        return None;
    }
    let ExpressionKind::Foreign { foreign: Foreign::Operator(operator), arguments } = &last.kind
    else {
        return None;
    };
    let [length, offset] = arguments.as_slice() else { return None };
    let before_end = matches!(
        (operator, &offset.kind),
        (Operator::IntSubtract, ExpressionKind::Literal(Literal::Int(1)))
            | (Operator::IntAdd, ExpressionKind::Literal(Literal::Int(-1)))
    );
    let ExpressionKind::Foreign { foreign: Foreign::Operator(Operator::ArrayLength), arguments } =
        &length.kind
    else {
        return None;
    };
    let [array] = arguments.as_slice() else { return None };
    (before_end && matches!(array.kind, ExpressionKind::Local(_))).then_some(array)
}

fn seeded(arguments: &[Expression]) -> Option<Seeded> {
    let [step, initial, _] = arguments else { return None };
    let ExpressionKind::Construct { constructor: nothing, arguments: fields, .. } = &initial.kind
    else {
        return None;
    };
    if !fields.is_empty() {
        return None;
    }
    let ExpressionKind::Lambda { parameters, body } = &step.kind else { return None };
    let [accumulator, element] = parameters.as_slice() else { return None };
    let ExpressionKind::Case { scrutinees, alternatives } = &body.kind else { return None };
    let [scrutinee] = scrutinees.as_slice() else { return None };
    if !matches!(scrutinee.kind, ExpressionKind::Local(id) if id == accumulator.id) {
        return None;
    }
    let just = just_constructor(body)?;
    let mut started = false;
    let mut continued = None;
    for alternative in alternatives {
        let Guarded::Unconditional(result) = &alternative.body else { return None };
        let ExpressionKind::Construct { constructor, arguments: built, .. } = &result.kind else {
            return None;
        };
        let [value] = built.as_slice() else { return None };
        if *constructor != just {
            return None;
        }
        match &alternative.patterns[0].kind {
            PatternKind::Constructor { constructor, arguments, .. } if *constructor == just => {
                let [field] = arguments.as_slice() else { return None };
                let PatternKind::Variable(previous) = &field.kind else { return None };
                if continued.is_some() || !chooses(value, previous.id, element.id) {
                    return None;
                }
                continued = Some((previous.clone(), value.clone()));
            }
            PatternKind::Constructor { constructor, .. } if constructor == nothing => {
                if started || !matches!(value.kind, ExpressionKind::Local(id) if id == element.id) {
                    return None;
                }
                started = true;
            }
            PatternKind::Wildcard if continued.is_some() && !started => {
                if !matches!(value.kind, ExpressionKind::Local(id) if id == element.id) {
                    return None;
                }
                started = true;
            }
            _ => return None,
        }
    }
    let (previous, chosen) = continued.filter(|_| started)?;
    if mentions(&chosen, accumulator.id) {
        return None;
    }
    Some(Seeded { nothing: *nothing, just, previous, element: element.clone(), chosen })
}

fn just_constructor(body: &Expression) -> Option<usize> {
    let ExpressionKind::Case { alternatives, .. } = &body.kind else { return None };
    alternatives.iter().find_map(|alternative| match &alternative.patterns[0].kind {
        PatternKind::Constructor { constructor, arguments, .. } if arguments.len() == 1 => {
            Some(*constructor)
        }
        _ => None,
    })
}

fn chooses(value: &Expression, previous: LocalId, element: LocalId) -> bool {
    match &value.kind {
        ExpressionKind::Let { body, .. } => chooses(body, previous, element),
        ExpressionKind::If { then, otherwise, .. } => {
            let local = |expression: &Expression| match expression.kind {
                ExpressionKind::Local(id) => Some(id),
                _ => None,
            };
            matches!(
                (local(then), local(otherwise)),
                (Some(left), Some(right))
                    if (left == previous && right == element) || (left == element && right == previous)
            )
        }
        _ => false,
    }
}

fn combines(body: &Expression, accumulator: LocalId) -> bool {
    let ExpressionKind::Foreign { foreign: Foreign::Operator(operator), arguments } = &body.kind
    else {
        return false;
    };
    let associative = matches!(
        operator,
        Operator::IntAdd
            | Operator::IntMultiply
            | Operator::IntAnd
            | Operator::IntOr
            | Operator::IntXor
    );
    let [left, right] = arguments.as_slice() else { return false };
    let is_accumulator = |expression: &Expression| matches!(expression.kind, ExpressionKind::Local(id) if id == accumulator);
    associative
        && match (is_accumulator(left), is_accumulator(right)) {
            (true, false) => !mentions(right, accumulator),
            (false, true) => !mentions(left, accumulator),
            _ => false,
        }
}
