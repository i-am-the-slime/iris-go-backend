//! Pure code over values known at compile time, worked out at compile time.
//!
//! A protocol buffer codec derived from a message type, `fieldCodec (Proxy :: Proxy Int) 3`,
//! is a function of constants that builds a record of closures; the table and the writers a
//! message's codec makes of its fields are arrays of such records, appended, folded and sorted.
//! Each step is a value the compiler can compute:
//!
//! - a call that builds functions from constant arguments is copied to its call, so that its
//!   fields resolve there;
//! - a call with constant arguments, of a function or of a local one such as a join point, that
//!   evaluates to a small constant is that constant, and so is a field of one that builds a
//!   record whose field is constant;
//! - arrays of known elements are appended, replicated, reversed, updated, indexed, measured,
//!   mapped, folded and sorted element by element;
//! - an effect run for each element of one is run for each, in order, as straight-line code.
//!
//! Every step works on arrays of at most [`LITERAL_ELEMENTS`] elements, copies functions of at
//! most [`EVALUATED_CALL_SIZE`] nodes and keeps constants of at most [`CONSTANT_RESULT_SIZE`], so
//! the work stays bounded; a call evaluated in vain is remembered and not tried again.

use rustc_hash::FxHashMap;
use smol_str::SmolStr;

use super::{Simplifier, substitute};
use crate::foreign::{
    ARRAY_APPEND, ARRAY_REPLICATE, ARRAY_REVERSE, ARRAY_SORT_BY, Foreign, Iteration, Operator,
};
use crate::monomorphic::traversal::{for_each_child_mut, visit};
use crate::monomorphic::{Binding, Expression, ExpressionKind, FunctionId, Literal, Local};
use crate::monotype::{Monotype, MonotypeId};
use crate::purity::{is_discardable, is_trivial, is_within_size, occurrences_up_to};

/// The size of a function copied to a call whose arguments are all constants.
const EVALUATED_CALL_SIZE: usize = 320;

/// The size of a function evaluated at compile time for a call whose arguments are all constants.
const EVALUATED_CONSTANT_SIZE: usize = 240;

/// The size of a constant a call evaluated at compile time may be.
const CONSTANT_RESULT_SIZE: usize = 64;

/// The longest array literal worked on element by element.
pub(super) const LITERAL_ELEMENTS: usize = 32;

impl Simplifier<'_> {
    /// The parameters and body of a function to copy to a call with constant arguments that
    /// builds functions: a codec, a record of readers and writers. Copied, its result is a
    /// value the call's surroundings take apart, and the closures it builds run as code there.
    pub(super) fn evaluated_call(
        &self,
        id: FunctionId,
        arguments: &[Expression],
    ) -> Option<(Vec<Local>, Expression)> {
        if id == self.entry || self.recursive[id.0 as usize] {
            return None;
        }
        let function = self.functions[id.0 as usize].as_ref()?;
        let saturated =
            !function.parameters.is_empty() && arguments.len() >= function.parameters.len();
        let evaluable = saturated
            && arguments.iter().all(is_constant)
            && self.builds_functions(function.result, 2)
            && self.sizes[id.0 as usize] <= EVALUATED_CALL_SIZE;
        evaluable.then(|| (function.parameters.clone(), function.body.clone()))
    }

    /// What a call with constant arguments evaluates to, worked out at compile time, when that is
    /// a small constant: `enumFromIndex (Proxy :: Proxy rep) 0` is `Just (Inl NoArguments)`. The
    /// callee is copied to the call and simplified, and the copy kept only if it is a constant;
    /// the answer is remembered for the same call elsewhere.
    pub(super) fn evaluated_constant(
        &mut self,
        id: FunctionId,
        arguments: &[Expression],
        monotype: MonotypeId,
    ) -> Option<Expression> {
        if self.fuel == 0 || id == self.entry || self.recursive[id.0 as usize] {
            return None;
        }
        let function = self.functions[id.0 as usize].as_ref()?;
        let evaluable = !function.parameters.is_empty()
            && arguments.len() == function.parameters.len()
            && self.sizes[id.0 as usize] <= EVALUATED_CONSTANT_SIZE
            && !self.builds_functions(monotype, 2)
            && self.monotypes.effect_result(monotype).is_none()
            && arguments.iter().all(is_constant);
        if !evaluable {
            return None;
        }
        let key = (id, arguments.to_vec(), None);
        if let Some(known) = self.evaluated_constants.get(&key) {
            return known.clone();
        }
        self.evaluated_constants.insert(key.clone(), None);
        let fuel = self.fuel;
        let mut renaming = FxHashMap::default();
        let parameters: Vec<Local> = function
            .parameters
            .clone()
            .iter()
            .map(|parameter| self.rename_binder(parameter, &mut renaming))
            .collect();
        let mut body = self.functions[id.0 as usize].as_ref()?.body.clone();
        self.rename(&mut body, &mut renaming);
        self.fuel -= 1;
        let evaluated = self.beta(parameters, body, arguments.to_vec(), monotype);
        let constant = is_constant(&evaluated) && is_within_size(&evaluated, CONSTANT_RESULT_SIZE);
        let evaluated = constant.then_some(evaluated);
        if evaluated.is_none() {
            self.fuel = fuel;
        }
        self.evaluated_constants.insert(key, evaluated.clone());
        evaluated
    }

    /// Whether a value of the type holds functions, within `depth` records and arrays.
    pub(super) fn builds_functions(&self, monotype: MonotypeId, depth: usize) -> bool {
        match self.monotypes.get(monotype) {
            Monotype::Function(..) => true,
            Monotype::Record(fields) if depth > 0 => {
                let fields = fields.clone();
                fields.iter().any(|field| self.builds_functions(field.monotype, depth - 1))
            }
            Monotype::Data(_) => self.monotypes.holds_function(monotype),
            Monotype::Array(element) if depth > 0 => {
                let element = *element;
                self.builds_functions(element, depth - 1)
            }
            _ => false,
        }
    }
}

/// A value known at compile time: a literal, a function, a constructor, an array or a record of
/// such values.
fn is_constant(expression: &Expression) -> bool {
    match &expression.kind {
        ExpressionKind::Literal(_) | ExpressionKind::Unit | ExpressionKind::Function(_) => true,
        ExpressionKind::Foreign { arguments, .. } => arguments.is_empty(),
        ExpressionKind::Construct { arguments, .. } | ExpressionKind::Array(arguments) => {
            arguments.len() <= LITERAL_ELEMENTS && arguments.iter().all(is_constant)
        }
        ExpressionKind::Record(fields) => fields.iter().all(|(_, value)| is_constant(value)),
        ExpressionKind::Coerce(value) => is_constant(value),
        _ => false,
    }
}

/// The size of a callback copied to each element of an array literal.
const COPIED_STEP_SIZE: usize = 80;

/// How much a fold or a map over an array literal copies of its callback, over all elements.
const COPIED_TOTAL_SIZE: usize = 160;

/// The size of an array literal of lambdas copied to each operation that works it out.
const COPIED_ARRAY_SIZE: usize = 160;

impl Simplifier<'_> {
    /// An operation on array literals worked out on their elements: `[a] <> [b, c]` is
    /// `[a, b, c]`, `replicate 3 x` is `[x, x, x]`, `map f [a, b]` is `[f a, f b]`, a fold is
    /// its steps one after another, `updateAt 1 x [a, b]` is `Just [a, x]` and a sort whose
    /// comparisons all fold to constants is the literal in its sorted order.
    pub(super) fn literal_array_operation(
        &mut self,
        foreign: &'static Foreign,
        arguments: Vec<Expression>,
        monotype: MonotypeId,
    ) -> Result<Expression, Vec<Expression>> {
        if self.fuel == 0 {
            return Err(arguments);
        }
        if foreign.calls(ARRAY_APPEND) {
            return self.appended(arguments, monotype);
        }
        if foreign.calls(ARRAY_REPLICATE) {
            return replicated(arguments, monotype);
        }
        if foreign.calls(ARRAY_REVERSE) {
            return reversed(arguments);
        }
        if foreign.calls(ARRAY_SORT_BY) {
            return self.sorted(arguments, monotype);
        }
        if let Foreign::UpdateAt = foreign {
            return self.updated(arguments, monotype);
        }
        if let Foreign::ArrayUpdated = foreign {
            return replaced(arguments, monotype);
        }
        if let Foreign::Operator(Operator::ArrayIndex) = foreign {
            return indexed(arguments);
        }
        if let Foreign::Operator(Operator::ArrayLength) = foreign {
            return measured(arguments, monotype);
        }
        let Foreign::Call { boundary, .. } = foreign else { return Err(arguments) };
        match boundary.iteration {
            Some(Iteration::FoldLeft) => self.folded(arguments, monotype, Direction::Leftward),
            Some(Iteration::FoldRight) => self.folded(arguments, monotype, Direction::Rightward),
            Some(Iteration::Map) => self.mapped(arguments, monotype, false),
            Some(Iteration::MapWithIndex) => self.mapped(arguments, monotype, true),
            _ => Err(arguments),
        }
    }

    fn appended(
        &mut self,
        arguments: Vec<Expression>,
        monotype: MonotypeId,
    ) -> Result<Expression, Vec<Expression>> {
        let [left, right] = arguments.as_slice() else { return Err(arguments) };
        let (Some(left), Some(right)) = (literal_elements(left), literal_elements(right)) else {
            return Err(arguments);
        };
        if left.len() + right.len() > LITERAL_ELEMENTS {
            return Err(arguments);
        }
        let elements = left.iter().chain(right).cloned().collect();
        Ok(Expression::new(ExpressionKind::Array(elements), monotype))
    }

    /// `updateAt index value array`, with the index a literal and the array one too.
    fn updated(
        &mut self,
        arguments: Vec<Expression>,
        monotype: MonotypeId,
    ) -> Result<Expression, Vec<Expression>> {
        let [_, _, index, value, array] = arguments.as_slice() else { return Err(arguments) };
        let (Some(index), Some(elements)) = (int_literal(index), literal_elements(array)) else {
            return Err(arguments);
        };
        if !is_trivial(value) && !is_constant(value) {
            return Err(arguments);
        }
        let position = usize::try_from(index).ok().filter(|&position| position < elements.len());
        if position.is_some_and(|position| !is_discardable(&elements[position])) {
            return Err(arguments);
        }
        // The choice `updateAt` makes, at the Maybe it answers with, decides on the literal's length.
        match self.update_choice(arguments.clone(), monotype) {
            Some(choice) => Ok(self.expression(choice)),
            None => Err(arguments),
        }
    }

    /// A fold over an array literal, one step after another: `foldl f z [a, b]` is
    /// `f (f z a) b` and `foldr f z [a, b]` is `f a (f b z)`.
    fn folded(
        &mut self,
        arguments: Vec<Expression>,
        monotype: MonotypeId,
        direction: Direction,
    ) -> Result<Expression, Vec<Expression>> {
        let [step, _, array] = arguments.as_slice() else { return Err(arguments) };
        // A fold that builds an action, `foldM`'s, stays a loop the action runs.
        if self.monotypes.effect_result(monotype).is_some() {
            return Err(arguments);
        }
        if !literal_elements(array)
            .is_some_and(|elements| copies_fit(step, elements.len(), &self.sizes))
        {
            return Err(arguments);
        }
        let original = arguments.clone();
        let [step, initial, array]: [Expression; 3] =
            arguments.try_into().unwrap_or_else(|_| unreachable!("a fold has three arguments"));
        let ExpressionKind::Array(elements) = array.kind else { unreachable!("matched above") };
        let mut accumulated = initial;
        let steps: Box<dyn Iterator<Item = Expression>> = match direction {
            Direction::Leftward => Box::new(elements.into_iter()),
            Direction::Rightward => Box::new(elements.into_iter().rev()),
        };
        for element in steps {
            let step = self.renamed(&step);
            let operands = match direction {
                Direction::Leftward => vec![accumulated, element],
                Direction::Rightward => vec![element, accumulated],
            };
            accumulated = self.apply(step, operands, monotype);
        }
        within_copied(accumulated, original)
    }

    /// `map f [a, b]` is `[f a, f b]`, and `mapWithIndex f [a, b]` is `[f 0 a, f 1 b]`.
    fn mapped(
        &mut self,
        arguments: Vec<Expression>,
        monotype: MonotypeId,
        indexed: bool,
    ) -> Result<Expression, Vec<Expression>> {
        let [callback, array] = arguments.as_slice() else { return Err(arguments) };
        if !literal_elements(array)
            .is_some_and(|elements| copies_fit(callback, elements.len(), &self.sizes))
        {
            return Err(arguments);
        }
        let Monotype::Array(produced) = *self.monotypes.get(monotype) else {
            return Err(arguments);
        };
        let original = arguments.clone();
        let integer = self.monotypes.intern(Monotype::Int);
        let [callback, array]: [Expression; 2] =
            arguments.try_into().unwrap_or_else(|_| unreachable!("a map has two arguments"));
        let ExpressionKind::Array(elements) = array.kind else { unreachable!("matched above") };
        let elements = elements
            .into_iter()
            .enumerate()
            .map(|(index, element)| {
                let callback = self.renamed(&callback);
                let operands = match indexed {
                    true => vec![int(index as i64, integer), element],
                    false => vec![element],
                };
                self.apply(callback, operands, produced)
            })
            .collect();
        within_copied(Expression::new(ExpressionKind::Array(elements), monotype), original)
    }

    /// `sortBy compare toInt array` of a literal whose elements every comparison orders at
    /// compile time, as the stable merge sort of `Data.Array` orders them.
    fn sorted(
        &mut self,
        arguments: Vec<Expression>,
        monotype: MonotypeId,
    ) -> Result<Expression, Vec<Expression>> {
        let [comparison, ordering_to_int, array] = arguments.as_slice() else {
            return Err(arguments);
        };
        let Some(elements) = literal_elements(array) else { return Err(arguments) };
        if !is_known_step(comparison) || !is_known_step(ordering_to_int) {
            return Err(arguments);
        }
        let integer = self.monotypes.intern(Monotype::Int);
        let ordering = self.monotypes.result_after(comparison.monotype, 2);
        let (comparison, ordering_to_int) = (comparison.clone(), ordering_to_int.clone());
        let elements = elements.to_vec();
        let mut after = |simplifier: &mut Self, left: usize, right: usize| {
            let compare = simplifier.renamed(&comparison);
            let operands = vec![elements[left].clone(), elements[right].clone()];
            let compared = simplifier.apply(compare, operands, ordering);
            let to_int = simplifier.renamed(&ordering_to_int);
            let compared = simplifier.apply(to_int, vec![compared], integer);
            int_literal(&compared).map(|value| value > 0)
        };
        let Some(order) = merge_sorted(self, (0..elements.len()).collect(), &mut after) else {
            return Err(arguments);
        };
        let mut elements: Vec<Option<Expression>> = elements.into_iter().map(Some).collect();
        let sorted = order.into_iter().filter_map(|index| elements[index].take()).collect();
        Ok(Expression::new(ExpressionKind::Array(sorted), monotype))
    }

    /// Whether an effect run for each element of an array is run for each in turn: the array is
    /// a literal of values that say more than a number, such as records of writers, and the
    /// effect small enough to copy to each element. Over numbers, the loop reads as well.
    pub(super) fn runs_each_of_literal(&self, array: &Expression, body: &Expression) -> bool {
        let structured = |element: &Expression| {
            !matches!(element.kind, ExpressionKind::Literal(_) | ExpressionKind::Unit)
        };
        self.fuel > 0
            && literal_elements(array).is_some_and(|elements| {
                elements.iter().any(structured)
                    && (elements.len() <= 1
                        || is_within_size(
                            body,
                            COPIED_STEP_SIZE.min(COPIED_TOTAL_SIZE / elements.len()),
                        ))
            })
    }

    /// An effect run for each element of an array literal, run for each in turn.
    pub(super) fn each_of_literal(
        &mut self,
        array: Expression,
        element: Local,
        body: Expression,
        monotype: MonotypeId,
    ) -> Expression {
        let ExpressionKind::Array(elements) = array.kind else { unreachable!("matched above") };
        let unit = self.monotypes.intern(Monotype::Unit);
        let ran = self.monotypes.effect_result(body.monotype).unwrap_or(unit);
        let mut sequence =
            Expression::new(ExpressionKind::EffectPure(Box::new(unit_value(unit))), monotype);
        for value in elements.into_iter().rev() {
            let mut renaming = FxHashMap::default();
            let local = self.rename_binder(&element, &mut renaming);
            let mut action = body.clone();
            self.rename(&mut action, &mut renaming);
            let bindings = vec![Binding { local, value }];
            let action = Expression::new(
                ExpressionKind::Let { bindings, body: Box::new(action) },
                body.monotype,
            );
            let action = self.expression(action);
            let ignored = self.named_local("ignored", ran);
            sequence = self.effect_bind(action, ignored, sequence, monotype);
        }
        sequence
    }

    fn renamed(&mut self, expression: &Expression) -> Expression {
        let mut copy = expression.clone();
        self.rename(&mut copy, &mut FxHashMap::default());
        copy
    }
}

/// The positions in the order a stable merge sort puts them, as `Data.Array.sortBy` does: `after`
/// says whether the element at the first position goes after the one at the second, or `None`
/// when that is not known, which stops the sort.
fn merge_sorted<S>(
    state: &mut S,
    positions: Vec<usize>,
    after: &mut impl FnMut(&mut S, usize, usize) -> Option<bool>,
) -> Option<Vec<usize>> {
    if positions.len() < 2 {
        return Some(positions);
    }
    let mut right = positions;
    let left = right.drain(..right.len() / 2).collect();
    let left = merge_sorted(state, left, after)?;
    let right = merge_sorted(state, right, after)?;
    let mut merged = Vec::with_capacity(left.len() + right.len());
    let (mut from_left, mut from_right) =
        (left.into_iter().peekable(), right.into_iter().peekable());
    while let (Some(&first), Some(&second)) = (from_left.peek(), from_right.peek()) {
        match after(state, first, second)? {
            true => merged.extend(from_right.next()),
            false => merged.extend(from_left.next()),
        }
    }
    merged.extend(from_left);
    merged.extend(from_right);
    Some(merged)
}

#[derive(Clone, Copy)]
enum Direction {
    Leftward,
    Rightward,
}

/// A copy of an array literal with the element at a literal index within it replaced.
fn replaced(
    arguments: Vec<Expression>,
    monotype: MonotypeId,
) -> Result<Expression, Vec<Expression>> {
    let [index, value, array] = arguments.as_slice() else { return Err(arguments) };
    let (Some(index), Some(elements)) = (int_literal(index), literal_elements(array)) else {
        return Err(arguments);
    };
    let Some(position) = usize::try_from(index).ok().filter(|&position| position < elements.len())
    else {
        return Err(arguments);
    };
    if !is_discardable(&elements[position]) {
        return Err(arguments);
    }
    let mut elements = elements.to_vec();
    elements[position] = value.clone();
    Ok(Expression::new(ExpressionKind::Array(elements), monotype))
}

/// The length of an array literal whose elements can be dropped.
fn measured(
    arguments: Vec<Expression>,
    monotype: MonotypeId,
) -> Result<Expression, Vec<Expression>> {
    let [array] = arguments.as_slice() else { return Err(arguments) };
    match literal_elements(array) {
        Some(elements) if elements.iter().all(is_discardable) => {
            Ok(int(elements.len() as i64, monotype))
        }
        _ => Err(arguments),
    }
}

/// The element of an array literal at a literal index within it, the others dropped.
fn indexed(arguments: Vec<Expression>) -> Result<Expression, Vec<Expression>> {
    let [array, index] = arguments.as_slice() else { return Err(arguments) };
    let (Some(index), Some(elements)) = (int_literal(index), literal_elements(array)) else {
        return Err(arguments);
    };
    let Some(position) = usize::try_from(index).ok().filter(|&position| position < elements.len())
    else {
        return Err(arguments);
    };
    let others_dropped = elements
        .iter()
        .enumerate()
        .all(|(other, element)| other == position || is_discardable(element));
    if !others_dropped {
        return Err(arguments);
    }
    Ok(elements[position].clone())
}

/// An array literal in the other order.
fn reversed(mut arguments: Vec<Expression>) -> Result<Expression, Vec<Expression>> {
    let [array] = arguments.as_mut_slice() else { return Err(arguments) };
    let ExpressionKind::Array(elements) = &mut array.kind else { return Err(arguments) };
    elements.reverse();
    Ok(arguments.pop().expect("invariant violated: reverse has one argument"))
}

/// `replicate n x` with a literal count, of a value that is trivial to copy.
fn replicated(
    arguments: Vec<Expression>,
    monotype: MonotypeId,
) -> Result<Expression, Vec<Expression>> {
    let [count, value] = arguments.as_slice() else { return Err(arguments) };
    let Some(count) = int_literal(count) else { return Err(arguments) };
    let count = count.max(0) as usize;
    if count > LITERAL_ELEMENTS || !(is_trivial(value) || is_constant(value) && count <= 1) {
        return Err(arguments);
    }
    let elements = vec![value.clone(); count];
    Ok(Expression::new(ExpressionKind::Array(elements), monotype))
}

/// The elements of an array literal small enough to work on one by one.
fn literal_elements(expression: &Expression) -> Option<&[Expression]> {
    match &expression.kind {
        ExpressionKind::Array(elements) if elements.len() <= LITERAL_ELEMENTS => {
            Some(elements.as_slice())
        }
        _ => None,
    }
}

/// What a fold or a map over a literal worked out to, unless the steps it copied stayed too big
/// to be worth more than the loop: then the operation as it was.
fn within_copied(
    worked_out: Expression,
    original: Vec<Expression>,
) -> Result<Expression, Vec<Expression>> {
    match is_within_size(&worked_out, COPIED_TOTAL_SIZE) {
        true => Ok(worked_out),
        false => Err(original),
    }
}

/// A callback known and small enough to copy to each of `count` elements, a function counted at
/// the size of its body, which the copies inline.
fn copies_fit(callback: &Expression, count: usize, sizes: &[usize]) -> bool {
    let callee = match &callback.kind {
        ExpressionKind::Function(id) => sizes[id.0 as usize],
        ExpressionKind::Apply { function, .. } => match function.kind {
            ExpressionKind::Function(id) => sizes[id.0 as usize],
            _ => 0,
        },
        _ => 0,
    };
    let limit = COPIED_TOTAL_SIZE / count.max(1);
    is_known_step(callback) && callee <= limit && is_within_size(callback, limit)
}

/// A callback whose code is known and small enough to copy to each element.
fn is_known_step(callback: &Expression) -> bool {
    let known = match &callback.kind {
        ExpressionKind::Lambda { .. } | ExpressionKind::Function(_) => true,
        ExpressionKind::Apply { function, .. } => {
            matches!(function.kind, ExpressionKind::Function(_))
        }
        _ => false,
    };
    known && is_within_size(callback, COPIED_STEP_SIZE)
}

/// A constructor with fields, which a case of the lambda it is passed to takes apart.
fn holds_fields(argument: &Expression) -> bool {
    matches!(&argument.kind, ExpressionKind::Construct { arguments, .. } if !arguments.is_empty())
}

fn int_literal(expression: &Expression) -> Option<i64> {
    match &expression.kind {
        ExpressionKind::Literal(Literal::Int(value)) => Some(*value),
        _ => None,
    }
}

fn int(value: i64, monotype: MonotypeId) -> Expression {
    Expression::new(ExpressionKind::Literal(Literal::Int(value)), monotype)
}

fn unit_value(monotype: MonotypeId) -> Expression {
    Expression::new(ExpressionKind::Unit, monotype)
}

/// Whether a let binds a small array literal of values that cost nothing to copy, constants and
/// lambdas, which its body hands to operations that work such a literal out and uses at most as
/// often otherwise, inside a lambda only when every use works it out: `noted`, folded twice for
/// the largest number and for the table of wire types, is copied to both folds.
pub(super) fn is_consumed_literal_array(
    binding: &Binding,
    body: &Expression,
    sizes: &[usize],
) -> bool {
    let ExpressionKind::Array(elements) = &binding.value.kind else { return false };
    let copyable = elements.len() <= LITERAL_ELEMENTS
        && (is_constant(&binding.value)
            || elements.iter().all(is_discardable)
                && is_within_size(&binding.value, COPIED_ARRAY_SIZE));
    if !copyable {
        return false;
    }
    let local = binding.local.id;
    let mut consumed = 0;
    visit(body, &mut |node| {
        let operands: &[Expression] = match &node.kind {
            ExpressionKind::Foreign { foreign, arguments }
                if works_out_literals(foreign, arguments, elements.len(), sizes) =>
            {
                arguments
            }
            ExpressionKind::EffectEach { array, .. } => std::slice::from_ref(array),
            _ => &[],
        };
        consumed += operands
            .iter()
            .filter(|operand| matches!(operand.kind, ExpressionKind::Local(id) if id == local))
            .count();
    });
    let uses = occurrences_up_to(body, local, 2 * consumed + 1);
    let all_consumed = uses.total == consumed;
    consumed > 0 && uses.total <= 2 * consumed && (all_consumed || uses.under_lambda == 0)
}

/// Whether an operation works out an array literal it is given, its callbacks being known.
fn works_out_literals(
    foreign: &Foreign,
    arguments: &[Expression],
    count: usize,
    sizes: &[usize],
) -> bool {
    let iterates = matches!(foreign, Foreign::Call { boundary, .. } if matches!(
        boundary.iteration,
        Some(Iteration::FoldLeft | Iteration::FoldRight | Iteration::Map | Iteration::MapWithIndex)
    ));
    let sorts = foreign.calls(ARRAY_SORT_BY) && arguments.iter().take(2).all(is_known_step);
    let copies = arguments.first().is_some_and(|callback| copies_fit(callback, count, sizes));
    sorts
        || iterates && copies
        || foreign.calls(ARRAY_APPEND)
        || foreign.calls(ARRAY_REVERSE)
        || matches!(
            foreign,
            Foreign::UpdateAt
                | Foreign::ArrayUpdated
                | Foreign::MaybeIndex
                | Foreign::Operator(Operator::ArrayIndex | Operator::ArrayLength)
        )
}

impl Simplifier<'_> {
    /// The arguments a lambda or function is applied to that are array literals of constants
    /// its body works out, written into the body before it is simplified: `foldl step table`
    /// steps with `table` known, so that each step's update of it is worked out too.
    pub(super) fn substituted_constant_arrays(
        &mut self,
        bindings: Vec<Binding>,
        mut body: Expression,
    ) -> (Vec<Binding>, Expression) {
        if self.fuel == 0 {
            return (bindings, body);
        }
        let mut kept = Vec::with_capacity(bindings.len());
        for binding in bindings {
            if is_consumed_literal_array(&binding, &body, &self.sizes) {
                body = substitute(body, binding.local.id, &binding.value, self.monotypes);
            } else {
                kept.push(binding);
            }
        }
        (kept, body)
    }
}

impl Simplifier<'_> {
    /// A field of what a call with constant arguments returns, when the callee builds a record
    /// whose field is a constant there: `(fieldCodec (Proxy :: Proxy (Array Cell)) 3).noted` is
    /// `[]`, without building the codec.
    pub(super) fn field_of_call(
        &mut self,
        record: Expression,
        label: &str,
        monotype: MonotypeId,
    ) -> Result<Expression, Expression> {
        let ExpressionKind::Apply { function, arguments } = &record.kind else {
            return Err(record);
        };
        let ExpressionKind::Function(id) = function.kind else { return Err(record) };
        if self.fuel == 0 || id == self.entry || self.recursive[id.0 as usize] {
            return Err(record);
        }
        let Some(callee) = self.functions[id.0 as usize].as_ref() else { return Err(record) };
        if callee.parameters.len() != arguments.len() || !arguments.iter().all(is_constant) {
            return Err(record);
        }
        let key = (id, arguments.clone(), Some(SmolStr::from(label)));
        if let Some(known) = self.evaluated_constants.get(&key) {
            return known.clone().ok_or(record);
        }
        self.evaluated_constants.insert(key.clone(), None);
        let Some(field) = built_field(&callee.body, label) else { return Err(record) };
        let mut renaming = FxHashMap::default();
        let parameters: Vec<Local> = callee
            .parameters
            .clone()
            .iter()
            .map(|parameter| self.rename_binder(parameter, &mut renaming))
            .collect();
        let mut field = field;
        self.rename(&mut field, &mut renaming);
        let fuel = self.fuel;
        self.fuel -= 1;
        let arguments = arguments.clone();
        let evaluated = self.beta(parameters, field, arguments, monotype);
        if is_constant(&evaluated) && is_within_size(&evaluated, CONSTANT_RESULT_SIZE) {
            self.evaluated_constants.insert(key, Some(evaluated.clone()));
            return Ok(evaluated);
        }
        self.fuel = fuel;
        Err(record)
    }
}

/// The field of the record a function's body builds, under the lets it builds it with that the
/// field needs.
fn built_field(body: &Expression, label: &str) -> Option<Expression> {
    match &body.kind {
        ExpressionKind::Let { bindings, body: inner } => {
            let field = built_field(inner, label)?;
            let needed = needed_bindings(bindings, &field);
            if needed.is_empty() {
                return Some(field);
            }
            let monotype = field.monotype;
            let kind = ExpressionKind::Let { bindings: needed, body: Box::new(field) };
            Some(Expression::new(kind, monotype))
        }
        ExpressionKind::Record(fields) => {
            fields.iter().find(|(field, _)| field == label).map(|(_, value)| value.clone())
        }
        _ => None,
    }
}

/// The bindings an expression mentions, and the ones those mention, in their order.
fn needed_bindings(bindings: &[Binding], expression: &Expression) -> Vec<Binding> {
    let mentions = |expression: &Expression, binding: &Binding| {
        occurrences_up_to(expression, binding.local.id, 1).total > 0
    };
    let mut needed: Vec<bool> =
        bindings.iter().map(|binding| mentions(expression, binding)).collect();
    let mut changed = true;
    while changed {
        changed = false;
        for (index, binding) in bindings.iter().enumerate() {
            if !needed[index] {
                continue;
            }
            for (other, candidate) in bindings.iter().enumerate() {
                if !needed[other] && mentions(&binding.value, candidate) {
                    needed[other] = true;
                    changed = true;
                }
            }
        }
    }
    bindings
        .iter()
        .zip(needed)
        .filter(|(_, needed)| *needed)
        .map(|(binding, _)| binding.clone())
        .collect()
}

impl Simplifier<'_> {
    /// The body with each call of a let-bound lambda whose arguments are constants evaluated
    /// where it is a constant: a join point that turns an enumeration's generic representation
    /// into its index, `join (Inr (Inl NoArguments))`, is `1`.
    pub(super) fn evaluated_local_calls(
        &mut self,
        binding: &Binding,
        mut body: Expression,
    ) -> Expression {
        let ExpressionKind::Lambda { parameters, body: lambda_body } = &binding.value.kind else {
            return body;
        };
        if self.fuel == 0 || !is_within_size(lambda_body, EVALUATED_CONSTANT_SIZE) {
            return body;
        }
        let arity = parameters.len();
        self.evaluate_calls_of(binding, arity, &mut body);
        body
    }

    fn evaluate_calls_of(&mut self, binding: &Binding, arity: usize, expression: &mut Expression) {
        if let ExpressionKind::Apply { function, arguments } = &expression.kind
            && matches!(function.kind, ExpressionKind::Local(local) if local == binding.local.id)
            && arguments.len() == arity
            && arguments.iter().all(is_constant)
            && arguments.iter().any(holds_fields)
            && self.fuel > 0
        {
            let fuel = self.fuel;
            self.fuel -= 1;
            let lambda = self.renamed(&binding.value);
            let evaluated = self.apply(lambda, arguments.clone(), expression.monotype);
            if is_constant(&evaluated) && is_within_size(&evaluated, CONSTANT_RESULT_SIZE) {
                *expression = evaluated;
            } else {
                self.fuel = fuel;
            }
            return;
        }
        for_each_child_mut(expression, &mut |child| self.evaluate_calls_of(binding, arity, child));
    }
}
