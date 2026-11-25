//! Arrays that are only measured and read at positions. An array a pipeline of known
//! combinators builds, `take n (map f (range a b))`, needs no storage when nothing but its
//! length and its elements at given positions are asked for: the length follows from the
//! combinators, and the element at `i` is `f (a + i)`.

use rustc_hash::FxHashMap;

use super::Simplifier;
use super::choice::operation;
use crate::foreign::{ARRAY_SLICE, Comparison, Foreign, Iteration, Operator};
use crate::monomorphic::traversal::{for_each_child, for_each_child_mut};
use crate::monomorphic::{Binding, Expression, ExpressionKind, Literal, Local, LocalId};
use crate::monotype::{Monotype, MonotypeId};
use crate::purity::is_within_size;

const VIEWED_CALLBACK_SIZE: usize = 24;
const VIEWED_READS: usize = 2;

/// What an array is built from, as far as its length and elements go.
enum View<'e> {
    Range { first: &'e Expression, last: &'e Expression },
    Map { callback: &'e Expression, inner: Box<View<'e>> },
    Prefix { end: &'e Expression, inner: Box<View<'e>> },
    EmptyWhen { condition: &'e Expression, inner: Box<View<'e>> },
    Stored(&'e Expression),
}

impl<'e> View<'e> {
    fn of(expression: &'e Expression) -> View<'e> {
        match &expression.kind {
            ExpressionKind::Foreign { foreign: Foreign::Range, arguments } => {
                View::Range { first: &arguments[0], last: &arguments[1] }
            }
            ExpressionKind::Foreign { foreign, arguments } if is_map(foreign) => {
                let [callback, inner] = arguments.as_slice() else {
                    return View::Stored(expression);
                };
                if !is_viewable_callback(callback) {
                    return View::Stored(expression);
                }
                View::Map { callback, inner: Box::new(View::of(inner)) }
            }
            ExpressionKind::Foreign { foreign, arguments } if foreign.calls(ARRAY_SLICE) => {
                let [start, end, inner] = arguments.as_slice() else {
                    return View::Stored(expression);
                };
                if !matches!(start.kind, ExpressionKind::Literal(Literal::Int(0))) {
                    return View::Stored(expression);
                }
                View::Prefix { end, inner: Box::new(View::of(inner)) }
            }
            ExpressionKind::If { condition, then, otherwise } if matches!(&then.kind, ExpressionKind::Array(elements) if elements.is_empty()) => {
                View::EmptyWhen { condition, inner: Box::new(View::of(otherwise)) }
            }
            _ => View::Stored(expression),
        }
    }

    fn builds(&self) -> bool {
        match self {
            View::Range { .. } | View::Map { .. } => true,
            View::Prefix { inner, .. } | View::EmptyWhen { inner, .. } => inner.builds(),
            View::Stored(_) => false,
        }
    }

    /// Whether the parts that the length and the reads repeat are cheap to repeat.
    fn repeats_cheaply(&self) -> bool {
        match self {
            View::Range { first, last } => is_plain(first) && is_plain(last),
            View::Map { inner, .. } => inner.repeats_cheaply(),
            View::Prefix { end, inner } => is_plain(end) && inner.repeats_cheaply(),
            View::EmptyWhen { condition, inner } => is_plain(condition) && inner.repeats_cheaply(),
            View::Stored(array) => matches!(array.kind, ExpressionKind::Local(_)),
        }
    }
}

fn is_map(foreign: &Foreign) -> bool {
    matches!(foreign, Foreign::Call { boundary, .. } if boundary.iteration == Some(Iteration::Map))
}

fn is_viewable_callback(callback: &Expression) -> bool {
    matches!(callback.kind, ExpressionKind::Lambda { .. } | ExpressionKind::Function(_))
        && is_within_size(callback, VIEWED_CALLBACK_SIZE)
}

/// Whether the array a binding builds is only measured and read, and how often it is read.
pub(super) fn viewable(binding: &Binding, body: &Expression) -> bool {
    let view = View::of(&binding.value);
    if !view.builds() || !view.repeats_cheaply() {
        return false;
    }
    let mut reads = 0;
    only_measured_and_read(body, binding.local.id, &mut reads) && reads <= VIEWED_READS
}

fn only_measured_and_read(expression: &Expression, local: LocalId, reads: &mut usize) -> bool {
    let is_local = |expression: &Expression| matches!(expression.kind, ExpressionKind::Local(id) if id == local);
    match &expression.kind {
        ExpressionKind::Local(id) => *id != local,
        ExpressionKind::Foreign {
            foreign: Foreign::Operator(Operator::ArrayLength),
            arguments,
        } if is_local(&arguments[0]) => true,
        ExpressionKind::Foreign { foreign: Foreign::Operator(Operator::ArrayIndex), arguments }
            if is_local(&arguments[0]) =>
        {
            *reads += 1;
            !mentions(&arguments[1], local)
        }
        _ => {
            let mut only = true;
            for_each_child(expression, &mut |child| {
                only = only && only_measured_and_read(child, local, reads)
            });
            only
        }
    }
}

impl Simplifier<'_> {
    /// The body with a `viewable` array's length bound once and each read of it computed from
    /// what it is built from.
    pub(super) fn view(&mut self, binding: Binding, body: Expression) -> Expression {
        let integer = self.monotypes.intern(Monotype::Int);
        let Monotype::Array(element) = *self.monotypes.get(binding.local.monotype) else {
            unreachable!("invariant violated: only an array is viewed")
        };
        let view = View::of(&binding.value);
        let length = self.view_length(&view, integer);
        let length = self.expression(length);
        let length_local = self.named_local("length", integer);
        let mut body = body;
        let step = self.named_local("step", integer);
        let mut reads = vec![];
        collect_reads(&body, binding.local.id, &mut reads);
        let values: Vec<Expression> = reads
            .into_iter()
            .map(|index| self.view_read(&view, index, element, integer, &step))
            .collect();
        let mut values = values.into_iter();
        replace_uses(&mut body, binding.local.id, &length_local.expression(), &mut values);
        let mut bindings = vec![Binding { local: length_local, value: length }];
        if let Some(value) = range_step(&view, integer, self.monotypes) {
            bindings.push(Binding { local: step, value });
        }
        let body = self.expression(body);
        self.let_bindings(bindings, body)
    }

    fn view_length(&mut self, view: &View, integer: MonotypeId) -> Expression {
        let boolean = self.monotypes.intern(Monotype::Boolean);
        let literal =
            |value| Expression::new(ExpressionKind::Literal(Literal::Int(value)), integer);
        let compare = |comparison, left: Expression, right: Expression| {
            operation(Operator::Compare(comparison), vec![left, right], boolean)
        };
        let choose = |condition: Expression, then: Expression, otherwise: Expression| {
            let kind = ExpressionKind::If {
                condition: Box::new(condition),
                then: Box::new(then),
                otherwise: Box::new(otherwise),
            };
            Expression::new(kind, integer)
        };
        match view {
            View::Range { first, last } => {
                let rising = operation(
                    Operator::IntSubtract,
                    vec![(*last).clone(), (*first).clone()],
                    integer,
                );
                let falling = operation(
                    Operator::IntSubtract,
                    vec![(*first).clone(), (*last).clone()],
                    integer,
                );
                let rising = operation(Operator::IntAdd, vec![rising, literal(1)], integer);
                let falling = operation(Operator::IntAdd, vec![falling, literal(1)], integer);
                choose(
                    compare(Comparison::LessThanOrEqual, (*first).clone(), (*last).clone()),
                    rising,
                    falling,
                )
            }
            View::Map { inner, .. } => self.view_length(inner, integer),
            View::Prefix { end, inner } => {
                let whole = self.view_length(inner, integer);
                let whole_local = self.named_local("whole", integer);
                let from_end = operation(
                    Operator::IntAdd,
                    vec![whole_local.expression(), (*end).clone()],
                    integer,
                );
                let from_end = choose(
                    compare(Comparison::LessThan, from_end.clone(), literal(0)),
                    literal(0),
                    from_end,
                );
                let within = choose(
                    compare(Comparison::LessThan, (*end).clone(), whole_local.expression()),
                    (*end).clone(),
                    whole_local.expression(),
                );
                let chosen = choose(
                    compare(Comparison::LessThan, (*end).clone(), literal(0)),
                    from_end,
                    within,
                );
                let kind = ExpressionKind::Let {
                    bindings: vec![Binding { local: whole_local, value: whole }],
                    body: Box::new(chosen),
                };
                Expression::new(kind, integer)
            }
            View::EmptyWhen { condition, inner } => {
                let inner = self.view_length(inner, integer);
                choose((*condition).clone(), literal(0), inner)
            }
            View::Stored(array) => {
                operation(Operator::ArrayLength, vec![(*array).clone()], integer)
            }
        }
    }

    /// The element at `index`, which a read only asks for within the array's length.
    fn view_read(
        &mut self,
        view: &View,
        index: Expression,
        element: MonotypeId,
        integer: MonotypeId,
        step: &Local,
    ) -> Expression {
        match view {
            View::Range { first, .. } => {
                let offset =
                    operation(Operator::IntMultiply, vec![index, step.expression()], integer);
                operation(Operator::IntAdd, vec![(*first).clone(), offset], integer)
            }
            View::Map { callback, inner } => {
                let argument = self
                    .monotypes
                    .function_parts(callback.monotype)
                    .map(|(argument, _)| argument)
                    .expect("invariant violated: a map's callback is a function");
                let read = self.view_read(inner, index, argument, integer, step);
                let mut callback = (*callback).clone();
                self.rename(&mut callback, &mut FxHashMap::default());
                let kind =
                    ExpressionKind::Apply { function: Box::new(callback), arguments: vec![read] };
                Expression::new(kind, element)
            }
            View::Prefix { inner, .. } | View::EmptyWhen { inner, .. } => {
                self.view_read(inner, index, element, integer, step)
            }
            View::Stored(array) => {
                operation(Operator::ArrayIndex, vec![(*array).clone(), index], element)
            }
        }
    }
}

fn collect_reads(expression: &Expression, local: LocalId, reads: &mut Vec<Expression>) {
    if let ExpressionKind::Foreign { foreign: Foreign::Operator(Operator::ArrayIndex), arguments } =
        &expression.kind
        && matches!(arguments[0].kind, ExpressionKind::Local(id) if id == local)
    {
        reads.push(arguments[1].clone());
        return;
    }
    for_each_child(expression, &mut |child| collect_reads(child, local, reads));
}

fn replace_uses(
    expression: &mut Expression,
    local: LocalId,
    length: &Expression,
    reads: &mut impl Iterator<Item = Expression>,
) {
    let is_local = |expression: &Expression| matches!(expression.kind, ExpressionKind::Local(id) if id == local);
    match &expression.kind {
        ExpressionKind::Foreign {
            foreign: Foreign::Operator(Operator::ArrayLength),
            arguments,
        } if is_local(&arguments[0]) => {
            *expression = length.clone().replacing(expression.position);
            return;
        }
        ExpressionKind::Foreign { foreign: Foreign::Operator(Operator::ArrayIndex), arguments }
            if is_local(&arguments[0]) =>
        {
            let read = reads.next().expect("invariant violated: every read was collected");
            *expression = read.replacing(expression.position);
            return;
        }
        _ => {}
    }
    for_each_child_mut(expression, &mut |child| replace_uses(child, local, length, reads));
}

fn is_plain(expression: &Expression) -> bool {
    match &expression.kind {
        ExpressionKind::Local(_) | ExpressionKind::Literal(_) => true,
        ExpressionKind::Foreign { foreign: Foreign::Operator(_), arguments } => {
            arguments.len() <= 2 && arguments.iter().all(is_plain)
        }
        _ => false,
    }
}

fn mentions(expression: &Expression, local: LocalId) -> bool {
    let mut mentioned = false;
    crate::monomorphic::traversal::visit(expression, &mut |node| {
        mentioned |= matches!(node.kind, ExpressionKind::Local(id) if id == local);
    });
    mentioned
}

/// Whether the array is built by combinators a view can stand in for.
pub(super) fn builds_view(expression: &Expression) -> bool {
    let view = View::of(expression);
    view.builds() && view.repeats_cheaply()
}

/// One step from an element of the view's range to the next: the range counts down when it
/// starts above where it ends.
fn range_step(
    view: &View,
    integer: MonotypeId,
    monotypes: &mut crate::monotype::Monotypes,
) -> Option<Expression> {
    match view {
        View::Range { first, last } => {
            let boolean = monotypes.intern(Monotype::Boolean);
            let literal =
                |value| Expression::new(ExpressionKind::Literal(Literal::Int(value)), integer);
            let condition = operation(
                Operator::Compare(Comparison::LessThanOrEqual),
                vec![(*first).clone(), (*last).clone()],
                boolean,
            );
            let kind = ExpressionKind::If {
                condition: Box::new(condition),
                then: Box::new(literal(1)),
                otherwise: Box::new(literal(-1)),
            };
            Some(Expression::new(kind, integer))
        }
        View::Map { inner, .. } | View::Prefix { inner, .. } | View::EmptyWhen { inner, .. } => {
            range_step(inner, integer, monotypes)
        }
        View::Stored(_) => None,
    }
}
