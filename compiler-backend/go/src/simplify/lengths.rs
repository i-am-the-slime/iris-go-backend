use super::Simplifier;
use super::choice::operation;
use crate::foreign::{Boundary, Foreign, Iteration, Operator};
use crate::monomorphic::traversal::{for_each_child, for_each_child_mut};
use crate::monomorphic::{Binding, Expression, ExpressionKind, LocalId};
use crate::purity::is_within_size;

/// A range bound repeated for a length is at most this many nodes.
const REPEATED_BOUND_SIZE: usize = 8;

#[derive(Default)]
struct Reads {
    lengths: usize,
    others: usize,
}

impl Simplifier<'_> {
    /// The body with each `length xs` of a binding `xs = map f source` counting `source`
    /// instead, when what is left reads `xs` at most once: a `map` keeps the length of what it
    /// maps, and the one read that is left can then take the `map` into its own loop instead of
    /// an array built to be read twice.
    pub(super) fn count_lengths_at_source(
        &self,
        binding: &Binding,
        body: Expression,
    ) -> Expression {
        let Some(source) = mapped_source(&binding.value) else { return body };
        let mut reads = Reads::default();
        count_reads(&body, binding.local.id, &mut reads);
        if reads.lengths == 0 || reads.others > 1 {
            return body;
        }
        let mut body = body;
        count_at_source(&mut body, binding.local.id, source);
        body
    }
}

/// What a chain of `map`s maps over, when counting it again costs no more than its bounds.
fn mapped_source(value: &Expression) -> Option<&Expression> {
    let mut current = value;
    let mut mapped = false;
    while let ExpressionKind::Foreign {
        foreign:
            Foreign::Call {
                boundary: Boundary { iteration: Some(Iteration::Map | Iteration::MapWithIndex), .. },
                ..
            },
        arguments,
    } = &current.kind
    {
        let [_, inner] = arguments.as_slice() else { return None };
        current = inner;
        mapped = true;
    }
    let counted_cheaply = match &current.kind {
        ExpressionKind::Local(_) => true,
        ExpressionKind::Foreign { foreign: Foreign::Range, arguments } => arguments
            .iter()
            .all(|bound| is_within_size(bound, REPEATED_BOUND_SIZE) && is_arithmetic(bound)),
        _ => false,
    };
    (mapped && counted_cheaply).then_some(current)
}

fn is_arithmetic(expression: &Expression) -> bool {
    match &expression.kind {
        ExpressionKind::Local(_) | ExpressionKind::Literal(_) => true,
        ExpressionKind::Foreign { foreign: Foreign::Operator(_), arguments } => {
            arguments.iter().all(is_arithmetic)
        }
        _ => false,
    }
}

fn is_length_of(expression: &Expression, local: LocalId) -> bool {
    matches!(
        &expression.kind,
        ExpressionKind::Foreign { foreign: Foreign::Operator(Operator::ArrayLength), arguments }
            if matches!(arguments.as_slice(), [array] if matches!(array.kind, ExpressionKind::Local(id) if id == local))
    )
}

fn count_reads(expression: &Expression, local: LocalId, reads: &mut Reads) {
    if is_length_of(expression, local) {
        reads.lengths += 1;
        return;
    }
    if matches!(expression.kind, ExpressionKind::Local(id) if id == local) {
        reads.others += 1;
        return;
    }
    for_each_child(expression, &mut |child| count_reads(child, local, reads));
}

fn count_at_source(expression: &mut Expression, local: LocalId, source: &Expression) {
    if is_length_of(expression, local) {
        *expression = operation(Operator::ArrayLength, vec![source.clone()], expression.monotype);
        return;
    }
    for_each_child_mut(expression, &mut |child| count_at_source(child, local, source));
}
