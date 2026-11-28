//! Folds that only prepend to the array they carry, grown at the end instead.
//!
//! `foldl (flip Array.cons) [] xs` and `foldl (\acc x -> [x] <> acc) [] xs` copy the whole
//! accumulator at every step. Such a step only ever puts elements in front of the accumulator or
//! gives it back unchanged, and reads it nowhere else, so the fold can append the same elements
//! in the opposite order, which an owned accumulator does in place, and reverse the result once
//! where it ends:
//!
//! ```go
//! accumulator := []int{}
//! for _, x := range xs {
//!     accumulator = append(accumulator, x)
//! }
//! slices.Reverse(accumulator)
//! ```
//!
//! A fold that starts from a non-empty array appends that array after the reversed result.

use crate::foreign::{self, Foreign, Iteration};
use crate::monomorphic::traversal::{for_each_child_mut, visit};
use crate::monomorphic::{Expression, ExpressionKind, Guarded, LocalId, Program};
use crate::monotype::{Monotype, Monotypes};

pub(super) fn append_prepending_folds(program: &mut Program, monotypes: &Monotypes) {
    for function in &mut program.functions {
        if has_prepending_fold(&function.body, monotypes) {
            rewrite(&mut function.body, monotypes);
        }
    }
}

fn has_prepending_fold(expression: &Expression, monotypes: &Monotypes) -> bool {
    let mut found = false;
    visit(expression, &mut |node| found |= prepending_step(node, monotypes).is_some());
    found
}

fn rewrite(expression: &mut Expression, monotypes: &Monotypes) {
    for_each_child_mut(expression, &mut |child| rewrite(child, monotypes));
    if let Some(appended) = appending_fold(expression, monotypes) {
        *expression = appended.replacing(expression.position);
    }
}

/// The step of a fold over an array whose results each prepend to the accumulator or give it
/// back, and which reads the accumulator nowhere else.
fn prepending_step(expression: &Expression, monotypes: &Monotypes) -> Option<Results> {
    let (_, [callback, _, _], accumulator_position) = fold_parts(expression)?;
    if !matches!(monotypes.get(expression.monotype), Monotype::Array(_)) {
        return None;
    }
    let ExpressionKind::Lambda { parameters, body } = &callback.kind else { return None };
    let [_, _] = parameters.as_slice() else { return None };
    let accumulator = parameters[accumulator_position].id;
    let mut results = Results { accumulator, prepends: 0, uses: 0 };
    let only_prepends = results.only_prepend(body) && results.prepends > 0;
    (only_prepends && uses(body, accumulator) == results.uses).then_some(results)
}

/// The fold as one that appends to the array it carries and reverses it where it ends.
fn appending_fold(expression: &Expression, monotypes: &Monotypes) -> Option<Expression> {
    let results = prepending_step(expression, monotypes)?;
    let (foreign, [callback, initial, array], _) = fold_parts(expression)?;
    let ExpressionKind::Lambda { parameters, body } = &callback.kind else { return None };
    let callback_monotype = callback.monotype;
    let mut body = (**body).clone();
    results.append_instead(&mut body);
    let callback = ExpressionKind::Lambda { parameters: parameters.clone(), body: Box::new(body) };
    let callback = Expression::new(callback, callback_monotype);
    let empty = Expression::new(ExpressionKind::Array(vec![]), expression.monotype);
    let arguments = vec![callback, empty, array.clone()];
    let appended = ExpressionKind::Foreign { foreign, arguments };
    let appended = Expression::new(appended, expression.monotype);
    let arguments = vec![appended];
    let reverse = ExpressionKind::Foreign { foreign: &Foreign::OwnedReverse, arguments };
    let reversed = Expression::new(reverse, expression.monotype);
    if matches!(&initial.kind, ExpressionKind::Array(elements) if elements.is_empty()) {
        return Some(reversed);
    }
    let arguments = vec![reversed, initial.clone()];
    let append = ExpressionKind::Foreign { foreign: foreign::ARRAY_APPEND.interned(), arguments };
    Some(Expression::new(append, expression.monotype))
}

/// A fold's foreign, its callback, initial value and array, and where its callback takes the
/// accumulator.
fn fold_parts(expression: &Expression) -> Option<(&'static Foreign, &[Expression; 3], usize)> {
    let ExpressionKind::Foreign { foreign, arguments } = &expression.kind else { return None };
    let Foreign::Call { boundary, .. } = foreign else { return None };
    let accumulator_position = match boundary.iteration? {
        Iteration::FoldLeft => 0,
        Iteration::FoldRight => 1,
        _ => return None,
    };
    Some((foreign, arguments.as_slice().try_into().ok()?, accumulator_position))
}

fn uses(expression: &Expression, local: LocalId) -> usize {
    let mut count = 0;
    visit(expression, &mut |node| {
        count += usize::from(matches!(node.kind, ExpressionKind::Local(id) if id == local));
    });
    count
}

/// The results of a fold's step, each of which prepends to the accumulator or gives it back.
struct Results {
    accumulator: LocalId,
    prepends: usize,
    /// The accumulator's uses in the results.
    uses: usize,
}

impl Results {
    fn only_prepend(&mut self, expression: &Expression) -> bool {
        match &expression.kind {
            ExpressionKind::Local(id) if *id == self.accumulator => {
                self.uses += 1;
                true
            }
            ExpressionKind::Let { body, .. } => self.only_prepend(body),
            ExpressionKind::If { then, otherwise, .. } => {
                self.only_prepend(then) && self.only_prepend(otherwise)
            }
            ExpressionKind::Case { alternatives, .. } => {
                alternatives.iter().all(|alternative| match &alternative.body {
                    Guarded::Unconditional(body) => self.only_prepend(body),
                    Guarded::Guards(branches) => {
                        branches.iter().all(|branch| self.only_prepend(&branch.body))
                    }
                })
            }
            _ if self.prepended(expression).is_some() => {
                self.prepends += 1;
                self.uses += 1;
                true
            }
            _ => false,
        }
    }

    /// The elements of `[x, …] <> accumulator`.
    fn prepended<'e>(&self, expression: &'e Expression) -> Option<&'e [Expression]> {
        let ExpressionKind::Foreign { foreign, arguments } = &expression.kind else { return None };
        if !foreign.calls(foreign::ARRAY_APPEND) {
            return None;
        }
        let [prefix, rest] = arguments.as_slice() else { return None };
        let ExpressionKind::Array(elements) = &prefix.kind else { return None };
        let accumulator = self.accumulator;
        let is_accumulator = matches!(rest.kind, ExpressionKind::Local(id) if id == accumulator);
        (!elements.is_empty() && is_accumulator).then_some(elements)
    }

    /// Each `[x, y] <> accumulator` of the results as `accumulator <> [y, x]`.
    fn append_instead(&self, expression: &mut Expression) {
        if let Some(elements) = self.prepended(expression) {
            let elements = elements.iter().rev().cloned().collect();
            let ExpressionKind::Foreign { arguments, .. } = &mut expression.kind else {
                unreachable!()
            };
            let suffix = Expression::new(ExpressionKind::Array(elements), arguments[0].monotype)
                .replacing(arguments[0].position);
            let accumulator = arguments[1].clone();
            *arguments = vec![accumulator, suffix];
            return;
        }
        match &mut expression.kind {
            ExpressionKind::Let { body, .. } => self.append_instead(body),
            ExpressionKind::If { then, otherwise, .. } => {
                self.append_instead(then);
                self.append_instead(otherwise);
            }
            ExpressionKind::Case { alternatives, .. } => {
                for alternative in alternatives {
                    match &mut alternative.body {
                        Guarded::Unconditional(body) => self.append_instead(body),
                        Guarded::Guards(branches) => branches
                            .iter_mut()
                            .for_each(|branch| self.append_instead(&mut branch.body)),
                    }
                }
            }
            _ => {}
        }
    }
}
