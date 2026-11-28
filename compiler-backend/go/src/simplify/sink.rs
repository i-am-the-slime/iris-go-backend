//! Pure lets moved into the branches that use them. `let error = Left (…)` that a following `if`
//! or `case` returns on its failure paths only is built on those paths: each branch that uses the
//! binding gets its own copy, placed as deep as the paths that do not use it allow, and a path
//! that never uses it builds nothing.
//!
//! Only a value that may be evaluated later or not at all moves ([`is_deferrable`], running no
//! effect and calling no function that might), and it moves across nothing that runs an effect
//! (an effect's sequence, a binding or a condition that runs one), so no effect is reordered.

use rustc_hash::FxHashMap;

use super::Simplifier;
use crate::monomorphic::traversal::{for_each_child_mut, mentions_local, rename_local};
use crate::monomorphic::{Binding, Expression, ExpressionKind, Guarded, LocalId};
use crate::purity::{KnownFunctions, is_deferrable, is_within_size, runs_effect};

/// A value copied into more than one branch is at most this many nodes.
const COPIED_SIZE: usize = 40;

impl Simplifier<'_> {
    /// Every pure let of the expression moved into the branches that use it.
    pub(super) fn sink_lets(&mut self, expression: &mut Expression) {
        if let ExpressionKind::Let { bindings, body } = &mut expression.kind
            && !is_recursive_group(bindings)
            && bindings.iter().all(|binding| !runs_effect(self, &binding.value))
        {
            let mut kept = vec![];
            for binding in std::mem::take(bindings).into_iter().rev() {
                match self.sinkable(&binding, body) {
                    true => self.sink(binding, body),
                    false => kept.push(binding),
                }
            }
            kept.reverse();
            *bindings = kept;
            if bindings.is_empty() {
                let monotype = expression.monotype;
                let kind = std::mem::replace(&mut expression.kind, ExpressionKind::Unit);
                let ExpressionKind::Let { body, .. } = kind else {
                    unreachable!("invariant violated: the expression was just matched as a let")
                };
                *expression = *body;
                debug_assert_eq!(expression.monotype, monotype);
                return self.sink_lets(expression);
            }
        }
        for_each_child_mut(expression, &mut |child| self.sink_lets(child));
    }

    /// Whether the binding is pure, used by the body on some paths only, and small enough for the
    /// copies it would take.
    fn sinkable(&self, binding: &Binding, body: &Expression) -> bool {
        let id = binding.local.id;
        mentions_local(body, id)
            && !needed_on_every_path(self, body, id)
            && is_deferrable(&binding.value)
            && calls_only_deferrable_functions(self, &binding.value, 4)
            && (places(self, body, id) == 1 || is_within_size(&binding.value, COPIED_SIZE))
    }

    /// The body with the binding placed at each point that leads only to its uses, or its value
    /// where that point is the use itself. The first copy keeps the binding's local; every other
    /// copy binds fresh locals.
    fn sink(&mut self, binding: Binding, body: &mut Expression) {
        let mut copies = 0;
        self.place(&binding, body, &mut copies);
    }

    fn place(&mut self, binding: &Binding, expression: &mut Expression, copies: &mut usize) {
        let id = binding.local.id;
        if !mentions_local(expression, id) {
            return;
        }
        if needed_on_every_path(self, expression, id) {
            let copy = self.copy(binding, expression, *copies);
            *copies += 1;
            if matches!(expression.kind, ExpressionKind::Local(local) if local == copy.local.id) {
                super::substitute_in_place(expression, copy.local.id, &copy.value, self.monotypes);
                return;
            }
            let monotype = expression.monotype;
            let placeholder = Expression::new(ExpressionKind::Unit, monotype);
            let inner = std::mem::replace(expression, placeholder);
            *expression = Expression::new(
                ExpressionKind::Let { bindings: vec![copy], body: Box::new(inner) },
                monotype,
            );
            return;
        }
        match &mut expression.kind {
            ExpressionKind::If { then, otherwise, .. } => {
                self.place(binding, then, copies);
                self.place(binding, otherwise, copies);
            }
            ExpressionKind::Case { alternatives, .. } => {
                for alternative in alternatives {
                    match &mut alternative.body {
                        Guarded::Unconditional(body) => self.place(binding, body, copies),
                        Guarded::Guards(branches) => {
                            for branch in branches {
                                self.place(binding, &mut branch.body, copies);
                            }
                        }
                    }
                }
            }
            ExpressionKind::Let { body, .. } => self.place(binding, body, copies),
            _ => unreachable!("invariant violated: only a branching expression leaves a use out"),
        }
    }

    /// The binding for one more place: after the first, its local and the binders of its value
    /// are fresh, and the place refers to the fresh local.
    fn copy(&mut self, binding: &Binding, place: &mut Expression, copies: usize) -> Binding {
        if copies == 0 {
            return binding.clone();
        }
        let mut renaming = FxHashMap::default();
        let mut value = binding.value.clone();
        self.rename(&mut value, &mut renaming);
        let local = self.fresh(&binding.local);
        rename_local(place, binding.local.id, local.id);
        Binding { local, value }
    }
}

/// Whether every way through the expression uses the local, or reaches a point this pass cannot
/// move it past. A lambda that captures it uses it.
fn needed_on_every_path(known: &impl KnownFunctions, expression: &Expression, id: LocalId) -> bool {
    match &expression.kind {
        ExpressionKind::If { condition, then, otherwise } => {
            mentions_local(condition, id)
                || runs_effect(known, condition)
                || (needed_on_every_path(known, then, id)
                    && needed_on_every_path(known, otherwise, id))
        }
        ExpressionKind::Case { scrutinees, alternatives } => {
            scrutinees
                .iter()
                .any(|scrutinee| mentions_local(scrutinee, id) || runs_effect(known, scrutinee))
                || alternatives.iter().any(|alternative| match &alternative.body {
                    Guarded::Unconditional(_) => false,
                    Guarded::Guards(branches) => branches.iter().any(|branch| {
                        branch.guards.iter().any(|guard| {
                            mentions_local(guard.value(), id) || runs_effect(known, guard.value())
                        })
                    }),
                })
                || alternatives.iter().all(|alternative| match &alternative.body {
                    Guarded::Unconditional(body) => needed_on_every_path(known, body, id),
                    Guarded::Guards(branches) => {
                        branches.iter().all(|branch| needed_on_every_path(known, &branch.body, id))
                    }
                })
        }
        ExpressionKind::Let { bindings, body } => {
            is_recursive_group(bindings)
                || bindings.iter().any(|binding| {
                    mentions_local(&binding.value, id) || runs_effect(known, &binding.value)
                })
                || needed_on_every_path(known, body, id)
        }
        _ => mentions_local(expression, id),
    }
}

/// The number of copies placing the local's binding in the expression takes.
fn places(known: &impl KnownFunctions, expression: &Expression, id: LocalId) -> usize {
    if !mentions_local(expression, id) {
        return 0;
    }
    if needed_on_every_path(known, expression, id) {
        return 1;
    }
    match &expression.kind {
        ExpressionKind::If { then, otherwise, .. } => {
            places(known, then, id) + places(known, otherwise, id)
        }
        ExpressionKind::Case { alternatives, .. } => alternatives
            .iter()
            .map(|alternative| match &alternative.body {
                Guarded::Unconditional(body) => places(known, body, id),
                Guarded::Guards(branches) => {
                    branches.iter().map(|branch| places(known, &branch.body, id)).sum()
                }
            })
            .sum(),
        ExpressionKind::Let { body, .. } => places(known, body, id),
        _ => 1,
    }
}

/// Whether every function the value calls may itself be evaluated later or not at all, looked into
/// `depth` calls deep. A call of a local, or of a recursive function, might not return.
fn calls_only_deferrable_functions(
    known: &impl KnownFunctions,
    expression: &Expression,
    depth: usize,
) -> bool {
    let mut deferrable = true;
    crate::monomorphic::traversal::visit(expression, &mut |node| {
        if let ExpressionKind::Apply { function, .. } = &node.kind {
            deferrable &= match &function.kind {
                ExpressionKind::Lambda { .. } => true,
                ExpressionKind::Function(id) => {
                    depth > 0
                        && !known.is_recursive(*id)
                        && known.known(*id).is_some_and(|callee| {
                            is_deferrable(&callee.body)
                                && calls_only_deferrable_functions(known, &callee.body, depth - 1)
                        })
                }
                _ => false,
            };
        }
    });
    deferrable
}

/// A let group whose bindings refer to each other, which the simplifier keeps as written.
fn is_recursive_group(bindings: &[Binding]) -> bool {
    bindings.iter().any(|binding| crate::purity::mentions_any(&binding.value, bindings))
}
