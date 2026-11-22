use rustc_hash::FxHashMap;

use super::Simplifier;
use crate::monomorphic::traversal::for_each_child_mut;
use crate::monomorphic::{Expression, ExpressionKind, Guard, Guarded, Local, LocalId, Pattern};

impl Simplifier<'_> {
    pub(super) fn rename_binder(
        &mut self,
        local: &Local,
        renaming: &mut FxHashMap<LocalId, LocalId>,
    ) -> Local {
        let fresh = self.fresh(local);
        renaming.insert(local.id, fresh.id);
        if self.thunk_parameters.contains(&local.id) {
            self.thunk_parameters.insert(fresh.id);
        }
        fresh
    }

    pub(super) fn rename(
        &mut self,
        expression: &mut Expression,
        renaming: &mut FxHashMap<LocalId, LocalId>,
    ) {
        match &mut expression.kind {
            ExpressionKind::Local(id) => *id = renaming.get(id).copied().unwrap_or(*id),
            ExpressionKind::Lambda { parameters, body } => {
                self.rename_binders(parameters, renaming);
                self.rename(body, renaming);
            }
            ExpressionKind::Let { bindings, body } => {
                for binding in bindings.iter_mut() {
                    binding.local = self.rename_binder(&binding.local, renaming);
                }
                for binding in bindings {
                    self.rename(&mut binding.value, renaming);
                }
                self.rename(body, renaming);
            }
            ExpressionKind::EffectBind { action, local, body } => {
                self.rename(action, renaming);
                *local = self.rename_binder(local, renaming);
                self.rename(body, renaming);
            }
            ExpressionKind::EffectEach { array, element, body } => {
                self.rename(array, renaming);
                *element = self.rename_binder(element, renaming);
                self.rename(body, renaming);
            }
            ExpressionKind::Case { scrutinees, alternatives } => {
                for scrutinee in scrutinees {
                    self.rename(scrutinee, renaming);
                }
                for alternative in alternatives {
                    for pattern in &mut alternative.patterns {
                        self.rename_pattern(pattern, renaming);
                    }
                    self.rename_guarded(&mut alternative.body, renaming);
                }
            }
            _ => for_each_child_mut(expression, &mut |child| self.rename(child, renaming)),
        }
    }

    fn rename_guarded(
        &mut self,
        guarded: &mut Guarded,
        renaming: &mut FxHashMap<LocalId, LocalId>,
    ) {
        match guarded {
            Guarded::Unconditional(body) => self.rename(body, renaming),
            Guarded::Guards(branches) => {
                for branch in branches {
                    for guard in &mut branch.guards {
                        match guard {
                            Guard::Boolean(condition) => self.rename(condition, renaming),
                            Guard::Pattern { pattern, value } => {
                                self.rename(value, renaming);
                                self.rename_pattern(pattern, renaming);
                            }
                        }
                    }
                    self.rename(&mut branch.body, renaming);
                }
            }
        }
    }

    fn rename_binders(&mut self, locals: &mut [Local], renaming: &mut FxHashMap<LocalId, LocalId>) {
        for local in locals {
            *local = self.rename_binder(local, renaming);
        }
    }

    fn rename_pattern(
        &mut self,
        pattern: &mut Pattern,
        renaming: &mut FxHashMap<LocalId, LocalId>,
    ) {
        pattern.for_each_local_mut(&mut |local| *local = self.rename_binder(local, renaming));
    }
}
