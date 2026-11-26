//! Whether a local is the only reference to its cells wherever a body uses it.

use rustc_hash::{FxHashMap, FxHashSet};

use super::paths::{Event, Paths};
use crate::emit::uses_local;
use crate::monomorphic::traversal::{for_each_child, for_each_guarded_child};
use crate::monomorphic::{Expression, ExpressionKind, Guarded, LocalId, Pattern, PatternKind};
use crate::monotype::MonotypeId;

/// What the framework asks of the program's data layout and of the functions a body calls.
pub(in crate::emit) trait Shapes {
    /// Whether `call` only reads `argument`, a local holding cells, and keeps none of them.
    fn inspects(&mut self, call: &Expression, argument: &Expression) -> bool;
    /// Whether a field of type `field` of a cell of type `cell` is part of its spine: a cell of
    /// the same data that the outer cell's owner owns too.
    fn is_spine(&mut self, cell: MonotypeId, field: MonotypeId) -> bool;
}

/// One branch of an `if` (`Then`, `Otherwise`) or of a `case` (the alternative, and the guarded
/// branch within it when it has guards).
#[derive(Clone, Copy, PartialEq, Eq)]
pub(in crate::emit) enum Branch {
    Then,
    Otherwise,
    Alternative(usize, Option<usize>),
}

/// The branches each conditional is known to take, by its address; a conditional missing from it
/// may take any branch.
pub(in crate::emit) type Forced = FxHashMap<*const Expression, Vec<Branch>>;

/// The code a local is used in: an expression or the body of an alternative.
#[derive(Clone, Copy)]
pub(in crate::emit) enum Scope<'e> {
    Expression(&'e Expression),
    Guarded(&'e Guarded),
}

impl<'e> Scope<'e> {
    pub(in crate::emit) fn expressions(self) -> Vec<&'e Expression> {
        match self {
            Scope::Expression(expression) => vec![expression],
            Scope::Guarded(guarded) => guarded_expressions(guarded),
        }
    }
}

/// Whether `target` is unique in `scope`: on every path the scope can take, it is consumed at
/// most once, its relatives (`ancestors`, and the locals that patterns on it bind to its spine)
/// are not used next to that consumption, and it is not read after it.
pub(in crate::emit) fn is_unique(
    shapes: &mut impl Shapes,
    target: LocalId,
    ancestors: &[LocalId],
    scope: Scope<'_>,
    forced: &Forced,
) -> bool {
    let relatives = relatives(shapes, target, ancestors, scope);
    let counter = Counter { target, relatives: &relatives, forced };
    let paths = match scope {
        Scope::Expression(expression) => counter.count(shapes, expression),
        Scope::Guarded(guarded) => counter.guarded(shapes, guarded),
    };
    paths.all_linear()
}

/// The locals that share cells with `target` in `scope`: its ancestors, and the locals that
/// patterns on it, or on those locals, bind to its spine.
pub(in crate::emit) fn relatives(
    shapes: &mut impl Shapes,
    target: LocalId,
    ancestors: &[LocalId],
    scope: Scope<'_>,
) -> FxHashSet<LocalId> {
    let mut family = FxHashSet::default();
    family.insert(target);
    for expression in scope.expressions() {
        descendants(shapes, expression, &mut family);
    }
    family.remove(&target);
    family.extend(ancestors.iter().copied());
    family
}

fn descendants(shapes: &mut impl Shapes, expression: &Expression, family: &mut FxHashSet<LocalId>) {
    if let ExpressionKind::Case { scrutinees, alternatives } = &expression.kind {
        for (position, scrutinee) in scrutinees.iter().enumerate() {
            let ExpressionKind::Local(id) = scrutinee.kind else { continue };
            if !family.contains(&id) {
                continue;
            }
            for alternative in alternatives {
                spine_locals(shapes, &alternative.patterns[position], family);
            }
        }
    }
    for_each_child(expression, &mut |child| descendants(shapes, child, family));
}

fn spine_locals(shapes: &mut impl Shapes, pattern: &Pattern, family: &mut FxHashSet<LocalId>) {
    match &pattern.kind {
        PatternKind::Variable(local) => {
            family.insert(local.id);
        }
        PatternKind::Named { local, pattern } => {
            family.insert(local.id);
            spine_locals(shapes, pattern, family);
        }
        PatternKind::Constructor { arguments, .. } => {
            for argument in arguments {
                if shapes.is_spine(pattern.monotype, argument.monotype) {
                    spine_locals(shapes, argument, family);
                }
            }
        }
        PatternKind::Wildcard
        | PatternKind::Literal(_)
        | PatternKind::Array(_)
        | PatternKind::Record(_)
        | PatternKind::Closure { .. } => {}
    }
}

pub(in crate::emit) fn guarded_expressions(guarded: &Guarded) -> Vec<&Expression> {
    let mut expressions = vec![];
    for_each_guarded_child(guarded, &mut |expression| expressions.push(expression));
    expressions
}

struct Counter<'f> {
    target: LocalId,
    relatives: &'f FxHashSet<LocalId>,
    forced: &'f Forced,
}

impl Counter<'_> {
    fn count(&self, shapes: &mut impl Shapes, expression: &Expression) -> Paths {
        match &expression.kind {
            ExpressionKind::Local(id) if *id == self.target => Paths::event(Event::Consume),
            ExpressionKind::Local(id) if self.relatives.contains(id) => {
                Paths::event(Event::Conflict)
            }
            ExpressionKind::Lambda { .. }
            | ExpressionKind::Closure { .. }
            | ExpressionKind::EffectPure(_)
            | ExpressionKind::EffectBind { .. }
            | ExpressionKind::EffectEach { .. } => {
                if uses_local(expression, self.target) {
                    Paths::event(Event::Shared)
                } else if self.relatives.iter().any(|&conflict| uses_local(expression, conflict)) {
                    Paths::event(Event::Conflict)
                } else {
                    Paths::empty()
                }
            }
            ExpressionKind::Let { bindings, body } => {
                let mut paths = Paths::empty();
                for binding in bindings {
                    paths = paths.then(self.count(shapes, &binding.value));
                }
                paths.then(self.count(shapes, body))
            }
            ExpressionKind::If { condition, then, otherwise } => {
                let allowed = self.forced.get(&std::ptr::from_ref(expression));
                let taken =
                    |branch: Branch| allowed.is_none_or(|allowed| allowed.contains(&branch));
                let mut branches = Paths::nothing();
                if taken(Branch::Then) {
                    branches = branches.or(self.count(shapes, then));
                }
                if taken(Branch::Otherwise) {
                    branches = branches.or(self.count(shapes, otherwise));
                }
                self.count(shapes, condition).then(branches)
            }
            ExpressionKind::Case { scrutinees, alternatives } => {
                let mut paths = Paths::empty();
                for (position, scrutinee) in scrutinees.iter().enumerate() {
                    let inspected = alternatives.iter().any(|alternative| {
                        !matches!(alternative.patterns[position].kind, PatternKind::Wildcard)
                    });
                    let scrutinised = match scrutinee.kind {
                        ExpressionKind::Local(id) if id == self.target => {
                            if inspected {
                                Paths::event(Event::Peek)
                            } else {
                                Paths::empty()
                            }
                        }
                        _ => self.count(shapes, scrutinee),
                    };
                    paths = paths.then(scrutinised);
                }
                let allowed = self.forced.get(&std::ptr::from_ref(expression));
                let taken = |index: usize, branch: Option<usize>| {
                    allowed.is_none_or(|allowed| {
                        allowed.iter().any(|allowed| match *allowed {
                            Branch::Alternative(alternative, allowed_branch) => {
                                alternative == index
                                    && (allowed_branch.is_none()
                                        || branch.is_none()
                                        || allowed_branch == branch)
                            }
                            Branch::Then | Branch::Otherwise => false,
                        })
                    })
                };
                let mut guards = Paths::empty();
                let mut bodies = Paths::nothing();
                for (index, alternative) in alternatives.iter().enumerate() {
                    match &alternative.body {
                        Guarded::Unconditional(body) => {
                            if taken(index, None) {
                                bodies = bodies.or(self.count(shapes, body));
                            }
                        }
                        Guarded::Guards(branches) => {
                            for (position, branch) in branches.iter().enumerate() {
                                for guard in &branch.guards {
                                    let value = guard.value();
                                    guards = guards.then(self.count(shapes, value));
                                }
                                if taken(index, Some(position)) {
                                    bodies = bodies.or(self.count(shapes, &branch.body));
                                }
                            }
                        }
                    }
                }
                let bodies = if alternatives.is_empty() { Paths::empty() } else { bodies };
                paths.then(guards).then(bodies)
            }
            ExpressionKind::Apply { function, arguments } => {
                let paths = self.count(shapes, function);
                self.call(shapes, expression, arguments, paths)
            }
            ExpressionKind::Foreign { arguments, .. } => {
                self.call(shapes, expression, arguments, Paths::empty())
            }
            _ => {
                let mut children = vec![];
                for_each_child(expression, &mut |child| children.push(child));
                let mut paths = Paths::empty();
                for child in children {
                    paths = paths.unordered(self.count(shapes, child));
                }
                paths
            }
        }
    }

    fn call(
        &self,
        shapes: &mut impl Shapes,
        call: &Expression,
        arguments: &[Expression],
        mut paths: Paths,
    ) -> Paths {
        for argument in arguments {
            let inspected = matches!(argument.kind, ExpressionKind::Local(id) if id == self.target)
                && shapes.inspects(call, argument);
            let argument_paths =
                if inspected { Paths::event(Event::Peek) } else { self.count(shapes, argument) };
            paths = paths.unordered(argument_paths);
        }
        paths
    }

    fn guarded(&self, shapes: &mut impl Shapes, guarded: &Guarded) -> Paths {
        match guarded {
            Guarded::Unconditional(body) => self.count(shapes, body),
            Guarded::Guards(branches) => {
                let mut guards = Paths::empty();
                let mut bodies = Paths::nothing();
                for branch in branches {
                    for guard in &branch.guards {
                        let value = guard.value();
                        guards = guards.then(self.count(shapes, value));
                    }
                    bodies = bodies.or(self.count(shapes, &branch.body));
                }
                guards.then(bodies)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use smol_str::SmolStr;

    use super::{Branch, Forced, Scope, Shapes, is_unique};
    use crate::monomorphic::{Binding, Expression, ExpressionKind, FunctionId, Local, LocalId};
    use crate::monotype::MonotypeId;

    const CONSUME: FunctionId = FunctionId(0);
    const INSPECT: FunctionId = FunctionId(1);

    struct Layout;

    impl Shapes for Layout {
        fn inspects(&mut self, call: &Expression, _: &Expression) -> bool {
            let ExpressionKind::Apply { function, .. } = &call.kind else { return false };
            matches!(function.kind, ExpressionKind::Function(INSPECT))
        }

        fn is_spine(&mut self, _: MonotypeId, _: MonotypeId) -> bool {
            true
        }
    }

    fn expression(kind: ExpressionKind) -> Expression {
        Expression::new(kind, MonotypeId::for_tests())
    }

    fn local(id: u32) -> Expression {
        expression(ExpressionKind::Local(LocalId(id)))
    }

    fn call(function: FunctionId, arguments: Vec<Expression>) -> Expression {
        let function = Box::new(expression(ExpressionKind::Function(function)));
        expression(ExpressionKind::Apply { function, arguments })
    }

    fn binding(id: u32, value: Expression, body: Expression) -> Expression {
        let local = Local {
            id: LocalId(id),
            name: SmolStr::new_static("bound"),
            monotype: MonotypeId::for_tests(),
        };
        let bindings = vec![Binding { local, value }];
        expression(ExpressionKind::Let { bindings, body: Box::new(body) })
    }

    fn conditional(then: Expression, otherwise: Expression) -> Expression {
        expression(ExpressionKind::If {
            condition: Box::new(local(9)),
            then: Box::new(then),
            otherwise: Box::new(otherwise),
        })
    }

    fn unique(body: &Expression) -> bool {
        is_unique(&mut Layout, LocalId(1), &[], Scope::Expression(body), &Forced::default())
    }

    #[test]
    fn a_local_passed_on_once_is_unique() {
        assert!(unique(&call(CONSUME, vec![local(1)])));
        assert!(unique(&call(CONSUME, vec![local(2), local(3)])));
    }

    #[test]
    fn a_local_passed_on_twice_is_shared() {
        assert!(!unique(&call(CONSUME, vec![local(1), local(1)])));
        assert!(!unique(&binding(2, local(1), call(CONSUME, vec![local(1)]))));
    }

    #[test]
    fn each_branch_may_consume_it_once() {
        let branches = conditional(call(CONSUME, vec![local(1)]), local(1));
        assert!(unique(&branches));
        let twice = conditional(local(1), call(CONSUME, vec![local(1), local(1)]));
        assert!(!unique(&twice));
    }

    #[test]
    fn it_may_be_inspected_before_it_is_consumed_but_not_after() {
        let inspected = call(INSPECT, vec![local(1)]);
        assert!(unique(&binding(2, inspected.clone(), call(CONSUME, vec![local(1)]))));
        assert!(!unique(&binding(2, call(CONSUME, vec![local(1)]), inspected)));
    }

    #[test]
    fn a_closure_capturing_it_shares_it() {
        let parameters = vec![];
        let lambda = expression(ExpressionKind::Lambda { parameters, body: Box::new(local(1)) });
        assert!(!unique(&lambda));
    }

    #[test]
    fn an_ancestor_used_next_to_it_shares_its_cells() {
        let body = call(CONSUME, vec![local(1), local(5)]);
        let scope = Scope::Expression(&body);
        assert!(is_unique(&mut Layout, LocalId(1), &[LocalId(6)], scope, &Forced::default()));
        assert!(!is_unique(&mut Layout, LocalId(1), &[LocalId(5)], scope, &Forced::default()));
    }

    #[test]
    fn a_branch_known_not_to_be_taken_does_not_count() {
        let body = conditional(local(1), call(CONSUME, vec![local(1), local(1)]));
        let scope = Scope::Expression(&body);
        let mut forced = Forced::default();
        forced.insert(std::ptr::from_ref(&body), vec![Branch::Then]);
        assert!(!is_unique(&mut Layout, LocalId(1), &[], scope, &Forced::default()));
        assert!(is_unique(&mut Layout, LocalId(1), &[], scope, &forced));
    }
}
