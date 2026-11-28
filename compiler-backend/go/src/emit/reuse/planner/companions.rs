use rustc_hash::FxHashSet;

use crate::emit::reuse::Cells;
use crate::emit::reuse::plan::is_true;
use crate::emit::uniqueness::{Branch, Forced, Scope};
use crate::foreign::{Foreign, GoFunction, GoPackage, Operator};
use crate::monomorphic::traversal::{all_locals, for_each_child, mentions_local, visit};
use crate::monomorphic::{
    Alternative, Expression, ExpressionKind, Guarded, LocalId, Pattern, PatternKind,
};
use crate::purity::{can_fail, is_deferrable, is_within_size};

use super::Planner;

const USE_LIMIT: usize = 8;

const DECIDING_LIMIT: usize = 8;

const DECIDING_SIZE: usize = 12;

impl<C: Cells> Planner<'_, C> {
    pub(super) fn companions_at_uses(
        &mut self,
        target: LocalId,
        companion: &Expression,
        ancestors: &[LocalId],
        scope: Scope<'_>,
    ) {
        let roots = scope.expressions();
        let mut search = Search {
            target,
            branches: vec![],
            in_scope: vec![],
            sites: vec![],
            conditionals: vec![],
            bound: FxHashSet::default(),
        };
        for root in &roots {
            search.expression(root);
        }
        if search.sites.len() > USE_LIMIT {
            return;
        }
        let mut family = self.conflicts(target, ancestors, scope);
        family.insert(target);
        for site in &search.sites {
            let mut forced = Forced::default();
            for &(conditional, branch) in &site.branches {
                forced.insert(conditional, vec![branch]);
            }
            if self.is_linear(target, ancestors, scope, &forced) {
                self.use_companions.insert(site.expression, companion.clone());
                continue;
            }
            let mut decisions = vec![];
            for &conditional in &search.conditionals {
                if decisions.len() == DECIDING_LIMIT {
                    break;
                }
                if let Some(clean) = self.clean_branches(conditional, &family, &search, site) {
                    forced.insert(std::ptr::from_ref(conditional), clean.clone());
                    decisions.push((conditional, clean));
                }
            }
            if decisions.is_empty() || !self.is_linear(target, ancestors, scope, &forced) {
                continue;
            }
            let mut owned = companion.clone();
            for (conditional, clean) in decisions {
                let decision = self.decision(conditional, &clean);
                owned = self.both(&owned, decision);
            }
            self.use_companions.insert(site.expression, owned);
        }
    }

    fn clean_branches(
        &mut self,
        conditional: &Expression,
        family: &FxHashSet<LocalId>,
        search: &Search<'_>,
        site: &Site,
    ) -> Option<Vec<Branch>> {
        let key = std::ptr::from_ref(conditional);
        if site.branches.iter().any(|(branch, _)| *branch == key)
            || contains_expression(conditional, site.expression)
        {
            return None;
        }
        let mut decidable = |expression: &Expression| {
            is_decidable(expression)
                && all_locals(expression).iter().all(|&(local, monotype)| {
                    (!search.bound.contains(&local) || site.in_scope.contains(&local))
                        && self.cells.cell(monotype).is_none()
                })
        };
        let touches =
            |expression: &Expression| family.iter().any(|&local| mentions_local(expression, local));
        let branches: Vec<(Branch, bool)> = match &conditional.kind {
            ExpressionKind::If { condition, then, otherwise } if decidable(condition) => {
                vec![(Branch::Then, touches(then)), (Branch::Otherwise, touches(otherwise))]
            }
            ExpressionKind::Case { scrutinees, alternatives }
                if scrutinees.iter().all(decidable) =>
            {
                let mut branches = vec![];
                for (index, alternative) in alternatives.iter().enumerate() {
                    let Guarded::Unconditional(body) = &alternative.body else { return None };
                    branches.push((Branch::Alternative(index, None), touches(body)));
                }
                branches
            }
            _ => return None,
        };
        let clean: Vec<Branch> =
            branches.iter().filter(|(_, touched)| !touched).map(|(branch, _)| *branch).collect();
        let touched = clean.len() < branches.len();
        (touched && !clean.is_empty()).then_some(clean)
    }

    fn decision(&mut self, conditional: &Expression, clean: &[Branch]) -> Expression {
        match &conditional.kind {
            ExpressionKind::If { condition, .. } => match clean {
                [Branch::Then] => (**condition).clone(),
                [Branch::Otherwise] => self.negation((**condition).clone()),
                _ => self.truth(true),
            },
            ExpressionKind::Case { scrutinees, alternatives } => {
                let alternatives = alternatives
                    .iter()
                    .enumerate()
                    .map(|(index, alternative)| Alternative {
                        patterns: alternative.patterns.iter().map(shape).collect(),
                        body: Guarded::Unconditional(
                            self.truth(clean.contains(&Branch::Alternative(index, None))),
                        ),
                        position: alternative.position,
                    })
                    .collect();
                let case = ExpressionKind::Case { scrutinees: scrutinees.clone(), alternatives };
                Expression::new(case, self.boolean)
            }
            _ => self.truth(false),
        }
    }

    fn negation(&self, value: Expression) -> Expression {
        let foreign = Foreign::Operator(Operator::BooleanNot).interned();
        Expression::new(ExpressionKind::Foreign { foreign, arguments: vec![value] }, self.boolean)
    }

    fn both(&self, left: &Expression, right: Expression) -> Expression {
        if is_true(left) {
            return right;
        }
        let foreign = Foreign::Operator(Operator::BooleanAnd).interned();
        let arguments = vec![left.clone(), right];
        Expression::new(ExpressionKind::Foreign { foreign, arguments }, self.boolean)
    }
}

struct Site {
    expression: *const Expression,
    branches: Vec<(*const Expression, Branch)>,
    in_scope: FxHashSet<LocalId>,
}

struct Search<'e> {
    target: LocalId,
    branches: Vec<(*const Expression, Branch)>,
    in_scope: Vec<LocalId>,
    sites: Vec<Site>,
    conditionals: Vec<&'e Expression>,
    bound: FxHashSet<LocalId>,
}

impl<'e> Search<'e> {
    fn expression(&mut self, expression: &'e Expression) {
        let key = std::ptr::from_ref(expression);
        match &expression.kind {
            ExpressionKind::Local(id) if *id == self.target => {
                let site = Site {
                    expression: key,
                    branches: self.branches.clone(),
                    in_scope: self.in_scope.iter().copied().collect(),
                };
                self.sites.push(site);
            }
            ExpressionKind::Lambda { .. }
            | ExpressionKind::Closure { .. }
            | ExpressionKind::EffectPure(_)
            | ExpressionKind::EffectBind { .. }
            | ExpressionKind::EffectEach { .. } => {
                visit(expression, &mut |inner| bind_all(inner, &mut self.bound));
            }
            ExpressionKind::Let { bindings, body } => {
                let mark = self.in_scope.len();
                for binding in bindings {
                    self.expression(&binding.value);
                    self.bound.insert(binding.local.id);
                    self.in_scope.push(binding.local.id);
                }
                self.expression(body);
                self.in_scope.truncate(mark);
            }
            ExpressionKind::If { condition, then, otherwise } => {
                self.conditionals.push(expression);
                self.expression(condition);
                self.branch(key, Branch::Then, then);
                self.branch(key, Branch::Otherwise, otherwise);
            }
            ExpressionKind::Case { scrutinees, alternatives } => {
                self.conditionals.push(expression);
                for scrutinee in scrutinees {
                    self.expression(scrutinee);
                }
                for (index, alternative) in alternatives.iter().enumerate() {
                    let mark = self.in_scope.len();
                    alternative.for_each_local(&mut |local| {
                        self.bound.insert(local.id);
                        self.in_scope.push(local.id);
                    });
                    match &alternative.body {
                        Guarded::Unconditional(body) => {
                            self.branch(key, Branch::Alternative(index, None), body);
                        }
                        Guarded::Guards(branches) => {
                            for (position, branch) in branches.iter().enumerate() {
                                for guard in &branch.guards {
                                    let value = guard.value();
                                    self.branch(key, Branch::Alternative(index, None), value);
                                }
                                let taken = Branch::Alternative(index, Some(position));
                                self.branch(key, taken, &branch.body);
                            }
                        }
                    }
                    self.in_scope.truncate(mark);
                }
            }
            _ => for_each_child(expression, &mut |child| self.expression(child)),
        }
    }

    fn branch(&mut self, key: *const Expression, branch: Branch, expression: &'e Expression) {
        self.branches.push((key, branch));
        self.expression(expression);
        self.branches.pop();
    }
}

fn bind_all(expression: &Expression, bound: &mut FxHashSet<LocalId>) {
    match &expression.kind {
        ExpressionKind::Lambda { parameters, .. } => {
            bound.extend(parameters.iter().map(|parameter| parameter.id));
        }
        ExpressionKind::Let { bindings, .. } => {
            bound.extend(bindings.iter().map(|binding| binding.local.id));
        }
        ExpressionKind::EffectBind { local, .. }
        | ExpressionKind::EffectEach { element: local, .. } => {
            bound.insert(local.id);
        }
        ExpressionKind::Case { alternatives, .. } => {
            for alternative in alternatives {
                alternative.for_each_local(&mut |local| {
                    bound.insert(local.id);
                });
            }
        }
        _ => {}
    }
}

fn contains_expression(expression: &Expression, target: *const Expression) -> bool {
    let mut found = false;
    visit(expression, &mut |inner| found |= std::ptr::eq(inner, target));
    found
}

fn is_decidable(expression: &Expression) -> bool {
    let mut simple = true;
    visit(expression, &mut |inner| {
        simple &= match &inner.kind {
            ExpressionKind::Literal(_)
            | ExpressionKind::Unit
            | ExpressionKind::Local(_)
            | ExpressionKind::Access { .. } => true,
            ExpressionKind::Foreign { foreign, .. } => matches!(
                foreign,
                Foreign::Operator(_)
                    | Foreign::Int64 { .. }
                    | Foreign::Call { function: GoFunction { package: GoPackage::Prim, .. }, .. }
            ),
            _ => false,
        }
    });
    simple
        && is_deferrable(expression)
        && !can_fail(expression)
        && is_within_size(expression, DECIDING_SIZE)
}

fn shape(pattern: &Pattern) -> Pattern {
    let kind = match &pattern.kind {
        PatternKind::Wildcard | PatternKind::Variable(_) => PatternKind::Wildcard,
        PatternKind::Named { pattern, .. } => return shape(pattern),
        PatternKind::Literal(literal) => PatternKind::Literal(literal.clone()),
        PatternKind::Array(elements) => PatternKind::Array(elements.iter().map(shape).collect()),
        PatternKind::Record(fields) => PatternKind::Record(
            fields.iter().map(|(label, field)| (label.clone(), shape(field))).collect(),
        ),
        PatternKind::Constructor { data, constructor, arguments } => PatternKind::Constructor {
            data: data.clone(),
            constructor: *constructor,
            arguments: arguments.iter().map(shape).collect(),
        },
        PatternKind::Closure { tag, captures } => {
            PatternKind::Closure { tag: *tag, captures: captures.iter().map(shape).collect() }
        }
    };
    Pattern { kind, monotype: pattern.monotype }
}
