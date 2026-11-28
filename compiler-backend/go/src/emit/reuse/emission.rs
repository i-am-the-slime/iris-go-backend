use rustc_hash::{FxHashMap, FxHashSet};
use smol_str::SmolStr;

use super::facts::{Facts, Variant};
use super::plan::Plan;
use super::planner::Planner;
use super::{CHECKED, Cells, REUSING, Reused};
use crate::emit::kept::mark_kept_fields;
use crate::monomorphic::traversal::{for_each_child_mut, mentions_local, prune_unreachable, visit};
use crate::monomorphic::{
    Binding, Expression, ExpressionKind, Function, FunctionId, Guarded, Kept, Local, Pattern,
    PatternKind, Program,
};
use crate::monotype::{DataType, MonotypeId};
use crate::purity::is_trivial;

pub(super) struct Emission<'p> {
    program: &'p Program,
    facts: Facts,
    identifiers: FxHashMap<Variant, FunctionId>,
}

impl<'p> Emission<'p> {
    pub(super) fn new(program: &'p Program, facts: Facts) -> Emission<'p> {
        Emission { program, facts, identifiers: FxHashMap::default() }
    }

    pub(super) fn finish(mut self, cells: &mut impl Cells) -> Reused {
        let count = self.program.functions.len();
        let mut pending = vec![];
        for index in 0..count {
            let id = FunctionId(index as u32);
            self.identifiers.insert(Variant::plain(id), id);
            pending.push(Variant::plain(id));
        }
        let demanded = self.facts.demanded.len();
        let mut functions: Vec<Option<Function>> = (0..count).map(|_| None).collect();
        let mut materialized = FxHashSet::default();
        let boolean = cells.boolean();
        while let Some(variant) = pending.pop() {
            let mut function = Box::new(self.program.function(variant.function).clone());
            let plan = Planner::new(self.program, cells, &mut self.facts, variant).plan(&function);
            let callbacks = plan.callbacks.values();
            let targets = plan.calls.values().map(|(target, _, _)| target).chain(callbacks);
            let mut targets: Vec<Variant> = targets.copied().collect();
            targets.sort_unstable_by_key(|target| {
                (target.function, target.owned, target.checked, target.donor)
            });
            for target in targets {
                if !self.identifiers.contains_key(&target) {
                    let next = FunctionId(self.identifiers.len() as u32);
                    self.identifiers.insert(target, next);
                    pending.push(target);
                }
            }
            let mut next_local = plan.next_local;
            self.rewrite(&mut function.body, &plan, cells, &mut next_local);
            mark_kept_fields(&mut function.body);
            if variant.is_reusing() {
                function.name = SmolStr::new(format!("{}{REUSING}", function.name));
            }
            if variant.checked != 0 {
                function.name = SmolStr::new(format!("{}{CHECKED}", function.name));
            }
            for &(position, companion) in &plan.companions {
                let name = SmolStr::new(format!("{}Owned", function.parameters[position].name));
                let local = Local { id: companion, name, monotype: boolean };
                function.parameters.push(local);
            }
            if let Some(donor) = plan.donor {
                let monotype = function.result;
                function.parameters.push(Local { id: donor, name: "donor".into(), monotype });
            }
            let id = self.identifiers[&variant];
            materialized.extend(plan.materialized.iter().map(|&local| (id, local)));
            if functions.len() <= id.0 as usize {
                functions.resize_with(id.0 as usize + 1, || None);
            }
            functions[id.0 as usize] = Some(*function);
        }
        assert_eq!(
            demanded,
            self.facts.demanded.len(),
            "invariant violated: emission planned a variant that ownership never settled"
        );
        let mut functions: Vec<Function> = functions
            .into_iter()
            .map(|function| {
                function.expect("invariant violated: a planned variant was not emitted")
            })
            .collect();
        let mut candidates = FxHashSet::default();
        for function in &functions {
            visit(&function.body, &mut |expression| {
                if let ExpressionKind::UniqueEdge { edge, .. } = &expression.kind {
                    candidates.insert(edge.data.clone());
                }
            });
        }
        for function in &mut functions {
            untrack(&mut function.body, &candidates);
        }
        let duplicates = self.duplicates(&mut functions);
        for function in &mut functions {
            redirect(&mut function.body, &duplicates);
        }
        let (program, renumbering) = prune_unreachable(functions, self.program.entry);
        let materialized = materialized
            .into_iter()
            .filter_map(|(function, local)| Some((*renumbering.get(&function)?, local)))
            .collect();
        Reused { program, materialized, candidates }
    }

    /// The variants that equal an earlier variant of the same function once
    /// each stops calling itself. Each variant calls itself as an unnamed function while
    /// they are compared.
    fn duplicates(&self, functions: &mut [Function]) -> FxHashMap<FunctionId, FunctionId> {
        let unnamed = FunctionId(u32::MAX);
        let mut variants: Vec<(Variant, FunctionId)> = self
            .identifiers
            .iter()
            .filter(|(variant, _)| !variant.is_plain())
            .map(|(variant, id)| (*variant, *id))
            .collect();
        variants.sort_by_key(|(_, id)| *id);
        for &(_, id) in &variants {
            let itself = FxHashMap::from_iter([(id, unnamed)]);
            redirect(&mut functions[id.0 as usize].body, &itself);
        }
        let mut representatives: FxHashMap<FunctionId, Vec<FunctionId>> = FxHashMap::default();
        let mut duplicates = FxHashMap::default();
        for &(variant, id) in &variants {
            let same = |other: &FunctionId| {
                let (this, other) = (&functions[id.0 as usize], &functions[other.0 as usize]);
                this.parameters == other.parameters && this.body == other.body
            };
            let candidates = representatives.entry(variant.function).or_default();
            match candidates.iter().find(|other| same(other)) {
                Some(&representative) => {
                    duplicates.insert(id, representative);
                }
                None => candidates.push(id),
            }
        }
        for &(_, id) in &variants {
            let itself = FxHashMap::from_iter([(unnamed, id)]);
            redirect(&mut functions[id.0 as usize].body, &itself);
        }
        duplicates
    }

    fn rewrite(
        &self,
        expression: &mut Expression,
        plan: &Plan,
        cells: &mut impl Cells,
        next_local: &mut u32,
    ) {
        let key = std::ptr::from_ref(&*expression);
        if let ExpressionKind::Case { alternatives, .. } = &mut expression.kind {
            for alternative in alternatives.iter_mut() {
                for pattern in &mut alternative.patterns {
                    rewrite_pattern(pattern, plan);
                }
            }
        }
        for_each_child_mut(expression, &mut |child| self.rewrite(child, plan, cells, next_local));
        if let ExpressionKind::Case { alternatives, .. } = &mut expression.kind {
            for alternative in alternatives.iter_mut() {
                let Some(bindings) = plan.bindings.get(&std::ptr::from_ref(&*alternative)) else {
                    continue;
                };
                match &mut alternative.body {
                    Guarded::Unconditional(body) => bind_companions(body, bindings),
                    Guarded::Guards(branches) => {
                        for branch in branches {
                            bind_companions(&mut branch.body, bindings);
                        }
                    }
                }
            }
        }
        let edges = plan.edges.get(&key);
        if let Some(token) = plan.constructs.get(&key) {
            let monotype = expression.monotype;
            let position = expression.position;
            let kind = std::mem::replace(&mut expression.kind, ExpressionKind::Unit);
            let ExpressionKind::Construct { data, constructor, arguments } = kind else {
                unreachable!("invariant violated: a planned reuse is not a construction")
            };
            let cell = Box::new(Expression::new(ExpressionKind::Local(token.cell), monotype));
            *expression = match &token.condition {
                None => {
                    let kept = Kept::default();
                    let reuse = ExpressionKind::Reuse { cell, data, constructor, arguments, kept };
                    tracked(Expression::new(reuse, monotype), edges, true)
                }
                Some(condition) => {
                    let mut bindings = vec![];
                    let mut values = vec![];
                    for argument in arguments {
                        if is_trivial(&argument) {
                            values.push(argument);
                            continue;
                        }
                        let local = Local::fresh(next_local, "field".into(), argument.monotype);
                        values.push(local.expression());
                        bindings.push(Binding { local, value: argument });
                    }
                    let reuse = ExpressionKind::Reuse {
                        cell,
                        data: data.clone(),
                        constructor,
                        arguments: values.clone(),
                        kept: Kept::default(),
                    };
                    let construct =
                        ExpressionKind::Construct { data, constructor, arguments: values };
                    let choice = ExpressionKind::If {
                        condition: Box::new(condition.clone()),
                        then: Box::new(tracked(Expression::new(reuse, monotype), edges, true)),
                        otherwise: Box::new(tracked(
                            Expression::new(construct, monotype),
                            edges,
                            false,
                        )),
                    };
                    let choice = Expression::new(choice, monotype);
                    match bindings.is_empty() {
                        true => choice,
                        false => {
                            let body = Box::new(choice);
                            Expression::new(ExpressionKind::Let { bindings, body }, monotype)
                        }
                    }
                }
            };
            expression.position = position;
        } else if matches!(expression.kind, ExpressionKind::Construct { .. }) {
            let construct = std::mem::replace(
                expression,
                Expression::new(ExpressionKind::Unit, expression.monotype),
            );
            *expression = tracked(construct, edges, false);
        }
        if let Some(target) = plan.callbacks.get(&key) {
            expression.kind = ExpressionKind::Function(self.identifiers[target]);
        }
        if let Some((target, donor, companions)) = plan.calls.get(&key) {
            let id = self.identifiers[target];
            let ExpressionKind::Apply { function, arguments } = &mut expression.kind else {
                unreachable!("invariant violated: a planned variant call is not an application")
            };
            let callee = self.program.function(target.function);
            let mut parameters: Vec<MonotypeId> =
                callee.parameters.iter().map(|parameter| parameter.monotype).collect();
            for companion in companions {
                parameters.push(companion.monotype);
                arguments.push(companion.clone());
            }
            if let &Some(donor) = donor {
                parameters.push(callee.result);
                arguments.push(Expression::new(ExpressionKind::Local(donor), callee.result));
            }
            let monotype = cells.function_type(&parameters, callee.result);
            **function = Expression::new(ExpressionKind::Function(id), monotype);
        }
        if let ExpressionKind::Case { scrutinees, .. } = &mut expression.kind {
            let mut bindings = vec![];
            for (position, scrutinee) in scrutinees.iter_mut().enumerate() {
                if let Some(&local) = plan.hoisted.get(&(key, position)) {
                    let monotype = scrutinee.monotype;
                    let reference = Expression::new(ExpressionKind::Local(local), monotype);
                    let value = std::mem::replace(scrutinee, reference);
                    let local = Local { id: local, name: "scrutinee".into(), monotype };
                    bindings.push(Binding { local, value });
                }
            }
            if !bindings.is_empty() {
                let monotype = expression.monotype;
                let case =
                    std::mem::replace(expression, Expression::new(ExpressionKind::Unit, monotype));
                let body = Box::new(case);
                *expression = Expression::new(ExpressionKind::Let { bindings, body }, monotype);
            }
        }
    }
}

fn tracked(
    value: Expression,
    edges: Option<&Vec<(usize, Expression)>>,
    reused: bool,
) -> Expression {
    let Some(edges) = edges else { return value };
    if edges.is_empty() && !reused {
        return value;
    }
    let monotype = value.monotype;
    let position = value.position;
    let edges = edges.clone();
    let mut marked =
        Expression::new(ExpressionKind::UniqueEdges { value: Box::new(value), edges }, monotype);
    marked.position = position;
    marked
}

fn untrack(expression: &mut Expression, candidates: &FxHashSet<DataType>) {
    for_each_child_mut(expression, &mut |child| untrack(child, candidates));
    let ExpressionKind::UniqueEdges { value, .. } = &mut expression.kind else { return };
    let data = match &value.kind {
        ExpressionKind::Construct { data, .. } | ExpressionKind::Reuse { data, .. } => data,
        _ => return,
    };
    if !candidates.contains(data) {
        let monotype = value.monotype;
        let value =
            std::mem::replace(&mut **value, Expression::new(ExpressionKind::Unit, monotype));
        let position = expression.position;
        *expression = value;
        expression.position = position;
    }
}

fn bind_companions(body: &mut Expression, bindings: &[Binding]) {
    let mut kept: Vec<Binding> = vec![];
    for binding in bindings.iter().rev() {
        let used = mentions_local(body, binding.local.id)
            || kept.iter().any(|later| mentions_local(&later.value, binding.local.id));
        if used {
            kept.push(binding.clone());
        }
    }
    let monotype = body.monotype;
    for binding in kept {
        let inner = std::mem::replace(body, Expression::new(ExpressionKind::Unit, monotype));
        let bindings = vec![binding];
        *body = Expression::new(ExpressionKind::Let { bindings, body: Box::new(inner) }, monotype);
    }
}

fn rewrite_pattern(pattern: &mut Pattern, plan: &Plan) {
    let key = std::ptr::from_ref(&*pattern);
    match &mut pattern.kind {
        PatternKind::Named { pattern, .. } => rewrite_pattern(pattern, plan),
        PatternKind::Array(elements) => {
            elements.iter_mut().for_each(|element| rewrite_pattern(element, plan))
        }
        PatternKind::Record(fields) => {
            fields.iter_mut().for_each(|(_, field)| rewrite_pattern(field, plan))
        }
        PatternKind::Constructor { arguments, .. }
        | PatternKind::Closure { captures: arguments, .. } => {
            arguments.iter_mut().for_each(|argument| rewrite_pattern(argument, plan))
        }
        PatternKind::Wildcard | PatternKind::Variable(_) | PatternKind::Literal(_) => {}
    }
    if let Some(&local) = plan.pattern_cells.get(&key) {
        let monotype = pattern.monotype;
        let inner = std::mem::replace(pattern, Pattern { kind: PatternKind::Wildcard, monotype });
        let local = Local { id: local, name: "cell".into(), monotype };
        pattern.kind = PatternKind::Named { local, pattern: Box::new(inner) };
    }
}

fn redirect(expression: &mut Expression, targets: &FxHashMap<FunctionId, FunctionId>) {
    if let ExpressionKind::Function(id) = &mut expression.kind {
        if let Some(&target) = targets.get(id) {
            *id = target;
        }
        return;
    }
    for_each_child_mut(expression, &mut |child| redirect(child, targets));
}
