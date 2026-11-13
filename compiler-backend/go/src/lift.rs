use rustc_hash::{FxHashMap, FxHashSet};
use smol_str::format_smolstr;

use crate::mono::{
    Binding, Expression, ExpressionKind, Function, FunctionId, Guard, Guarded, Local, LocalId,
    Pattern, PatternKind, Program,
};
use crate::monotype::{Monotype, MonotypeId, Monotypes};
use crate::simplify::{for_each_child, for_each_child_mut};

pub fn lift_local_functions(
    program: Program,
    monotypes: &mut Monotypes,
    next_local: u32,
) -> Program {
    let Program { functions, entry } = program;
    let original = functions.len();
    let mut functions: Vec<Option<Function>> = functions.into_iter().map(Some).collect();
    let mut lifter = Lifter {
        created: vec![],
        next_function: original,
        monotypes,
        next_local,
        binders: FxHashMap::default(),
    };
    for index in 0..original {
        let mut function =
            functions[index].take().expect("invariant violated: function lifted twice");
        lifter.binders.clear();
        for parameter in &function.parameters {
            lifter.binders.insert(parameter.id, parameter.clone());
        }
        collect_binders(&function.body, &mut lifter.binders);
        let base = function.name.clone();
        function.body = lifter.expression(function.body, &base);
        flatten_applications(&mut function.body);
        functions[index] = Some(absorb_lambdas(function));
        for mut created in lifter.created.drain(..) {
            flatten_applications(&mut created.body);
            functions.push(Some(created));
        }
    }
    let mut functions: Vec<Function> = functions
        .into_iter()
        .map(|function| function.expect("invariant violated: function lost during lifting"))
        .collect();
    if saturate_wrappers(&mut functions, entry, &mut lifter) {
        for function in &mut functions {
            flatten_applications(&mut function.body);
        }
    }
    Program { functions, entry }
}

fn saturate_wrappers(
    functions: &mut [Function],
    entry: FunctionId,
    lifter: &mut Lifter<'_>,
) -> bool {
    let mut saturated = false;
    loop {
        let mut changed = false;
        for index in 0..functions.len() {
            if FunctionId(index as u32) == entry {
                continue;
            }
            let ExpressionKind::Apply { function, arguments } = &functions[index].body.kind else {
                continue;
            };
            let ExpressionKind::Function(callee) = function.kind else { continue };
            if callee.0 as usize == index {
                continue;
            }
            let callee = &functions[callee.0 as usize];
            if callee.parameters.len() <= arguments.len() {
                continue;
            }
            let missing = callee.parameters[arguments.len()..].to_vec();
            let result = callee.result;
            let erased = missing.iter().any(|parameter| erases(lifter.monotypes, parameter.monotype))
                || erases(lifter.monotypes, result);
            if erased {
                continue;
            }
            let fresh: Vec<Local> =
                missing.iter().map(|parameter| lifter.fresh(parameter)).collect();
            let wrapper = &mut functions[index];
            let ExpressionKind::Apply { arguments, .. } = &mut wrapper.body.kind else {
                unreachable!()
            };
            for parameter in &fresh {
                let reference = ExpressionKind::Local(parameter.id);
                arguments.push(Expression::new(reference, parameter.monotype));
            }
            wrapper.body.monotype = result;
            wrapper.result = result;
            wrapper.parameters.extend(fresh);
            changed = true;
        }
        if !changed {
            return saturated;
        }
        saturated = true;
    }
}

struct Lifter<'m> {
    created: Vec<Function>,
    next_function: usize,
    monotypes: &'m mut Monotypes,
    next_local: u32,
    binders: FxHashMap<LocalId, Local>,
}

impl Lifter<'_> {
    fn fresh(&mut self, local: &Local) -> Local {
        let id = LocalId(self.next_local);
        self.next_local += 1;
        Local { id, name: local.name.clone(), monotype: local.monotype }
    }

    fn expression(&mut self, mut expression: Expression, base: &str) -> Expression {
        for_each_child_mut(&mut expression, &mut |child| {
            let taken =
                std::mem::replace(child, Expression::new(ExpressionKind::Unit, child.monotype));
            *child = self.expression(taken, base);
        });
        let ExpressionKind::Let { bindings, body } = expression.kind else { return expression };
        if !bindings
            .iter()
            .all(|binding| matches!(binding.value.kind, ExpressionKind::Lambda { .. }))
        {
            return Expression::new(ExpressionKind::Let { bindings, body }, expression.monotype);
        }
        let group: FxHashSet<LocalId> = bindings.iter().map(|binding| binding.local.id).collect();
        let mut captured = FxHashSet::default();
        for binding in &bindings {
            free_locals(&binding.value, &mut captured);
        }
        let mut captured: Vec<Local> = captured
            .into_iter()
            .filter(|id| !group.contains(id))
            .map(|id| self.binders[&id].clone())
            .collect();
        captured.sort_by_key(|local| local.id);

        let first = self.next_function;
        self.next_function += bindings.len();
        let targets: Vec<(LocalId, FunctionId, MonotypeId)> = bindings
            .iter()
            .enumerate()
            .map(|(position, binding)| {
                let mut monotype = binding.local.monotype;
                for local in captured.iter().rev() {
                    monotype = self.monotypes.function(local.monotype, monotype);
                }
                (binding.local.id, FunctionId((first + position) as u32), monotype)
            })
            .collect();

        for binding in bindings {
            let parameters: Vec<Local> = captured.iter().map(|local| self.fresh(local)).collect();
            let renaming: FxHashMap<LocalId, Local> = captured
                .iter()
                .zip(&parameters)
                .map(|(original, parameter)| (original.id, parameter.clone()))
                .collect();
            let mut value = binding.value;
            replace_references(&mut value, &targets, &parameters, &renaming);
            let ExpressionKind::Lambda { parameters: lambda_parameters, body } = value.kind else {
                unreachable!("invariant violated: lifted binding is a lambda")
            };
            let mut all_parameters = parameters;
            all_parameters.extend(lambda_parameters);
            let name = format_smolstr!("{base}{}", crate::context::capitalise(&binding.local.name));
            let function =
                Function { name, parameters: all_parameters, result: body.monotype, body: *body };
            self.created.push(absorb_lambdas(function));
        }
        let mut body = *body;
        replace_references(&mut body, &targets, &captured, &FxHashMap::default());
        body
    }
}

fn absorb_lambdas(mut function: Function) -> Function {
    while let ExpressionKind::Lambda { .. } = function.body.kind {
        let ExpressionKind::Lambda { parameters, body } = function.body.kind else {
            unreachable!()
        };
        function.parameters.extend(parameters);
        function.body = *body;
    }
    function.result = function.body.monotype;
    function
}

fn replace_references(
    expression: &mut Expression,
    targets: &[(LocalId, FunctionId, MonotypeId)],
    captured: &[Local],
    renaming: &FxHashMap<LocalId, Local>,
) {
    if let ExpressionKind::Apply { function, arguments } = &mut expression.kind
        && let ExpressionKind::Local(id) = function.kind
        && let Some(&(_, target, monotype)) = targets.iter().find(|(local, ..)| *local == id)
    {
        for argument in arguments.iter_mut() {
            replace_references(argument, targets, captured, renaming);
        }
        let mut leading: Vec<Expression> = captured.iter().map(local_expression).collect();
        leading.append(arguments);
        **function = Expression::new(ExpressionKind::Function(target), monotype);
        *arguments = leading;
        return;
    }
    if let ExpressionKind::Local(id) = expression.kind {
        if let Some(&(_, target, monotype)) = targets.iter().find(|(local, ..)| *local == id) {
            let function = Expression::new(ExpressionKind::Function(target), monotype);
            if captured.is_empty() {
                *expression = function;
            } else {
                let arguments = captured.iter().map(local_expression).collect();
                let kind = ExpressionKind::Apply { function: Box::new(function), arguments };
                *expression = Expression::new(kind, expression.monotype);
            }
        } else if let Some(renamed) = renaming.get(&id) {
            *expression = local_expression(renamed);
        }
        return;
    }
    for_each_child_mut(expression, &mut |child| {
        replace_references(child, targets, captured, renaming)
    });
}

fn flatten_applications(expression: &mut Expression) {
    for_each_child_mut(expression, &mut |child| flatten_applications(child));
    let ExpressionKind::Apply { function, arguments } = &mut expression.kind else { return };
    if let ExpressionKind::Let { body, .. } = &mut function.kind {
        let monotype = expression.monotype;
        let arguments = std::mem::take(arguments);
        let inner =
            std::mem::replace(body.as_mut(), Expression::new(ExpressionKind::Unit, monotype));
        let kind = ExpressionKind::Apply { function: Box::new(inner), arguments };
        **body = Expression::new(kind, monotype);
        flatten_applications(body);
        body.monotype = monotype;
        let ExpressionKind::Apply { function, .. } =
            std::mem::replace(&mut expression.kind, ExpressionKind::Unit)
        else {
            unreachable!()
        };
        let mut function = *function;
        function.monotype = monotype;
        *expression = function;
        return;
    }
    let ExpressionKind::Apply { .. } = function.kind else { return };
    let ExpressionKind::Apply { function: inner, arguments: mut leading } =
        std::mem::replace(&mut function.kind, ExpressionKind::Unit)
    else {
        unreachable!()
    };
    leading.append(arguments);
    *function = inner;
    *arguments = leading;
}

fn local_expression(local: &Local) -> Expression {
    Expression::new(ExpressionKind::Local(local.id), local.monotype)
}

fn free_locals(expression: &Expression, free: &mut FxHashSet<LocalId>) {
    let mut used = FxHashSet::default();
    let mut bound = FxHashMap::default();
    collect_uses(expression, &mut used);
    collect_binders(expression, &mut bound);
    free.extend(used.into_iter().filter(|id| !bound.contains_key(id)));
}

fn collect_uses(expression: &Expression, used: &mut FxHashSet<LocalId>) {
    if let ExpressionKind::Local(id) = expression.kind {
        used.insert(id);
    }
    for_each_child(expression, &mut |child| collect_uses(child, used));
}

fn collect_binders(expression: &Expression, binders: &mut FxHashMap<LocalId, Local>) {
    match &expression.kind {
        ExpressionKind::Lambda { parameters, .. } => {
            for parameter in parameters {
                binders.insert(parameter.id, parameter.clone());
            }
        }
        ExpressionKind::Let { bindings, .. } => {
            for Binding { local, .. } in bindings {
                binders.insert(local.id, local.clone());
            }
        }
        ExpressionKind::EffectBind { local, .. } => {
            binders.insert(local.id, local.clone());
        }
        ExpressionKind::EffectEach { element, .. } => {
            binders.insert(element.id, element.clone());
        }
        ExpressionKind::Case { alternatives, .. } => {
            for alternative in alternatives {
                for pattern in &alternative.patterns {
                    pattern_binders(pattern, binders);
                }
                if let Guarded::Guards(branches) = &alternative.body {
                    for branch in branches {
                        for guard in &branch.guards {
                            if let Guard::Pattern { pattern, .. } = guard {
                                pattern_binders(pattern, binders);
                            }
                        }
                    }
                }
            }
        }
        _ => {}
    }
    for_each_child(expression, &mut |child| collect_binders(child, binders));
}

fn pattern_binders(pattern: &Pattern, binders: &mut FxHashMap<LocalId, Local>) {
    match &pattern.kind {
        PatternKind::Variable(local) => {
            binders.insert(local.id, local.clone());
        }
        PatternKind::Named { local, pattern } => {
            binders.insert(local.id, local.clone());
            pattern_binders(pattern, binders);
        }
        PatternKind::Array(elements) => {
            elements.iter().for_each(|element| pattern_binders(element, binders))
        }
        PatternKind::Record(fields) => {
            fields.iter().for_each(|(_, field)| pattern_binders(field, binders))
        }
        PatternKind::Constructor { arguments, .. } => {
            arguments.iter().for_each(|argument| pattern_binders(argument, binders))
        }
        PatternKind::Wildcard | PatternKind::Literal(_) => {}
    }
}

fn erases(monotypes: &Monotypes, monotype: MonotypeId) -> bool {
    match monotypes.get(monotype) {
        Monotype::Erased(_) => true,
        Monotype::Function(argument, result) => {
            erases(monotypes, *argument) || erases(monotypes, *result)
        }
        Monotype::Array(element)
        | Monotype::Effect(element)
        | Monotype::Reference(element)
        | Monotype::MutableArray(element)
        | Monotype::Object(element)
        | Monotype::Nullable(element)
        | Monotype::Lazy(element) => erases(monotypes, *element),
        Monotype::Record(fields) => fields.iter().any(|field| erases(monotypes, field.monotype)),
        _ => false,
    }
}
