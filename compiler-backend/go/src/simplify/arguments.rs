use rustc_hash::FxHashMap;
use smol_str::{SmolStr, format_smolstr};

use super::{INLINE_FUEL, INLINE_SIZE, Simplifier};
use crate::lift::collect_binders;
use crate::monomorphic::traversal::{
    for_each_binder_mut, for_each_child, for_each_child_mut, visit,
};
use crate::monomorphic::{
    Expression, ExpressionKind, Function, FunctionId, FunctionSpelling, Local, LocalId,
};
use crate::monotype::MonotypeId;
use crate::naming::capitalise;
use crate::purity::{is_within_size, size};

const SPECIALIZATIONS_PER_FUNCTION: usize = 8;
const SPECIALIZED_SIZE: usize = 800;

#[derive(Default)]
pub(super) struct ArgumentSpecializations {
    made: FxHashMap<Specialization, (FunctionId, MonotypeId)>,
    counts: FxHashMap<FunctionId, usize>,
    originals: FxHashMap<FunctionId, FunctionId>,
}

#[derive(Clone, PartialEq, Eq, Hash)]
struct Specialization {
    callee: FunctionId,
    arguments: Vec<Option<Expression>>,
}

enum KnownFunction {
    Defined,
    Built,
}

struct ParameterUses {
    occurs: bool,
    only_called: bool,
    passed_on_unchanged: bool,
}

impl Simplifier<'_> {
    pub(super) fn specialized_call(
        &mut self,
        callee: FunctionId,
        arguments: Vec<Expression>,
        monotype: MonotypeId,
    ) -> Result<Expression, Vec<Expression>> {
        let Some(templates) = self.known_arguments(callee, &arguments) else {
            return Err(arguments);
        };
        let specialization = Specialization { callee, arguments: templates };
        let Some((copy, copy_monotype)) = self.specialization(&specialization, &arguments) else {
            return Err(arguments);
        };
        let mut given = vec![];
        for (index, argument) in arguments.into_iter().enumerate() {
            match specialization.arguments.get(index) {
                Some(Some(_)) => given.extend(free_locals(&argument)),
                _ => given.push(argument),
            }
        }
        let function = Expression::new(ExpressionKind::Function(copy), copy_monotype);
        if given.is_empty() {
            return Ok(function);
        }
        let kind = ExpressionKind::Apply { function: Box::new(function), arguments: given };
        Ok(Expression::new(kind, monotype))
    }

    fn known_arguments(
        &self,
        callee: FunctionId,
        arguments: &[Expression],
    ) -> Option<Vec<Option<Expression>>> {
        if callee == self.entry {
            return None;
        }
        let function = self.functions[callee.0 as usize].as_ref()?;
        if !is_within_size(&function.body, SPECIALIZED_SIZE) {
            return None;
        }
        let mut templates: Vec<Option<Expression>> = function
            .parameters
            .iter()
            .zip(arguments)
            .enumerate()
            .map(|(index, (parameter, argument))| {
                let typed = self.monotypes.function_parts(parameter.monotype).is_some()
                    && self.monotypes.same_without_causes(argument.monotype, parameter.monotype);
                let known = typed.then(|| self.known_function(argument)).flatten()?;
                let uses = parameter_uses(&function.body, callee, index, parameter.id);
                let used = match known {
                    KnownFunction::Defined => uses.occurs,
                    KnownFunction::Built => uses.occurs && uses.only_called,
                };
                (used && uses.passed_on_unchanged).then(|| template(argument, parameter.monotype))
            })
            .collect();
        templates.resize(function.parameters.len(), None);
        let kept = function.parameters.len() - templates.iter().flatten().count();
        let passed: usize = templates
            .iter()
            .zip(arguments)
            .filter(|(template, _)| template.is_some())
            .map(|(_, argument)| free_locals(argument).len())
            .sum();
        let specializes = templates.iter().any(Option::is_some) && kept + passed > 0;
        specializes.then_some(templates)
    }

    fn known_function(&self, argument: &Expression) -> Option<KnownFunction> {
        let takes_more = |id: FunctionId, given: usize| {
            self.functions[id.0 as usize]
                .as_ref()
                .is_some_and(|function| function.parameters.len() > given)
        };
        match &argument.kind {
            ExpressionKind::Function(id) => takes_more(*id, 0).then_some(KnownFunction::Defined),
            ExpressionKind::Apply { function, arguments } => {
                let ExpressionKind::Function(id) = function.kind else { return None };
                let built =
                    takes_more(id, arguments.len()) && arguments.iter().all(is_constant_or_local);
                built.then_some(KnownFunction::Built)
            }
            ExpressionKind::Lambda { .. } => {
                is_within_size(argument, INLINE_SIZE).then_some(KnownFunction::Built)
            }
            _ => None,
        }
    }

    fn specialization(
        &mut self,
        specialization: &Specialization,
        arguments: &[Expression],
    ) -> Option<(FunctionId, MonotypeId)> {
        let specializations = &mut self.argument_specializations;
        if let Some(&made) = specializations.made.get(specialization) {
            return Some(made);
        }
        let callee = specialization.callee;
        let original = specializations.originals.get(&callee).copied().unwrap_or(callee);
        let count = specializations.counts.entry(original).or_default();
        if *count >= SPECIALIZATIONS_PER_FUNCTION {
            return None;
        }
        *count += 1;
        let copy = FunctionId(self.functions.len() as u32);
        let function = self.specialized_copy(specialization, arguments);
        let monotype = self.function_monotype(&function.parameters, function.result);
        let specializations = &mut self.argument_specializations;
        specializations.made.insert(specialization.clone(), (copy, monotype));
        specializations.originals.insert(copy, original);
        self.functions.push(None);
        self.sizes.push(size(&function.body));
        self.recursive.push(self.recursive[callee.0 as usize]);
        self.uses.push(self.uses[callee.0 as usize]);
        self.suspension.copy(callee);
        let function = self.simplified_copy(function);
        self.sizes[copy.0 as usize] = size(&function.body);
        self.functions[copy.0 as usize] = Some(function);
        Some((copy, monotype))
    }

    fn specialized_copy(
        &mut self,
        specialization: &Specialization,
        arguments: &[Expression],
    ) -> Function {
        let callee = self.functions[specialization.callee.0 as usize]
            .clone()
            .expect("invariant violated: a specialized function is known");
        let mut renaming = FxHashMap::default();
        let parameters: Vec<Local> = callee
            .parameters
            .iter()
            .map(|parameter| self.rename_binder(parameter, &mut renaming))
            .collect();
        let mut body = callee.body;
        self.rename(&mut body, &mut renaming);
        let mut kept = vec![];
        let mut names = String::new();
        for (index, parameter) in parameters.into_iter().enumerate() {
            let known = specialization.arguments.get(index).is_some_and(Option::is_some);
            let (true, Some(argument)) = (known, arguments.get(index)) else {
                kept.push(parameter);
                continue;
            };
            let mut passed = FxHashMap::default();
            for free in free_locals(argument) {
                let ExpressionKind::Local(id) = free.kind else { continue };
                let name = self.monotypes.value_name(free.monotype);
                let template = Local { id: LocalId(0), name, monotype: free.monotype };
                let extra = self.fresh(&template);
                passed.insert(id, extra.id);
                kept.push(extra);
            }
            let mut value = argument.clone();
            self.rename(&mut value, &mut passed);
            names.push_str(&capitalise(&self.argument_name(argument, &parameter)));
            self.substitute_copies(&mut body, parameter.id, &value);
        }
        let name = format_smolstr!("{}{names}", callee.name);
        let spelling =
            FunctionSpelling::Lifted { parent: callee.name.clone(), local: names.into() };
        self.monotypes.function_spellings.entry(name.clone()).or_insert(spelling);
        Function {
            name,
            origin: callee.origin,
            parameters: kept,
            result: callee.result,
            body,
            position: callee.position,
        }
    }

    fn substitute_copies(
        &mut self,
        expression: &mut Expression,
        parameter: LocalId,
        value: &Expression,
    ) {
        if let ExpressionKind::Local(id) = expression.kind
            && id == parameter
        {
            let mut copy = value.clone();
            self.rename(&mut copy, &mut FxHashMap::default());
            *expression = copy;
            return;
        }
        for_each_child_mut(expression, &mut |child| {
            self.substitute_copies(child, parameter, value)
        });
    }

    fn simplified_copy(&mut self, mut function: Function) -> Function {
        let fuel = std::mem::replace(&mut self.fuel, INLINE_FUEL);
        let names = std::mem::take(&mut self.names);
        function.body = self.expression(function.body);
        function = self.absorb_lambdas(function);
        self.adopt_names(&mut function);
        self.names = names;
        self.fuel = fuel;
        function
    }

    fn argument_name(&self, argument: &Expression, parameter: &Local) -> SmolStr {
        let applied = match &argument.kind {
            ExpressionKind::Apply { function, .. } => &function.kind,
            kind => kind,
        };
        let ExpressionKind::Function(id) = applied else { return parameter.name.clone() };
        let name = &self.functions[id.0 as usize]
            .as_ref()
            .expect("invariant violated: a known argument's function is known")
            .name;
        match self.monotypes.function_spellings.get(name) {
            Some(FunctionSpelling::Specialized { name, .. }) => name.clone(),
            Some(FunctionSpelling::Lifted { local, .. }) => local.clone(),
            _ => name.clone(),
        }
    }

    fn function_monotype(&mut self, parameters: &[Local], result: MonotypeId) -> MonotypeId {
        parameters
            .iter()
            .rev()
            .fold(result, |result, parameter| self.monotypes.function(parameter.monotype, result))
    }
}

fn is_constant_or_local(argument: &Expression) -> bool {
    match &argument.kind {
        ExpressionKind::Literal(_)
        | ExpressionKind::Unit
        | ExpressionKind::Local(_)
        | ExpressionKind::Function(_) => true,
        ExpressionKind::Construct { arguments, .. } => arguments.is_empty(),
        _ => false,
    }
}

fn parameter_uses(
    body: &Expression,
    callee: FunctionId,
    index: usize,
    parameter: LocalId,
) -> ParameterUses {
    fn walk(
        expression: &Expression,
        callee: FunctionId,
        index: usize,
        parameter: LocalId,
        uses: &mut ParameterUses,
    ) {
        let is_parameter = |expression: &Expression| matches!(expression.kind, ExpressionKind::Local(id) if id == parameter);
        match &expression.kind {
            ExpressionKind::Local(id) if *id == parameter => {
                uses.occurs = true;
                uses.only_called = false;
            }
            ExpressionKind::Function(id) if *id == callee => uses.passed_on_unchanged = false,
            ExpressionKind::Apply { function, arguments } if is_parameter(function) => {
                uses.occurs = true;
                for argument in arguments {
                    walk(argument, callee, index, parameter, uses);
                }
            }
            ExpressionKind::Apply { function, arguments } if matches!(function.kind, ExpressionKind::Function(id) if id == callee) =>
            {
                for (position, argument) in arguments.iter().enumerate() {
                    if position == index && is_parameter(argument) {
                        continue;
                    }
                    if position == index {
                        uses.passed_on_unchanged = false;
                    }
                    walk(argument, callee, index, parameter, uses);
                }
                if arguments.len() <= index {
                    uses.passed_on_unchanged = false;
                }
            }
            _ => {
                for_each_child(expression, &mut |child| walk(child, callee, index, parameter, uses))
            }
        }
    }
    let mut uses = ParameterUses { occurs: false, only_called: true, passed_on_unchanged: true };
    walk(body, callee, index, parameter, &mut uses);
    uses
}

fn template(argument: &Expression, monotype: MonotypeId) -> Expression {
    let mut template = argument.clone();
    template.monotype = monotype;
    let mut slots: FxHashMap<LocalId, LocalId> = FxHashMap::default();
    for_each_binder_mut(&mut template, &mut |local| {
        let next = LocalId(slots.len() as u32);
        local.id = *slots.entry(local.id).or_insert(next);
        local.name = SmolStr::default();
    });
    number_locals(&mut template, &mut slots);
    template
}

fn number_locals(expression: &mut Expression, slots: &mut FxHashMap<LocalId, LocalId>) {
    if let ExpressionKind::Local(id) = &mut expression.kind {
        let next = LocalId(slots.len() as u32);
        *id = *slots.entry(*id).or_insert(next);
        return;
    }
    for_each_child_mut(expression, &mut |child| number_locals(child, slots));
}

fn free_locals(argument: &Expression) -> Vec<Expression> {
    let mut bound = FxHashMap::default();
    collect_binders(argument, &mut bound);
    let mut seen = vec![];
    let mut locals = vec![];
    visit(argument, &mut |node| {
        if let ExpressionKind::Local(id) = node.kind
            && !bound.contains_key(&id)
            && !seen.contains(&id)
        {
            seen.push(id);
            locals.push(node.clone());
        }
    });
    locals
}
