use rustc_hash::{FxHashMap, FxHashSet};

use super::EitherShape;
use super::survey::{Candidate, Survey, unmark_sides};
use super::syntax::every_block;
use super::values;
use crate::go_traversal::{self, Walk};
use crate::syntax::{GoDeclaration, GoExpression, GoStatement, GoType, Name};

/// The `Either` type of the results of a function of the type, when it returns one.
fn fallible_result(type_: &GoType, shapes: &FxHashMap<String, EitherShape>) -> Option<String> {
    match type_ {
        GoType::Function { result: Some(result), .. } => match result.as_ref() {
            GoType::Named(name) if shapes.contains_key(name) => Some(name.clone()),
            _ => None,
        },
        _ => None,
    }
}

/// The functions that return their two results: top-level functions, the function parameters
/// of top-level functions, and locals defined as function literals, each with its `Either` type.
/// The program must do nothing with them but call them and pass them on as such parameters, and
/// pass such parameters nothing but function literals and such functions.
#[derive(Default)]
pub(super) struct Conventions {
    pub(super) functions: FxHashMap<String, String>,
    pub(super) parameters: FxHashMap<String, FxHashMap<usize, String>>,
    /// For each declaration, by its position, its locals.
    locals: Vec<FxHashMap<String, String>>,
    /// The `Either` parameters of top-level functions that take the value and the failure apart,
    /// by function and position: the function is only ever called, each call passes a
    /// construction or a local, and its body only asks the parameter for its tag and fields.
    pub(super) split_parameters: FxHashMap<String, FxHashMap<usize, String>>,
    /// The marks of calls of function values that return two results, with their `Either` type.
    marks: FxHashMap<String, String>,
}

impl Conventions {
    pub(super) fn choose(
        declarations: &mut [GoDeclaration],
        shapes: &FxHashMap<String, EitherShape>,
        marks: FxHashMap<String, String>,
        fixed_signatures: &FxHashSet<String>,
    ) -> Conventions {
        let mut conventions = Conventions { marks, ..Conventions::default() };
        let mut binders: Vec<FxHashMap<String, usize>> = vec![];
        for declaration in declarations.iter_mut() {
            let mut counts: FxHashMap<String, usize> = FxHashMap::default();
            declaration.for_each_name_mut(&mut |name| {
                if let Name::Binder(name) = name {
                    *counts.entry(name.clone()).or_default() += 1;
                }
            });
            if let GoDeclaration::Function { name, parameters, result, .. } = declaration
                && !fixed_signatures.contains(name)
            {
                if let Some(GoType::Named(result)) = result
                    && shapes.contains_key(result)
                {
                    conventions.functions.insert(name.clone(), result.clone());
                }
                let slots: FxHashMap<usize, String> = parameters
                    .iter()
                    .enumerate()
                    .filter(|(_, (parameter, _))| counts.get(parameter) == Some(&1))
                    .filter_map(|(index, (_, type_))| {
                        Some((index, fallible_result(type_, shapes)?))
                    })
                    .collect();
                if !slots.is_empty() {
                    conventions.parameters.insert(name.clone(), slots);
                }
            }
            binders.push(counts);
        }
        for declaration in declarations.iter_mut() {
            let mut locals = FxHashMap::default();
            let names = declaration.all_names();
            if let GoDeclaration::Function { body, .. } = declaration {
                let counts = &binders[conventions.locals.len()];
                every_block(body, &mut |block| {
                    for statement in block.iter() {
                        if let GoStatement::Define { names: defined, values } = statement
                            && let ([local], [value]) = (defined.as_slice(), values.as_slice())
                            && let GoExpression::Function {
                                result: Some(GoType::Named(result)),
                                ..
                            } = value.unattributed()
                            && shapes.contains_key(result)
                            && counts.get(local) == Some(&1)
                        {
                            locals.insert(local.clone(), result.clone());
                        }
                    }
                });
            }
            for name in &names {
                if binders[conventions.locals.len()].contains_key(name) {
                    conventions.functions.remove(name);
                    conventions.parameters.remove(name);
                }
            }
            conventions.locals.push(locals);
        }
        loop {
            let mut check = Check {
                conventions: &mut conventions,
                position: 0,
                owner: None,
                changed: false,
                returning_results: vec![],
                literal_returns_results: false,
                benefiting: FxHashSet::default(),
            };
            for (position, declaration) in declarations.iter_mut().enumerate() {
                check.position = position;
                check.owner = match declaration {
                    GoDeclaration::Function { name, parameters, .. } => Some((
                        name.clone(),
                        parameters.iter().map(|(parameter, _)| parameter.clone()).collect(),
                    )),
                    _ => None,
                };
                if let GoDeclaration::Written { source, .. } = declaration {
                    let written: Vec<String> = check
                        .conventions
                        .functions
                        .keys()
                        .chain(check.conventions.parameters.keys())
                        .filter(|name| source.contains(name.as_str()))
                        .cloned()
                        .collect();
                    for name in written {
                        check.drop_function(&name);
                    }
                }
                let returns_results = match declaration {
                    GoDeclaration::Function { name, .. } => {
                        check.conventions.functions.contains_key(name)
                    }
                    _ => false,
                };
                check.returning_results = vec![returns_results];
                go_traversal::declaration(&mut check, declaration);
            }
            let benefiting = std::mem::take(&mut check.benefiting);
            let changed = check.changed;
            if changed {
                continue;
            }
            let before = conventions.functions.len();
            conventions.functions.retain(|name, _| benefiting.contains(name));
            if conventions.functions.len() == before {
                break;
            }
        }
        conventions.split_parameters =
            conventions.choose_split_parameters(declarations, shapes, fixed_signatures);
        conventions
    }

    fn choose_split_parameters(
        &self,
        declarations: &mut [GoDeclaration],
        shapes: &FxHashMap<String, EitherShape>,
        fixed_signatures: &FxHashSet<String>,
    ) -> FxHashMap<String, FxHashMap<usize, String>> {
        let mut chosen: FxHashMap<String, FxHashMap<usize, String>> = FxHashMap::default();
        for declaration in declarations.iter() {
            let GoDeclaration::Function { name, parameters, .. } = declaration else { continue };
            if fixed_signatures.contains(name) {
                continue;
            }
            let slots: FxHashMap<usize, String> = parameters
                .iter()
                .enumerate()
                .filter_map(|(index, (_, type_))| match type_ {
                    GoType::Named(shape) if shapes.contains_key(shape) => {
                        Some((index, shape.clone()))
                    }
                    _ => None,
                })
                .collect();
            if !slots.is_empty() {
                chosen.insert(name.clone(), slots);
            }
        }
        if chosen.is_empty() {
            return chosen;
        }
        let mut calls = SplitCalls { chosen: &mut chosen, shapes };
        for declaration in declarations.iter_mut() {
            if let GoDeclaration::Written { source, .. } = declaration {
                calls.chosen.retain(|name, _| !source.contains(name.as_str()));
            }
            go_traversal::declaration(&mut calls, declaration);
        }
        let passed = chosen.clone();
        for (position, declaration) in declarations.iter_mut().enumerate() {
            let callable = self.callable(position, declaration);
            let GoDeclaration::Function { name, parameters, body, .. } = declaration else {
                continue;
            };
            let Some(slots) = chosen.get_mut(name.as_str()) else { continue };
            let mut binders: FxHashMap<String, usize> = FxHashMap::default();
            crate::syntax::statements_names(body, &mut |name| {
                if let Name::Binder(name) = name {
                    *binders.entry(name.clone()).or_default() += 1;
                }
            });
            let own = self.functions.get(name.as_str()).cloned();
            let mut survey = Survey::new(shapes, &callable, &self.parameters, &passed, &binders);
            for (index, shape) in slots.iter() {
                let parameter = &parameters[*index].0;
                if !binders.contains_key(parameter) {
                    survey.candidates.insert(parameter.clone(), Candidate::parameter(shape));
                }
            }
            survey.block(body, own.as_deref());
            slots.retain(|index, _| {
                survey.candidates.get(&parameters[*index].0).is_some_and(Candidate::splits)
            });
            unmark_sides(body, &|_| false);
        }
        chosen.retain(|_, slots| !slots.is_empty());
        chosen
    }

    /// What calls in the declaration at the position return two results, by name.
    pub(super) fn callable(
        &self,
        position: usize,
        declaration: &GoDeclaration,
    ) -> FxHashMap<String, String> {
        let mut callable = self.functions.clone();
        callable.extend(self.marks.iter().map(|(mark, shape)| (mark.clone(), shape.clone())));
        if let GoDeclaration::Function { name, parameters, .. } = declaration
            && let Some(slots) = self.parameters.get(name)
        {
            for (index, shape) in slots {
                callable.insert(parameters[*index].0.clone(), shape.clone());
            }
        }
        callable.extend(
            self.locals[position].iter().map(|(name, shape)| (name.clone(), shape.clone())),
        );
        callable
    }
}

/// Drops the split parameters of functions the code uses other than by calling them, and those
/// that a call passes something other than a construction or a local.
struct SplitCalls<'c> {
    chosen: &'c mut FxHashMap<String, FxHashMap<usize, String>>,
    shapes: &'c FxHashMap<String, EitherShape>,
}

impl Walk for SplitCalls<'_> {
    fn expression(&mut self, value: &mut GoExpression) {
        match value {
            GoExpression::Call { function, arguments }
                if let GoExpression::Identifier(head) = function.unattributed()
                    && self.chosen.contains_key(head) =>
            {
                let head = head.clone();
                for (index, argument) in arguments.iter_mut().enumerate() {
                    if let Some(shape) = self.chosen[&head].get(&index)
                        && !passable(argument, &self.shapes[shape])
                        && let Some(slots) = self.chosen.get_mut(&head)
                    {
                        slots.remove(&index);
                    }
                    self.expression(argument);
                }
                if self.chosen[&head].is_empty() {
                    self.chosen.remove(&head);
                }
            }
            GoExpression::Identifier(name) => {
                self.chosen.remove(name.as_str());
            }
            value => go_traversal::expression(self, value),
        }
    }
}

/// Whether a call can pass the value to a split parameter: a construction or a local.
fn passable(argument: &GoExpression, shape: &EitherShape) -> bool {
    match argument.unattributed() {
        GoExpression::Identifier(_) => true,
        value => shape.construction(value).is_some(),
    }
}

/// Drops from the conventions every function that the code uses in another way.
struct Check<'c> {
    conventions: &'c mut Conventions,
    position: usize,
    /// The declaration's function and the names of its parameters.
    owner: Option<(String, Vec<String>)>,
    changed: bool,
    /// For the function the code is in and those around it, whether it returns two results.
    returning_results: Vec<bool>,
    /// Whether the next function literal is one that returns two results.
    literal_returns_results: bool,
    /// The top-level functions with a call that reads their two results as such: one that a
    /// local keeps, whose results are returned or that runs for its effects alone.
    benefiting: FxHashSet<String>,
}

impl Check<'_> {
    /// The `Either` type of a name that returns two results in the current declaration.
    fn slot(&self, name: &str) -> Option<String> {
        self.conventions
            .locals
            .get(self.position)
            .and_then(|locals| locals.get(name))
            .or_else(|| self.conventions.functions.get(name))
            .cloned()
    }

    fn drop_function(&mut self, name: &str) {
        self.changed |= self.conventions.functions.remove(name).is_some();
        self.changed |= self.conventions.parameters.remove(name).is_some();
        if let Some(locals) = self.conventions.locals.get_mut(self.position) {
            self.changed |= locals.remove(name).is_some();
        }
    }

    /// The function and parameter position, for a parameter of the declaration that returns
    /// two results.
    fn own_parameter(&self, name: &str) -> Option<(String, usize)> {
        let (function, parameters) = self.owner.as_ref()?;
        let index = parameters.iter().position(|parameter| parameter == name)?;
        self.conventions
            .parameters
            .get(function)
            .is_some_and(|slots| slots.contains_key(&index))
            .then(|| (function.clone(), index))
    }

    /// The top-level function returning two results that the value calls.
    fn called_function(&self, value: &GoExpression) -> Option<String> {
        let GoExpression::Call { function, .. } = value.unattributed() else { return None };
        let GoExpression::Identifier(name) = function.unattributed() else { return None };
        self.conventions.functions.contains_key(name).then(|| name.clone())
    }
}

impl Walk for Check<'_> {
    fn statement(&mut self, statement: &mut GoStatement) {
        let kept = match &*statement {
            GoStatement::Define { names, values } if names.len() == 1 && values.len() == 1 => {
                self.called_function(&values[0])
            }
            GoStatement::Assign { targets, values } if targets.len() == 1 && values.len() == 1 => {
                self.called_function(&values[0])
            }
            GoStatement::Variable { value: Some(value), .. } | GoStatement::Expression(value) => {
                self.called_function(value)
            }
            GoStatement::Return(Some(value)) if self.returning_results.last() == Some(&true) => {
                self.called_function(value)
            }
            _ => None,
        };
        if let Some(function) = kept {
            self.benefiting.insert(function);
        }
        if let GoStatement::Define { names, values } = &*statement
            && let ([local], [value]) = (names.as_slice(), values.as_slice())
            && matches!(value.unattributed(), GoExpression::Function { .. })
            && self
                .conventions
                .locals
                .get(self.position)
                .is_some_and(|locals| locals.contains_key(local))
        {
            self.literal_returns_results = true;
        }
        go_traversal::statement(self, statement);
        self.literal_returns_results = false;
    }

    fn expression(&mut self, value: &mut GoExpression) {
        match value {
            GoExpression::Function { body, .. } => {
                let returns_results = std::mem::take(&mut self.literal_returns_results);
                self.returning_results.push(returns_results);
                self.block(body);
                self.returning_results.pop();
            }
            GoExpression::Call { function, arguments }
                if let GoExpression::Identifier(head) = function.unattributed()
                    && head.starts_with(values::LITERAL_MARK) =>
            {
                for argument in arguments.iter_mut() {
                    self.literal_returns_results = true;
                    self.expression(argument);
                }
            }
            GoExpression::Call { function, arguments } => {
                let head = match function.unattributed() {
                    GoExpression::Identifier(name) => Some(name.clone()),
                    _ => None,
                };
                if head.is_none() {
                    self.expression(function);
                }
                let slots = head
                    .as_ref()
                    .and_then(|head| self.conventions.parameters.get(head))
                    .cloned()
                    .unwrap_or_default();
                for (index, argument) in arguments.iter_mut().enumerate() {
                    let Some(shape) = slots.get(&index) else {
                        self.expression(argument);
                        continue;
                    };
                    match argument.unattributed() {
                        GoExpression::Function { .. } => {
                            self.literal_returns_results = true;
                            self.expression(argument);
                        }
                        GoExpression::Identifier(name)
                            if self.slot(name).as_ref() == Some(shape) =>
                        {
                            self.changed |= self.conventions.parameters.remove(name).is_some();
                        }
                        GoExpression::Identifier(name)
                            if let Some((function, position)) = self.own_parameter(name)
                                && self.conventions.parameters[&function][&position] == *shape => {}
                        _ => {
                            let head = head.clone().expect("invariant violated: a named callee");
                            if let Some(slots) = self.conventions.parameters.get_mut(&head) {
                                slots.remove(&index);
                                if slots.is_empty() {
                                    self.conventions.parameters.remove(&head);
                                }
                            }
                            self.changed = true;
                            self.expression(argument);
                        }
                    }
                }
            }
            GoExpression::Identifier(name) => {
                let name = name.clone();
                if self.slot(&name).is_some() || self.conventions.parameters.contains_key(&name) {
                    self.drop_function(&name);
                }
                if let Some((function, index)) = self.own_parameter(&name) {
                    if let Some(slots) = self.conventions.parameters.get_mut(&function) {
                        slots.remove(&index);
                        if slots.is_empty() {
                            self.conventions.parameters.remove(&function);
                        }
                    }
                    self.changed = true;
                }
            }
            value => go_traversal::expression(self, value),
        }
    }
}
