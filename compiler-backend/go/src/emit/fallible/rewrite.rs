mod expressions;
mod statements;
mod tidy;

use rustc_hash::{FxHashMap, FxHashSet};

use super::conventions::Conventions;
use super::survey::{Candidate, Survey, unmark_sides};
use super::syntax::{every_block, is_plain, reads};
use super::zeros::Zeros;
use super::{Conversion, EitherShape, nil};
use crate::emit::locals::NUMBERED;
use crate::emit::{call, identifier_expression};
use crate::syntax::{GoDeclaration, GoExpression, GoStatement, GoType, Name};

/// A local holding an `Either` that lives on as two locals.
#[derive(Clone)]
pub(super) struct Split {
    shape: String,
    pub(super) value: String,
    pub(super) failure: String,
}

pub(super) struct Rewrite<'r> {
    shapes: &'r FxHashMap<String, EitherShape>,
    conventions: &'r Conventions,
    /// What calls in the declaration return two results, by name, with their `Either` type.
    callable: FxHashMap<String, String>,
    zeros: &'r Zeros,
    /// The names the declaration binds.
    locals: FxHashSet<String>,
    converters: &'r mut FxHashMap<(String, Conversion), String>,
    names: FxHashSet<String>,
    splits: FxHashMap<String, Split>,
    /// The failure locals that one `:=` defines and nothing assigns, by their `Left` type: one of
    /// them may take over the name of an earlier one of the type that nothing reads any more.
    reusable_failures: FxHashMap<String, String>,
    failure_names: FxHashSet<String>,
    /// The failure struct of each failure local.
    failure_types: FxHashMap<String, String>,
    /// The locals that hold one construction of an `Either` of a value that never changes, such
    /// as a stream's shared `Right(End)`, with the construction.
    constructions: FxHashMap<String, GoExpression>,
}

impl<'r> Rewrite<'r> {
    pub(super) fn new(
        shapes: &'r FxHashMap<String, EitherShape>,
        conventions: &'r Conventions,
        callable: FxHashMap<String, String>,
        zeros: &'r Zeros,
        converters: &'r mut FxHashMap<(String, Conversion), String>,
        names: FxHashSet<String>,
    ) -> Rewrite<'r> {
        Rewrite {
            shapes,
            conventions,
            callable,
            zeros,
            locals: FxHashSet::default(),
            converters,
            names,
            splits: FxHashMap::default(),
            reusable_failures: FxHashMap::default(),
            failure_names: FxHashSet::default(),
            failure_types: FxHashMap::default(),
            constructions: FxHashMap::default(),
        }
    }

    pub(super) fn declaration(&mut self, declaration: &mut GoDeclaration) {
        self.constructions = unchanging_constructions(declaration, self.shapes);
        match declaration {
            GoDeclaration::Function { name, parameters, result, body } => {
                let own = self.conventions.functions.get(name.as_str()).cloned();
                let mut split_parameters: Vec<(usize, String, String)> = self
                    .conventions
                    .split_parameters
                    .get(name.as_str())
                    .into_iter()
                    .flatten()
                    .map(|(index, shape)| (*index, parameters[*index].0.clone(), shape.clone()))
                    .collect();
                split_parameters.sort();
                let surveyed: Vec<(String, String)> = split_parameters
                    .iter()
                    .map(|(_, parameter, shape)| (parameter.clone(), shape.clone()))
                    .collect();
                self.choose_splits(body, own.as_deref(), &surveyed);
                self.locals.extend(parameters.iter().map(|(parameter, _)| parameter.clone()));
                *body = self.block(std::mem::take(body), own.as_deref());
                if let Some(own) = &own {
                    *result = Some(self.shapes[own].results());
                }
                if let Some(slots) = self.conventions.parameters.get(name.as_str()) {
                    for (index, shape) in slots {
                        if let GoType::Function { result, .. } = &mut parameters[*index].1 {
                            *result = Some(Box::new(self.shapes[shape].results()));
                        }
                    }
                }
                for (index, parameter, shape) in split_parameters.into_iter().rev() {
                    let split = self.parameter_split(&parameter, &shape, body);
                    let shape = &self.shapes[&shape];
                    parameters.splice(
                        index..=index,
                        [(split.value, shape.right.clone()), (split.failure, shape.failure_type())],
                    );
                }
                self.tidy(body);
                self.split_nested(body);
                self.drop_unread_constructions(body);
            }
            GoDeclaration::Variable { value, .. } => {
                let taken = std::mem::replace(value, nil());
                *value = self.expression(taken);
            }
            _ => {}
        }
    }

    /// Leaves out the unchanging constructions that the returns they stood for no longer read,
    /// and the locals that only they read.
    fn drop_unread_constructions(&self, body: &mut Vec<GoStatement>) {
        let mut names: FxHashSet<String> = FxHashSet::default();
        for (local, built) in &self.constructions {
            names.insert(local.clone());
            if let GoExpression::Composite { fields, .. } = built.unattributed() {
                for (_, field) in fields {
                    if let GoExpression::Identifier(name) = field.unattributed() {
                        names.insert(name.clone());
                    }
                }
            }
        }
        loop {
            let read = reads(body, &names);
            let unread = names.iter().filter(|name| !read.contains_key(*name)).cloned();
            let unread: FxHashSet<String> = unread.collect();
            let mut dropped = false;
            every_block(body, &mut |block| {
                block.retain(|statement| match statement {
                    GoStatement::Define { names, values }
                        if let ([local], [value]) = (names.as_slice(), values.as_slice())
                            && unread.contains(local)
                            && is_plain(value) =>
                    {
                        dropped = true;
                        false
                    }
                    _ => true,
                });
            });
            if !dropped {
                return;
            }
        }
    }

    /// Splits again the value locals that hold an `Either` themselves, for `Either e1 (Either e2
    /// a)`, until none is left.
    fn split_nested(&mut self, body: &mut Vec<GoStatement>) {
        if self.splits.values().any(|split| self.holds_either(split)) {
            split_locals_again(body, self.shapes, self.zeros, self.converters, &mut self.names);
        }
    }

    fn holds_either(&self, split: &Split) -> bool {
        matches!(&self.shapes[&split.shape].right, GoType::Named(name) if self.shapes.contains_key(name))
    }

    /// The two parameters a split parameter becomes. Where the body still wants the `Either`, it
    /// builds it from them first.
    fn parameter_split(
        &mut self,
        parameter: &str,
        shape: &str,
        body: &mut Vec<GoStatement>,
    ) -> Split {
        if let Some(split) = self.splits.get(parameter) {
            return split.clone();
        }
        let value = crate::emit::inlining::fresh(&self.shapes[shape].value_name, &mut self.names);
        let failure = crate::emit::inlining::fresh(&format!("err{NUMBERED}"), &mut self.names);
        let converter = self.converter(shape, Conversion::FromResults);
        body.insert(
            0,
            GoStatement::Define {
                names: vec![parameter.to_string()],
                values: vec![call(
                    identifier_expression(&converter),
                    vec![identifier_expression(&value), identifier_expression(&failure)],
                )],
            },
        );
        Split { shape: shape.to_string(), value, failure }
    }

    /// Picks the locals of a function body that become two locals.
    fn choose_splits(
        &mut self,
        body: &mut [GoStatement],
        own: Option<&str>,
        split_parameters: &[(String, String)],
    ) {
        let mut binders: FxHashMap<String, usize> = FxHashMap::default();
        let mut count = |name: Name<'_>| {
            if let Name::Binder(name) = name {
                *binders.entry(name.clone()).or_default() += 1;
            }
        };
        crate::syntax::statements_names(body, &mut count);
        self.locals = binders.keys().cloned().collect();
        let mut survey = Survey::new(
            self.shapes,
            &self.callable,
            &self.conventions.parameters,
            &self.conventions.split_parameters,
            &binders,
        );
        for (parameter, shape) in split_parameters {
            survey.candidates.insert(parameter.clone(), Candidate::parameter(shape));
        }
        survey.block(body, own);
        let chosen = survey.candidates.into_iter().filter(|(_, candidate)| candidate.splits());
        let mut chosen: Vec<(String, Candidate)> = chosen.collect();
        chosen.sort_by(|left, right| left.0.cmp(&right.0));
        for (local, candidate) in chosen {
            let shape = &self.shapes[&candidate.shape];
            let (value, failure) = match &candidate.results {
                Some(results) if candidate.calls == 1 && !candidate.reassigned => results.clone(),
                _ => (
                    crate::emit::inlining::fresh(&shape.value_name, &mut self.names),
                    crate::emit::inlining::fresh(&format!("err{NUMBERED}"), &mut self.names),
                ),
            };
            if !candidate.reassigned {
                self.reusable_failures.insert(failure.clone(), format!("{:?}", shape.left));
            }
            self.failure_names.insert(failure.clone());
            self.failure_types.insert(failure.clone(), shape.failure.clone());
            self.splits.insert(local, Split { shape: candidate.shape, value, failure });
        }
        let splits = &self.splits;
        unmark_sides(body, &|local| splits.contains_key(local));
    }
}

/// Splits the locals of a rewritten body that still hold an `Either`, again while the value
/// locals that brings hold one themselves.
pub(super) fn split_locals_again(
    body: &mut Vec<GoStatement>,
    shapes: &FxHashMap<String, EitherShape>,
    zeros: &Zeros,
    converters: &mut FxHashMap<(String, Conversion), String>,
    names: &mut FxHashSet<String>,
) {
    let none = Conventions::default();
    for _ in 0..4 {
        let mut inner = Rewrite::new(
            shapes,
            &none,
            FxHashMap::default(),
            zeros,
            &mut *converters,
            std::mem::take(names),
        );
        inner.choose_splits(body, None, &[]);
        if !inner.splits.is_empty() {
            *body = inner.block(std::mem::take(body), None);
            inner.tidy(body);
        }
        let nested = inner.splits.values().any(|split| inner.holds_either(split));
        *names = std::mem::take(&mut inner.names);
        if !nested {
            break;
        }
    }
}

/// The locals of a declaration that one `:=` defines as a construction of an `Either` and nothing
/// assigns, whose field is a constant or such a local itself.
fn unchanging_constructions(
    declaration: &mut GoDeclaration,
    shapes: &FxHashMap<String, EitherShape>,
) -> FxHashMap<String, GoExpression> {
    let mut binders: FxHashMap<String, usize> = FxHashMap::default();
    let mut written: FxHashSet<String> = FxHashSet::default();
    declaration.for_each_name_mut(&mut |name| match name {
        Name::Binder(name) => *binders.entry(name.clone()).or_default() += 1,
        Name::Written(name) => {
            written.insert(name.clone());
        }
        Name::Reference(_) => {}
    });
    let unchanging = |name: &str| binders.get(name) == Some(&1) && !written.contains(name);
    let mut constructions = FxHashMap::default();
    let GoDeclaration::Function { body, .. } = declaration else { return constructions };
    every_block(body, &mut |block| {
        for statement in block.iter() {
            let GoStatement::Define { names, values } = statement else { continue };
            let ([local], [value]) = (names.as_slice(), values.as_slice()) else { continue };
            let GoExpression::Composite { type_: GoType::Named(either), .. } = value.unattributed()
            else {
                continue;
            };
            let Some((_, field)) = shapes.get(either).and_then(|shape| shape.construction(value))
            else {
                continue;
            };
            let constant = match field.as_ref().map(GoExpression::unattributed) {
                None => true,
                Some(GoExpression::Identifier(name)) => unchanging(name),
                Some(field) => is_constant(field),
            };
            if constant && unchanging(local) {
                constructions.insert(local.clone(), value.clone());
            }
        }
    });
    constructions
}

/// A literal, or a struct of literals.
fn is_constant(value: &GoExpression) -> bool {
    match value.unattributed() {
        GoExpression::Integer(_)
        | GoExpression::Float(_)
        | GoExpression::String(_)
        | GoExpression::Rune(_)
        | GoExpression::Boolean(_) => true,
        GoExpression::Composite { fields, .. } => fields.iter().all(|(label, field)| {
            is_constant(field) || (label.as_deref() == Some("Tag") && is_tag(field))
        }),
        _ => false,
    }
}

/// A constant naming a constructor, such as `StepIntEnd`, which no code assigns.
fn is_tag(value: &GoExpression) -> bool {
    matches!(value.unattributed(), GoExpression::Identifier(_) | GoExpression::Qualified { .. })
}
