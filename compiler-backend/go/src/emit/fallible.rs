//! Functions that return an `Either` return Go's `(A, EFailure)` instead.
//!
//! `ExceptT`'s bind cases on the `Either` an action returns and hands a `Left` straight back. A
//! top-level function whose Go result is an `Either` struct, and which the program only ever
//! calls, returns the `Right` value and a failure: a struct of the `Left` value and whether there
//! is one, whose zero value means there is none. A failure is returned by value, so failing
//! allocates nothing. A local that keeps such a call's result, and that the code only asks for
//! its tag and its fields, becomes the two results, so a bind reads as Go's own error handling:
//!
//! ```go
//! scope2, err := stromscope.Adopt(scope, child, r)
//! if err.Failed {
//!     return nil, err
//! }
//! ```
//!
//! Function literals, foreign functions and the values data structures keep go on passing
//! `Either` structs. Where one meets the other, a function for each `Either` type converts:
//! `EitherTFromResults(f(x))` builds the struct from a call's results, and `EitherTResults(e)`
//! takes a struct apart for a `return`.

use rustc_hash::{FxHashMap, FxHashSet};

use super::locals::NUMBERED;
use super::packages::Spelling;
use super::{DataKind, Emitter, binary, call, identifier_expression};
use crate::error::GoResult;
use crate::go_traversal::{self, Walk};
use crate::monotype::DataType;
use crate::syntax::{
    GoCase, GoDeclaration, GoDefault, GoExpression, GoStatement, GoType, Name, Reference,
    StructField,
};

/// The Go struct of one `Either` type.
#[derive(Clone)]
pub(super) struct EitherShape {
    data: DataType,
    left_tag: String,
    right_tag: String,
    left_field: String,
    right_field: String,
    left: GoType,
    right: GoType,
    /// A name for a local holding the `Right` value, marked for numbering.
    value_name: String,
    /// The struct holding a `Left` value and whether there is one, by value.
    failure: String,
}

impl EitherShape {
    fn results(&self) -> GoType {
        GoType::Results(vec![self.right.clone(), self.failure_type()])
    }

    /// Whether both sides keep their value in one field, as `Either Int Int` does.
    fn shares_field(&self) -> bool {
        self.left_field == self.right_field
    }

    fn failure_type(&self) -> GoType {
        GoType::Named(self.failure.clone())
    }

    /// The failure that says there is none: the zero value.
    fn no_failure(&self) -> GoExpression {
        GoExpression::Composite { type_: self.failure_type(), fields: vec![] }
    }

    fn failed_with(&self, left: GoExpression) -> GoExpression {
        GoExpression::Composite {
            type_: self.failure_type(),
            fields: vec![
                (Some(FAILED.into()), GoExpression::Boolean(true)),
                (Some(LEFT.into()), left),
            ],
        }
    }

    /// Which constructor a tag names: `Some(true)` for `Left`.
    fn is_left_tag(&self, tag: &GoExpression) -> Option<bool> {
        match tag.unattributed() {
            GoExpression::Identifier(name) if *name == self.left_tag => Some(true),
            GoExpression::Identifier(name) if *name == self.right_tag => Some(false),
            _ => None,
        }
    }

    /// The constructor a composite literal of the type builds, `true` for `Left`, and its field.
    fn construction(&self, value: &GoExpression) -> Option<(bool, Option<GoExpression>)> {
        let GoExpression::Composite { fields, .. } = value.unattributed() else { return None };
        let tag = fields.iter().find(|(label, _)| label.as_deref() == Some("Tag"))?;
        let left = self.is_left_tag(&tag.1)?;
        let wanted = if left { &self.left_field } else { &self.right_field };
        let field = fields.iter().find(|(label, _)| label.as_deref() == Some(wanted.as_str()));
        Some((left, field.map(|(_, value)| value.clone())))
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum Conversion {
    FromResults,
    Results,
    Failure,
}

impl Conversion {
    fn suffix(self) -> &'static str {
        match self {
            Conversion::FromResults => "FromResults",
            Conversion::Results => "Results",
            Conversion::Failure => "Failure",
        }
    }
}

const FAILED: &str = "Failed";
const LEFT: &str = "Left";

fn nil() -> GoExpression {
    identifier_expression("nil")
}

/// `err.Failed`, or `!err.Failed` for a test that there is no failure.
fn failure_test_of(failure: &str, failed: bool) -> GoExpression {
    let test = GoExpression::Field {
        value: Box::new(identifier_expression(failure)),
        name: FAILED.into(),
    };
    match failed {
        true => test,
        false => GoExpression::Unary { operator: "!", operand: Box::new(test) },
    }
}

/// The failure local a condition tests, and whether it holds when there is a failure.
fn tested_failure<'e>(
    condition: &'e GoExpression,
    failures: &FxHashSet<String>,
) -> Option<(&'e str, bool)> {
    match condition.unattributed() {
        GoExpression::Field { value, name } if name == FAILED => match value.unattributed() {
            GoExpression::Identifier(local) if failures.contains(local) => Some((local, true)),
            _ => None,
        },
        GoExpression::Unary { operator: "!", operand } => {
            let (local, failed) = tested_failure(operand, failures)?;
            Some((local, !failed))
        }
        _ => None,
    }
}

/// Whether the value is a failure struct's zero value.
fn is_no_failure(value: &GoExpression) -> bool {
    matches!(value.unattributed(), GoExpression::Composite { fields, .. } if fields.is_empty())
}

impl<Q> Emitter<'_, '_, '_, Q>
where
    Q: checking::ExternalQueries,
{
    /// Turns the functions that return an `Either` into functions with two results, and the
    /// locals that hold their results into two locals.
    pub(super) fn return_failures_apart(
        &mut self,
        declarations: &mut Vec<GoDeclaration>,
    ) -> GoResult<()> {
        let shapes = self.either_shapes()?;
        if shapes.is_empty() {
            return Ok(());
        }
        let conventions = Conventions::choose(declarations, &shapes);
        if conventions.is_empty() {
            return Ok(());
        }
        let zeros = Zeros::new(&self.type_declarations);
        let mut converters: FxHashMap<(String, Conversion), String> = FxHashMap::default();
        for (position, declaration) in declarations.iter_mut().enumerate() {
            let mut rewrite = Rewrite {
                shapes: &shapes,
                conventions: &conventions,
                callable: conventions.callable(position, declaration),
                zeros: &zeros,
                locals: FxHashSet::default(),
                converters: &mut converters,
                names: declaration.all_names(),
                splits: FxHashMap::default(),
                reusable_failures: FxHashMap::default(),
                failure_names: FxHashSet::default(),
                failure_types: FxHashMap::default(),
            };
            rewrite.declaration(declaration);
        }
        NestedResults {
            shapes: &shapes,
            zeros: &zeros,
            converters: &mut converters,
            functions: FxHashMap::default(),
        }
        .flatten(declarations, &conventions);
        let mut wanted: Vec<((String, Conversion), String)> = converters.into_iter().collect();
        wanted.sort_by(|left, right| left.1.cmp(&right.1));
        for ((shape, conversion), placeholder) in wanted {
            let shape = &shapes[&shape];
            let name = self.declare_converter(shape, conversion, &zeros, declarations)?;
            rename_global(declarations, &placeholder, &name);
        }
        self.declare_failures(&shapes, declarations);
        Ok(())
    }

    /// The failure structs the rewritten code refers to.
    fn declare_failures(
        &mut self,
        shapes: &FxHashMap<String, EitherShape>,
        declarations: &mut [GoDeclaration],
    ) {
        let mut referred: FxHashSet<String> = FxHashSet::default();
        for declaration in declarations.iter_mut() {
            declaration.for_each_reference_mut(&mut |reference| {
                if let Reference::Type(name) = reference {
                    referred.insert(name.clone());
                }
            });
        }
        let mut declared: FxHashSet<String> = FxHashSet::default();
        let mut sorted: Vec<&EitherShape> = shapes.values().collect();
        sorted.sort_by(|left, right| left.failure.cmp(&right.failure));
        for shape in sorted {
            if !referred.contains(&shape.failure) || !declared.insert(shape.failure.clone()) {
                continue;
            }
            self.homes.insert(shape.failure.clone(), shape.data.file_id);
            self.type_declarations.push(GoDeclaration::Type {
                name: shape.failure.clone(),
                type_: GoType::Struct(vec![
                    StructField::new(FAILED, GoType::Bool),
                    StructField::new(LEFT, shape.left.clone()),
                ]),
                line: None,
                member_lines: vec![],
            });
        }
    }

    /// The `Either` types whose Go struct has a tag and one field for each side.
    fn either_shapes(&mut self) -> GoResult<FxHashMap<String, EitherShape>> {
        let mut layouts: Vec<(DataType, super::DataLayout)> =
            self.data_layouts.iter().map(|(data, layout)| (data.clone(), layout.clone())).collect();
        layouts.sort_by(|left, right| left.1.name.cmp(&right.1.name));
        let mut shapes = FxHashMap::default();
        let mut failures: FxHashMap<String, String> = FxHashMap::default();
        for (data, layout) in layouts {
            if !self.context.is_type(data.file_id, data.item, "Data.Either", "Either")?
                || layout.kind != DataKind::Tagged
                || layout.boxed
                || layout.erases_arguments
                || layout.maybe.is_some()
            {
                continue;
            }
            let [left, right] = layout.constructors.as_slice() else { continue };
            let ([(left_field, left_type)], [(right_field, right_type)]) =
                (left.fields.as_slice(), right.fields.as_slice())
            else {
                continue;
            };
            let value_name = self.value_base(*right_type);
            let left_go = self.go_type(*left_type)?;
            let failure = match failures.get(&format!("{left_go:?}")) {
                Some(failure) => failure.clone(),
                None => {
                    let base = match &left_go {
                        GoType::Named(name) if name == "int32" => "Int".into(),
                        GoType::Named(name) if name == "float64" => "Number".into(),
                        GoType::Named(name) => {
                            crate::naming::capitalise(name.rsplit('.').next().unwrap_or(name))
                        }
                        GoType::String => "String".into(),
                        GoType::Int => "Int".into(),
                        GoType::Float64 => "Number".into(),
                        GoType::Bool => "Boolean".into(),
                        GoType::Rune => "Char".into(),
                        _ => format!("{}Left", layout.name),
                    };
                    let failure = self.global_name(Spelling::derived("", base, "Failure"));
                    failures.insert(format!("{left_go:?}"), failure.clone());
                    failure
                }
            };
            let shape = EitherShape {
                data: data.clone(),
                left_tag: left.tag.clone(),
                right_tag: right.tag.clone(),
                left_field: left_field.clone(),
                right_field: right_field.clone(),
                left: left_go,
                right: self.go_type(*right_type)?,
                value_name,
                failure,
            };
            shapes.insert(layout.name.clone(), shape);
        }
        Ok(shapes)
    }

    /// The function converting between an `Either` struct and a call's two results.
    fn declare_converter(
        &mut self,
        shape: &EitherShape,
        conversion: Conversion,
        zeros: &Zeros,
        declarations: &mut Vec<GoDeclaration>,
    ) -> GoResult<String> {
        let layout = self.data_layout(&shape.data)?;
        let name =
            self.global_name(Spelling::derived("", layout.name.clone(), conversion.suffix()));
        self.homes.insert(name.clone(), shape.data.file_id);
        let either = GoType::Named(layout.name.clone());
        let declaration = match conversion {
            Conversion::FromResults => {
                let value = identifier_expression("value");
                let left = GoExpression::Field {
                    value: Box::new(identifier_expression("err")),
                    name: LEFT.into(),
                };
                GoDeclaration::Function {
                    name: name.clone(),
                    parameters: vec![
                        ("value".into(), shape.right.clone()),
                        ("err".into(), shape.failure_type()),
                    ],
                    result: Some(either),
                    body: vec![
                        GoStatement::If {
                            condition: failure_test_of("err", true),
                            then: vec![GoStatement::Return(Some(self.composite(
                                &layout,
                                0,
                                vec![left],
                            )))],
                            otherwise: vec![],
                        },
                        GoStatement::Return(Some(self.composite(&layout, 1, vec![value]))),
                    ],
                }
            }
            Conversion::Results => {
                let either_value = identifier_expression("either");
                let side = |field: &str| GoExpression::Field {
                    value: Box::new(either_value.clone()),
                    name: field.to_string(),
                };
                let is_left = binary("==", side("Tag"), identifier_expression(&shape.left_tag));
                GoDeclaration::Function {
                    name: name.clone(),
                    parameters: vec![("either".into(), either)],
                    result: Some(shape.results()),
                    body: vec![
                        GoStatement::If {
                            condition: is_left,
                            then: vec![GoStatement::Return(Some(GoExpression::Results(vec![
                                zeros.zero(&shape.right),
                                shape.failed_with(side(&shape.left_field)),
                            ])))],
                            otherwise: vec![],
                        },
                        GoStatement::Return(Some(GoExpression::Results(vec![
                            side(&shape.right_field),
                            shape.no_failure(),
                        ]))),
                    ],
                }
            }
            Conversion::Failure => {
                let either_value = identifier_expression("either");
                let side = |field: &str| GoExpression::Field {
                    value: Box::new(either_value.clone()),
                    name: field.to_string(),
                };
                let is_left = binary("==", side("Tag"), identifier_expression(&shape.left_tag));
                GoDeclaration::Function {
                    name: name.clone(),
                    parameters: vec![("either".into(), either)],
                    result: Some(shape.failure_type()),
                    body: vec![
                        GoStatement::If {
                            condition: is_left,
                            then: vec![GoStatement::Return(Some(
                                shape.failed_with(side(&shape.left_field)),
                            ))],
                            otherwise: vec![],
                        },
                        GoStatement::Return(Some(shape.no_failure())),
                    ],
                }
            }
        };
        declarations.push(declaration);
        Ok(name)
    }
}

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
struct Conventions {
    functions: FxHashMap<String, String>,
    parameters: FxHashMap<String, FxHashMap<usize, String>>,
    /// For each declaration, by its position, its locals.
    locals: Vec<FxHashMap<String, String>>,
    /// The `Either` parameters of top-level functions that take the value and the failure apart,
    /// by function and position: the function is only ever called, each call passes a
    /// construction or a local, and its body only asks the parameter for its tag and fields.
    split_parameters: FxHashMap<String, FxHashMap<usize, String>>,
}

impl Conventions {
    fn choose(
        declarations: &mut [GoDeclaration],
        shapes: &FxHashMap<String, EitherShape>,
    ) -> Conventions {
        let mut conventions = Conventions::default();
        let mut binders: Vec<FxHashMap<String, usize>> = vec![];
        for declaration in declarations.iter_mut() {
            let mut counts: FxHashMap<String, usize> = FxHashMap::default();
            declaration.for_each_name_mut(&mut |name| {
                if let Name::Binder(name) = name {
                    *counts.entry(name.clone()).or_default() += 1;
                }
            });
            if let GoDeclaration::Function { name, parameters, result, .. } = declaration {
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
        conventions.split_parameters = conventions.choose_split_parameters(declarations, shapes);
        conventions
    }

    fn choose_split_parameters(
        &self,
        declarations: &mut [GoDeclaration],
        shapes: &FxHashMap<String, EitherShape>,
    ) -> FxHashMap<String, FxHashMap<usize, String>> {
        let mut chosen: FxHashMap<String, FxHashMap<usize, String>> = FxHashMap::default();
        for declaration in declarations.iter() {
            let GoDeclaration::Function { name, parameters, .. } = declaration else { continue };
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
            let mut survey = Survey {
                shapes,
                callable: &callable,
                parameters: &self.parameters,
                split_parameters: &passed,
                binders: &binders,
                candidates: FxHashMap::default(),
                facts: vec![],
            };
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

    fn is_empty(&self) -> bool {
        self.functions.is_empty()
            && self.split_parameters.is_empty()
            && self.parameters.is_empty()
            && self.locals.iter().all(FxHashMap::is_empty)
    }

    /// What calls in the declaration at the position return two results, by name.
    fn callable(&self, position: usize, declaration: &GoDeclaration) -> FxHashMap<String, String> {
        let mut callable = self.functions.clone();
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

/// Renames every reference to a global.
fn rename_global(declarations: &mut [GoDeclaration], from: &str, to: &str) {
    if from == to {
        return;
    }
    for declaration in declarations.iter_mut() {
        go_traversal::each_expression_in_declaration(declaration, |expression| {
            if let GoExpression::Identifier(name) = expression
                && name == from
            {
                *name = to.to_string();
            }
        });
    }
}

/// The zero values of Go types, for the value a function returns beside a failure.
struct Zeros {
    declared: FxHashMap<String, GoType>,
}

impl Zeros {
    fn new(type_declarations: &[GoDeclaration]) -> Zeros {
        let declared = type_declarations
            .iter()
            .filter_map(|declaration| match declaration {
                GoDeclaration::Type { name, type_, .. }
                | GoDeclaration::Alias { name, type_, .. } => Some((name.clone(), type_.clone())),
                _ => None,
            })
            .collect();
        Zeros { declared }
    }

    fn zero(&self, type_: &GoType) -> GoExpression {
        self.literal(type_, type_, 0).unwrap_or_else(|| GoExpression::Unary {
            operator: "*",
            operand: Box::new(call(
                identifier_expression("new"),
                vec![GoExpression::Type(type_.clone())],
            )),
        })
    }

    fn literal(&self, spelled: &GoType, type_: &GoType, depth: usize) -> Option<GoExpression> {
        Some(match type_ {
            GoType::Int | GoType::Float64 | GoType::Rune => GoExpression::Integer(0),
            GoType::Bool => GoExpression::Boolean(false),
            GoType::String => GoExpression::String(String::new()),
            GoType::Pointer(_)
            | GoType::Slice(_)
            | GoType::Function { .. }
            | GoType::Any
            | GoType::Erased(_) => nil(),
            GoType::EmptyStruct | GoType::Struct(_) => {
                GoExpression::Composite { type_: spelled.clone(), fields: vec![] }
            }
            GoType::Named(name)
                if matches!(
                    name.as_str(),
                    "int32"
                        | "int64"
                        | "uint64"
                        | "uint32"
                        | "uint16"
                        | "uint8"
                        | "int"
                        | "float64"
                ) =>
            {
                GoExpression::Integer(0)
            }
            GoType::Named(name) if depth < 8 => {
                let underlying = self.declared.get(name)?;
                let spelled = match underlying {
                    GoType::Struct(_) | GoType::EmptyStruct => spelled,
                    _ => underlying,
                };
                return self.literal(spelled, underlying, depth + 1);
            }
            _ => return None,
        })
    }
}

/// A local holding an `Either` that lives on as two locals.
#[derive(Clone)]
struct Split {
    shape: String,
    value: String,
    failure: String,
}

/// What the survey of a declaration learns about a local holding an `Either`.
struct Candidate {
    shape: String,
    /// Calls of fallible functions it holds the result of.
    calls: usize,
    /// Whether a statement after its definition assigns it again.
    reassigned: bool,
    /// Whether it reads the `Left` where only an `if` that returned before tells it is one, which
    /// holds as long as nothing assigns it again.
    read_after_early_return: bool,
    /// Whether a `var` declares it for the branches that follow to store into.
    joins: bool,
    /// Whether it is used in a way the two locals can't stand for.
    escapes: bool,
    /// The two locals of the last `EFromResults(value, err)` it holds.
    results: Option<(String, String)>,
}

impl Candidate {
    /// A parameter, which the calls store into as branches store into a joining local.
    fn parameter(shape: &str) -> Candidate {
        Candidate {
            shape: shape.to_string(),
            calls: 0,
            reassigned: false,
            read_after_early_return: false,
            joins: true,
            escapes: false,
            results: None,
        }
    }

    /// Whether the local becomes two: it holds a call's two results, joins branches or changes,
    /// as a fold's accumulator does.
    fn splits(&self) -> bool {
        let stays_known = !(self.reassigned && self.read_after_early_return);
        let worth_it = self.calls > 0 || self.joins || self.reassigned;
        !self.escapes && stays_known && worth_it
    }
}

struct Rewrite<'r> {
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
}

impl Rewrite<'_> {
    fn declaration(&mut self, declaration: &mut GoDeclaration) {
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
            }
            GoDeclaration::Variable { value, .. } => {
                let taken = std::mem::replace(value, nil());
                *value = self.expression(taken);
            }
            _ => {}
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
        let value = super::inlining::fresh(&self.shapes[shape].value_name, &mut self.names);
        let failure = super::inlining::fresh(&format!("err{NUMBERED}"), &mut self.names);
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
        let mut survey = Survey {
            shapes: self.shapes,
            callable: &self.callable,
            parameters: &self.conventions.parameters,
            split_parameters: &self.conventions.split_parameters,
            binders: &binders,
            candidates: FxHashMap::default(),
            facts: vec![],
        };
        for (parameter, shape) in split_parameters {
            survey.candidates.insert(parameter.clone(), Candidate::parameter(shape));
        }
        survey.block(body, own);
        let mut chosen: Vec<(String, Candidate)> =
            survey.candidates.into_iter().filter(|(_, candidate)| candidate.splits()).collect();
        chosen.sort_by(|left, right| left.0.cmp(&right.0));
        for (local, candidate) in chosen {
            let shape = &self.shapes[&candidate.shape];
            let (value, failure) = match &candidate.results {
                Some(results) if candidate.calls == 1 && !candidate.reassigned => results.clone(),
                _ => (
                    super::inlining::fresh(&shape.value_name, &mut self.names),
                    super::inlining::fresh(&format!("err{NUMBERED}"), &mut self.names),
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

    fn block(&mut self, statements: Vec<GoStatement>, own: Option<&str>) -> Vec<GoStatement> {
        let mut out = Vec::with_capacity(statements.len());
        for statement in statements {
            self.statement(statement, own, &mut out);
        }
        out
    }

    fn statement(&mut self, statement: GoStatement, own: Option<&str>, out: &mut Vec<GoStatement>) {
        match statement {
            GoStatement::Define { names, mut values }
                if names.len() == 1
                    && values.len() == 1
                    && let Some(split) = self.splits.get(&names[0]).cloned() =>
            {
                let source = values.pop().expect("invariant violated: one value");
                self.store(&split, source, true, out);
            }
            GoStatement::Variable { name, value, .. }
                if let Some(split) = self.splits.get(&name).cloned() =>
            {
                match value {
                    Some(source) => self.store(&split, source, true, out),
                    None => {
                        let shape = &self.shapes[&split.shape];
                        out.push(GoStatement::Variable {
                            name: split.value.clone(),
                            type_: shape.right.clone(),
                            value: None,
                        });
                        out.push(GoStatement::Variable {
                            name: split.failure.clone(),
                            type_: shape.failure_type(),
                            value: None,
                        });
                    }
                }
            }
            GoStatement::Assign { targets, mut values }
                if targets.len() == 1
                    && values.len() == 1
                    && let GoExpression::Identifier(target) = targets[0].unattributed()
                    && let Some(split) = self.splits.get(target).cloned() =>
            {
                let source = values.pop().expect("invariant violated: one value");
                self.store(&split, source, false, out);
            }
            GoStatement::Assign { targets, values }
                if targets.len() == values.len()
                    && targets.len() > 1
                    && targets.iter().any(|target| self.split_target(target).is_some()) =>
            {
                let mut stored_targets = Vec::with_capacity(targets.len() + 1);
                let mut stored_values = Vec::with_capacity(values.len() + 1);
                for (target, value) in targets.into_iter().zip(values) {
                    let Some(split) = self.split_target(&target) else {
                        stored_targets.push(self.expression(target));
                        stored_values.push(self.expression(value));
                        continue;
                    };
                    let (value, failure) = self.passed_apart(value, &split.shape);
                    stored_targets.push(identifier_expression(&split.value));
                    stored_targets.push(identifier_expression(&split.failure));
                    stored_values.push(value);
                    stored_values.push(failure);
                }
                out.push(GoStatement::Assign { targets: stored_targets, values: stored_values });
            }
            GoStatement::Return(Some(value)) if let Some(own) = own => {
                let returned = self.returned(value, own);
                out.push(returned);
            }
            GoStatement::Switch { value: Some(scrutinee), cases, default }
                if let Some(split) = self.split_tag(&scrutinee) =>
            {
                self.switch_on_failure(&split, cases, default, own, out);
            }
            GoStatement::Expression(value) => {
                let value = match self.fallible_call(value.clone()) {
                    Some(call) => call,
                    None => self.expression(value),
                };
                out.push(GoStatement::Expression(value));
            }
            GoStatement::Defer(value) => {
                let value = match self.fallible_call(value.clone()) {
                    Some(call) => call,
                    None => self.expression(value),
                };
                out.push(GoStatement::Defer(value));
            }
            GoStatement::Define { names, mut values }
                if let ([local], [_]) = (names.as_slice(), values.as_slice())
                    && let Some(shape) = self.callable.get(local).cloned()
                    && matches!(values[0].unattributed(), GoExpression::Function { .. }) =>
            {
                let literal = values.pop().expect("invariant violated: one value");
                values.push(self.converted_literal(literal, &shape));
                out.push(GoStatement::Define { names, values });
            }
            statement => out.push(self.nested(statement, own)),
        }
    }

    /// The statement with its expressions and blocks rewritten.
    fn nested(&mut self, statement: GoStatement, own: Option<&str>) -> GoStatement {
        match statement {
            GoStatement::Define { names, values } => GoStatement::Define {
                names,
                values: values.into_iter().map(|value| self.expression(value)).collect(),
            },
            GoStatement::Variable { name, type_, value } => GoStatement::Variable {
                name,
                type_,
                value: value.map(|value| self.expression(value)),
            },
            GoStatement::Assign { targets, values } => GoStatement::Assign {
                targets: targets.into_iter().map(|target| self.expression(target)).collect(),
                values: values.into_iter().map(|value| self.expression(value)).collect(),
            },
            GoStatement::Expression(value) => GoStatement::Expression(self.expression(value)),
            GoStatement::Defer(value) => GoStatement::Defer(self.expression(value)),
            GoStatement::Return(value) => {
                GoStatement::Return(value.map(|value| self.expression(value)))
            }
            GoStatement::If { condition, then, otherwise } => GoStatement::If {
                condition: self.expression(condition),
                then: self.block(then, own),
                otherwise: self.block(otherwise, own),
            },
            GoStatement::Switch { value, cases, default } => GoStatement::Switch {
                value: value.map(|value| self.expression(value)),
                cases: cases
                    .into_iter()
                    .map(|case| GoCase {
                        values: case
                            .values
                            .into_iter()
                            .map(|value| self.expression(value))
                            .collect(),
                        body: self.block(case.body, own),
                        line: case.line,
                    })
                    .collect(),
                default: default.map(|default| GoDefault {
                    covers: default.covers,
                    body: self.block(default.body, own),
                    line: default.line,
                }),
            },
            GoStatement::IfAssert { name, value, type_, then } => GoStatement::IfAssert {
                name,
                value: self.expression(value),
                type_,
                then: self.block(then, own),
            },
            GoStatement::Loop(body) => GoStatement::Loop(self.block(body, own)),
            GoStatement::LabeledLoop { label, body } => {
                GoStatement::LabeledLoop { label, body: self.block(body, own) }
            }
            GoStatement::Range { index, element, iterable, body } => GoStatement::Range {
                index,
                element,
                iterable: self.expression(iterable),
                body: self.block(body, own),
            },
            GoStatement::Counting { variable, start, end, body } => GoStatement::Counting {
                variable,
                start: self.expression(start),
                end: self.expression(end),
                body: self.block(body, own),
            },
            GoStatement::CountingDown { variable, start, body } => GoStatement::CountingDown {
                variable,
                start: self.expression(start),
                body: self.block(body, own),
            },
            statement @ (GoStatement::Continue
            | GoStatement::Break
            | GoStatement::BreakTo(_)
            | GoStatement::Line(_)) => statement,
        }
    }

    /// Stores an `Either` into a split local's two locals.
    fn store(
        &mut self,
        split: &Split,
        source: GoExpression,
        declare: bool,
        out: &mut Vec<GoStatement>,
    ) {
        let shape = &self.shapes[&split.shape];
        let value = identifier_expression(&split.value);
        let failure = identifier_expression(&split.failure);
        if let Some((_, joined_value, joined_failure)) = joined_results(&source) {
            if (&joined_value, &joined_failure) != (&split.value, &split.failure) {
                let values = vec![
                    identifier_expression(&joined_value),
                    identifier_expression(&joined_failure),
                ];
                out.push(match declare {
                    true => GoStatement::Define {
                        names: vec![split.value.clone(), split.failure.clone()],
                        values,
                    },
                    false => GoStatement::Assign { targets: vec![value, failure], values },
                });
            }
            return;
        }
        if let Some(source) = self.fallible_call(source.clone()) {
            out.push(match declare {
                true => GoStatement::Define {
                    names: vec![split.value.clone(), split.failure.clone()],
                    values: vec![source],
                },
                false => {
                    GoStatement::Assign { targets: vec![value, failure], values: vec![source] }
                }
            });
            return;
        }
        let (left, field) = shape
            .construction(&source)
            .expect("invariant violated: a split local holds a call or a construction");
        let side = if left { &shape.left } else { &shape.right };
        let field = match field {
            Some(field) => self.expression(field),
            None => self.zeros.zero(side),
        };
        let (right_type, left_type) = (shape.right.clone(), shape.failure_type());
        match (left, declare) {
            (false, true) => {
                out.push(match super::operators::is_untyped_constant(field.unattributed()) {
                    true => GoStatement::Variable {
                        name: split.value.clone(),
                        type_: right_type,
                        value: Some(field),
                    },
                    false => GoStatement::Define {
                        names: vec![split.value.clone()],
                        values: vec![field],
                    },
                });
                out.push(GoStatement::Variable {
                    name: split.failure.clone(),
                    type_: left_type,
                    value: None,
                });
            }
            (true, true) => {
                out.push(GoStatement::Variable {
                    name: split.value.clone(),
                    type_: right_type,
                    value: None,
                });
                out.push(GoStatement::Define {
                    names: vec![split.failure.clone()],
                    values: vec![self.failure(field, shape)],
                });
            }
            (false, false) if self.holds_either(split) => {
                out.push(GoStatement::Assign { targets: vec![value], values: vec![field] });
                out.push(GoStatement::Assign {
                    targets: vec![failure],
                    values: vec![shape.no_failure()],
                });
            }
            (false, false) => out.push(GoStatement::Assign {
                targets: vec![value, failure],
                values: vec![field, shape.no_failure()],
            }),
            (true, false) => {
                let stored = self.failure(field, shape);
                if stored != failure {
                    out.push(GoStatement::Assign { targets: vec![failure], values: vec![stored] });
                }
            }
        }
    }

    /// The failure of a `Left` value: the failure it was read from, when it is one, else a new one.
    fn failure(&self, value: GoExpression, shape: &EitherShape) -> GoExpression {
        if let GoExpression::Field { value: from, name } = value.unattributed()
            && name == LEFT
            && let GoExpression::Identifier(from) = from.unattributed()
            && self.failure_types.get(from) == Some(&shape.failure)
        {
            return identifier_expression(from);
        }
        shape.failed_with(value)
    }

    /// The `return` of a fallible function, returning its two results.
    fn returned(&mut self, value: GoExpression, own: &str) -> GoStatement {
        let shape = &self.shapes[own];
        if let GoExpression::Identifier(local) = value.unattributed()
            && let Some(split) = self.splits.get(local)
        {
            return GoStatement::Return(Some(GoExpression::Results(vec![
                identifier_expression(&split.value),
                identifier_expression(&split.failure),
            ])));
        }
        if let Some(call) = self.fallible_call(value.clone()) {
            return GoStatement::Return(Some(call));
        }
        if let Some((left, field)) = shape.construction(&value) {
            let side = if left { &shape.left } else { &shape.right };
            let field = match field {
                Some(field) => self.expression(field),
                None => self.zeros.zero(side),
            };
            let results = match left {
                true => vec![self.zeros.zero(&shape.right), self.failure(field, shape)],
                false => vec![field, shape.no_failure()],
            };
            return GoStatement::Return(Some(GoExpression::Results(results)));
        }
        let value = self.expression(value);
        let converter = self.converter(own, Conversion::Results);
        GoStatement::Return(Some(call(identifier_expression(&converter), vec![value])))
    }

    /// A `switch` on a split local's tag, as an `if` on its failure.
    fn switch_on_failure(
        &mut self,
        split: &Split,
        cases: Vec<GoCase>,
        default: Option<GoDefault>,
        own: Option<&str>,
        out: &mut Vec<GoStatement>,
    ) {
        let shape = &self.shapes[&split.shape];
        let mut left = None;
        let mut right = None;
        for case in cases {
            let is_left = case.values.iter().find_map(|value| shape.is_left_tag(value));
            let body = with_line(case.line, case.body);
            match is_left {
                Some(true) => left = Some(body),
                _ => right = Some(body),
            }
        }
        if let Some(default) = default {
            let body = with_line(default.line, default.body);
            if left.is_none() {
                left = Some(body);
            } else {
                right = Some(body);
            }
        }
        let left = self.block(left.unwrap_or_default(), own);
        let right = self.block(right.unwrap_or_default(), own);
        if let Some(moved) = moved_results(&left, &right, split) {
            out.extend(
                left.into_iter().filter(|statement| matches!(statement, GoStatement::Line(_))),
            );
            out.push(moved);
            return;
        }
        let failed = failure_test_of(&split.failure, true);
        if breaks_out(&left) || breaks_out(&right) {
            out.push(GoStatement::Switch {
                value: None,
                cases: vec![GoCase { values: vec![failed], body: left, line: None }],
                default: Some(GoDefault { covers: vec![], body: right, line: None }),
            });
            return;
        }
        out.push(GoStatement::If { condition: failed, then: left, otherwise: right });
    }

    /// The split local whose tag the scrutinee reads.
    fn split_tag(&self, scrutinee: &GoExpression) -> Option<Split> {
        let GoExpression::Field { value, name } = scrutinee.unattributed() else { return None };
        let GoExpression::Identifier(local) = value.unattributed() else { return None };
        (name == "Tag").then(|| self.splits.get(local).cloned()).flatten()
    }

    fn fallible_call_name(&self, function: &GoExpression) -> Option<String> {
        match function.unattributed() {
            GoExpression::Identifier(name) => self.callable.get(name).cloned(),
            _ => None,
        }
    }

    /// The arguments of a call, the function literals it passes to parameters that return two
    /// results returning them.
    fn arguments(
        &mut self,
        function: &GoExpression,
        arguments: Vec<GoExpression>,
    ) -> Vec<GoExpression> {
        let slots = match function.unattributed() {
            GoExpression::Identifier(name) => self.conventions.parameters.get(name),
            _ => None,
        };
        let slots = slots.cloned().unwrap_or_default();
        let split = match function.unattributed() {
            GoExpression::Identifier(name) => self.conventions.split_parameters.get(name),
            _ => None,
        };
        let split = split.cloned().unwrap_or_default();
        let mut out = Vec::with_capacity(arguments.len());
        for (index, argument) in arguments.into_iter().enumerate() {
            match (slots.get(&index), split.get(&index)) {
                (Some(shape), _)
                    if matches!(argument.unattributed(), GoExpression::Function { .. }) =>
                {
                    out.push(self.converted_literal(argument, shape));
                }
                (_, Some(shape)) => {
                    let (value, failure) = self.passed_apart(argument, shape);
                    out.push(value);
                    out.push(failure);
                }
                _ => out.push(self.expression(argument)),
            }
        }
        out
    }

    fn split_target(&self, target: &GoExpression) -> Option<Split> {
        match target.unattributed() {
            GoExpression::Identifier(local) => self.splits.get(local).cloned(),
            _ => None,
        }
    }

    /// An `Either` passed to a split parameter, as its value and its failure.
    fn passed_apart(
        &mut self,
        argument: GoExpression,
        shape: &str,
    ) -> (GoExpression, GoExpression) {
        let either = &self.shapes[shape];
        if let GoExpression::Identifier(local) = argument.unattributed() {
            if let Some(split) = self.splits.get(local) {
                return (
                    identifier_expression(&split.value),
                    identifier_expression(&split.failure),
                );
            }
            let right = GoExpression::Field {
                value: Box::new(argument.clone()),
                name: either.right_field.clone(),
            };
            let converter = self.converter(shape, Conversion::Failure);
            return (right, call(identifier_expression(&converter), vec![argument]));
        }
        let (left, field) = either
            .construction(&argument)
            .expect("invariant violated: a split parameter is passed a local or a construction");
        let side = if left { &either.left } else { &either.right };
        let field = match field {
            Some(field) => self.expression(field),
            None => self.zeros.zero(side),
        };
        let either = &self.shapes[shape];
        match left {
            true => (self.zeros.zero(&either.right), self.failure(field, either)),
            false => (field, either.no_failure()),
        }
    }

    /// A function literal returning an `Either`, returning its two results instead.
    fn converted_literal(&mut self, literal: GoExpression, shape: &str) -> GoExpression {
        match literal {
            GoExpression::Attributed { line, value } => GoExpression::Attributed {
                line,
                value: Box::new(self.converted_literal(*value, shape)),
            },
            GoExpression::Function { parameters, body, .. } => GoExpression::Function {
                parameters,
                result: Some(self.shapes[shape].results()),
                body: self.block(body, Some(shape)),
            },
            value => self.expression(value),
        }
    }

    /// The call of a fallible function the value is, with its arguments rewritten.
    fn fallible_call(&mut self, value: GoExpression) -> Option<GoExpression> {
        match value {
            GoExpression::Attributed { line, value } => {
                let value = self.fallible_call(*value)?;
                Some(GoExpression::Attributed { line, value: Box::new(value) })
            }
            GoExpression::Call { function, arguments }
                if self.fallible_call_name(&function).is_some() =>
            {
                let arguments = self.arguments(&function, arguments);
                Some(GoExpression::Call { function, arguments })
            }
            _ => None,
        }
    }

    fn converter(&mut self, shape: &str, conversion: Conversion) -> String {
        converter(self.converters, shape, conversion)
    }

    fn expression(&mut self, value: GoExpression) -> GoExpression {
        match value {
            GoExpression::Field { value, name } => {
                if let GoExpression::Identifier(local) = value.unattributed()
                    && let Some(split) = self.splits.get(local)
                {
                    let shape = &self.shapes[&split.shape];
                    let side = match read_side(&name) {
                        Some((left, _)) => Some(left),
                        None if shape.shares_field() => None,
                        None if name == shape.right_field => Some(false),
                        None if name == shape.left_field => Some(true),
                        None => None,
                    };
                    if side == Some(false) {
                        return identifier_expression(&split.value);
                    }
                    if side == Some(true) {
                        return GoExpression::Field {
                            value: Box::new(identifier_expression(&split.failure)),
                            name: LEFT.into(),
                        };
                    }
                }
                GoExpression::Field { value: Box::new(self.expression(*value)), name }
            }
            GoExpression::Binary { operator, left, right } if matches!(operator, "==" | "!=") => {
                if let Some(test) = self.failure_test(operator, &left, &right) {
                    return test;
                }
                GoExpression::Binary {
                    operator,
                    left: Box::new(self.expression(*left)),
                    right: Box::new(self.expression(*right)),
                }
            }
            GoExpression::Call { function, arguments }
                if let Some(shape) = self.fallible_call_name(&function) =>
            {
                let arguments = self.arguments(&function, arguments);
                let converter = self.converter(&shape, Conversion::FromResults);
                call(
                    identifier_expression(&converter),
                    vec![GoExpression::Call { function, arguments }],
                )
            }
            GoExpression::Call { function, arguments }
                if matches!(function.unattributed(), GoExpression::Identifier(_)) =>
            {
                let arguments = self.arguments(&function, arguments);
                GoExpression::Call { function, arguments }
            }
            GoExpression::Function { parameters, result, body } => {
                let body = self.block(body, None);
                GoExpression::Function { parameters, result, body }
            }
            mut value => {
                struct Children<'a, 'r>(&'a mut Rewrite<'r>);
                impl Walk for Children<'_, '_> {
                    fn expression(&mut self, value: &mut GoExpression) {
                        let taken = std::mem::replace(value, nil());
                        *value = self.0.expression(taken);
                    }
                    fn block(&mut self, _: &mut Vec<GoStatement>) {}
                }
                go_traversal::expression(&mut Children(self), &mut value);
                value
            }
        }
    }

    /// `local.Tag == tag` of a split local, as a test of its failure.
    fn failure_test(
        &self,
        operator: &str,
        left: &GoExpression,
        right: &GoExpression,
    ) -> Option<GoExpression> {
        let (field, tag) = match self.split_tag(left) {
            Some(split) => (split, right),
            None => (self.split_tag(right)?, left),
        };
        let shape = &self.shapes[&field.shape];
        let is_left = shape.is_left_tag(tag)?;
        let failed = (operator == "==") == is_left;
        Some(failure_test_of(&field.failure, failed))
    }

    /// Settles the split locals' declarations once the body is rewritten: a failure branch that
    /// ends ends the `if`, the value takes the name of the local it was copied into, and what
    /// nothing reads is `_`.
    fn tidy(&self, body: &mut Vec<GoStatement>) {
        if self.splits.is_empty() {
            return;
        }
        let pairs: FxHashMap<String, String> = self
            .splits
            .values()
            .map(|split| (split.failure.clone(), split.value.clone()))
            .collect();
        every_block(body, &mut |block| pass_split_once(block, &pairs));
        every_block(body, &mut |block| return_early(block, &self.failure_names));
        let values: FxHashSet<String> =
            self.splits.values().map(|split| split.value.clone()).collect();
        let adopted = adopt_copies(body, &values);
        let mut split_names: FxHashSet<String> =
            values.into_iter().map(|value| adopted.get(&value).cloned().unwrap_or(value)).collect();
        split_names.extend(self.failure_names.iter().cloned());
        forward_moves(body, &split_names);
        split_names.extend(call_results(body));
        loop {
            let read = reads(body, &split_names);
            let before = body.clone();
            drop_unread(body, &split_names, &read);
            if *body == before {
                break;
            }
        }
        reuse_failure_names(body, &self.reusable_failures);
        declare_each_once(body, &split_names);
        every_block(body, &mut |block| {
            for statement in block.iter_mut() {
                if let GoStatement::If { condition, then, otherwise } = statement
                    && then.iter().all(|statement| matches!(statement, GoStatement::Line(_)))
                    && let Some((failure, failed)) = tested_failure(condition, &self.failure_names)
                        .map(|(failure, failed)| (failure.to_string(), failed))
                {
                    *condition = failure_test_of(&failure, !failed);
                    *then = std::mem::take(otherwise);
                }
            }
        });
    }
}

/// `if err.Failed { return j(…, zero, err) } else { return j(…, value, F{}) }` as `return j(…,
/// value, err)`: a split parameter's value is not read where there is a failure. The two calls
/// differ only there.
fn pass_split_once(block: &mut [GoStatement], pairs: &FxHashMap<String, String>) {
    for statement in block.iter_mut() {
        let GoStatement::If { condition, then, otherwise } = &*statement else { continue };
        let failures: FxHashSet<String> = pairs.keys().cloned().collect();
        let Some((failure, true)) = tested_failure(condition, &failures) else { continue };
        let value = &pairs[failure];
        let (Some(failed), Some(succeeded)) = (only_call(then), only_call(otherwise)) else {
            continue;
        };
        let Some(merged) = merged_call(failed, succeeded, failure, value) else { continue };
        *statement = merged;
    }
}

/// The one statement of a branch, when it returns or runs a call.
fn only_call(statements: &[GoStatement]) -> Option<&GoStatement> {
    let mut rest = statements.iter().filter(|statement| !matches!(statement, GoStatement::Line(_)));
    let (Some(statement), None) = (rest.next(), rest.next()) else { return None };
    let call = match statement {
        GoStatement::Return(Some(value)) | GoStatement::Expression(value) => value,
        _ => return None,
    };
    matches!(call.unattributed(), GoExpression::Call { .. }).then_some(statement)
}

fn merged_call(
    failed: &GoStatement,
    succeeded: &GoStatement,
    failure: &str,
    value: &str,
) -> Option<GoStatement> {
    let arguments = |statement: &GoStatement| match statement {
        GoStatement::Return(Some(call)) | GoStatement::Expression(call) => {
            match call.unattributed() {
                GoExpression::Call { function, arguments } => {
                    Some((function.clone(), arguments.clone()))
                }
                _ => None,
            }
        }
        _ => None,
    };
    let (failed_function, failed_arguments) = arguments(failed)?;
    let (function, mut merged) = arguments(succeeded)?;
    if failed_function.unattributed() != function.unattributed()
        || failed_arguments.len() != merged.len()
        || std::mem::discriminant(failed) != std::mem::discriminant(succeeded)
    {
        return None;
    }
    let is = |argument: &GoExpression, name: &str| matches!(argument.unattributed(), GoExpression::Identifier(found) if found == name);
    let mut index = 0;
    let mut passed = false;
    while index < merged.len() {
        if failed_arguments[index].unattributed() == merged[index].unattributed() {
            index += 1;
            continue;
        }
        let pair = index + 1 < merged.len()
            && is_plain(&failed_arguments[index])
            && is(&merged[index], value)
            && is(&failed_arguments[index + 1], failure)
            && is_no_failure(&merged[index + 1]);
        if !pair || passed {
            return None;
        }
        merged[index + 1] = identifier_expression(failure);
        passed = true;
        index += 2;
    }
    if !passed {
        return None;
    }
    let call = GoExpression::Call { function, arguments: merged };
    Some(match succeeded {
        GoStatement::Return(_) => GoStatement::Return(Some(call)),
        _ => GoStatement::Expression(call),
    })
}

/// The name a converter is called by until it is declared.
fn converter(
    converters: &mut FxHashMap<(String, Conversion), String>,
    shape: &str,
    conversion: Conversion,
) -> String {
    converters
        .entry((shape.to_string(), conversion))
        .or_insert_with(|| format!("\u{0}{shape}{}", conversion.suffix()))
        .clone()
}

/// The functions returning `Either e1 (Either e2 a)` return `(A, E2Failure, E1Failure)`, and the
/// calls that keep both results take the three apart, so that the inner `Either` can be split as
/// the outer one is.
struct NestedResults<'n> {
    shapes: &'n FxHashMap<String, EitherShape>,
    zeros: &'n Zeros,
    converters: &'n mut FxHashMap<(String, Conversion), String>,
    /// By function, its outer and inner `Either` types.
    functions: FxHashMap<String, (String, String)>,
}

impl NestedResults<'_> {
    fn flatten(&mut self, declarations: &mut [GoDeclaration], conventions: &Conventions) {
        for (function, outer) in &conventions.functions {
            if let GoType::Named(inner) = &self.shapes[outer].right
                && self.shapes.contains_key(inner)
            {
                self.functions.insert(function.clone(), (outer.clone(), inner.clone()));
            }
        }
        loop {
            let mut uses =
                NestedUses { functions: &mut self.functions, owner: None, changed: false };
            for declaration in declarations.iter_mut() {
                if let GoDeclaration::Written { source, .. } = declaration {
                    let written: Vec<String> = uses
                        .functions
                        .keys()
                        .filter(|name| source.contains(name.as_str()))
                        .cloned()
                        .collect();
                    for name in written {
                        uses.functions.remove(&name);
                        uses.changed = true;
                    }
                }
                uses.owner = match declaration {
                    GoDeclaration::Function { name, .. } => Some(name.clone()),
                    _ => None,
                };
                go_traversal::declaration(&mut uses, declaration);
            }
            if !uses.changed {
                break;
            }
        }
        if self.functions.is_empty() {
            return;
        }
        for declaration in declarations.iter_mut() {
            let mut names = declaration.all_names();
            let GoDeclaration::Function { name, result, body, .. } = declaration else { continue };
            let own = self.functions.get(name.as_str()).cloned();
            if let Some((outer, inner)) = &own {
                let (outer, inner) = (&self.shapes[outer], &self.shapes[inner]);
                *result = Some(GoType::Results(vec![
                    inner.right.clone(),
                    inner.failure_type(),
                    outer.failure_type(),
                ]));
            }
            let mut changed = false;
            *body = self.block(std::mem::take(body), own.as_ref(), &mut names, &mut changed);
            if changed {
                split_locals_again(body, self.shapes, self.zeros, self.converters, &mut names);
            }
        }
    }

    fn block(
        &mut self,
        statements: Vec<GoStatement>,
        own: Option<&(String, String)>,
        names: &mut FxHashSet<String>,
        changed: &mut bool,
    ) -> Vec<GoStatement> {
        let mut out = Vec::with_capacity(statements.len());
        for statement in statements {
            self.statement(statement, own, names, changed, &mut out);
        }
        out
    }

    fn statement(
        &mut self,
        statement: GoStatement,
        own: Option<&(String, String)>,
        names: &mut FxHashSet<String>,
        changed: &mut bool,
        out: &mut Vec<GoStatement>,
    ) {
        match statement {
            GoStatement::Define { names: defined, values }
                if defined.len() == 2
                    && let Some((_, inner)) = self.called(&values) =>
            {
                *changed = true;
                let (kept, failure) = (defined[0].clone(), defined[1].clone());
                let (value, inner_failure) = match kept.as_str() {
                    "_" => ("_".to_string(), "_".to_string()),
                    _ => self.fresh(&inner, names),
                };
                out.push(GoStatement::Define {
                    names: vec![value.clone(), inner_failure.clone(), failure],
                    values,
                });
                if kept != "_" {
                    let joined = self.joined(&inner, &value, &inner_failure);
                    out.push(GoStatement::Define { names: vec![kept], values: vec![joined] });
                }
            }
            GoStatement::Assign { targets, values }
                if targets.len() == 2
                    && let Some((_, inner)) = self.called(&values) =>
            {
                *changed = true;
                let kept = match targets[0].unattributed() {
                    GoExpression::Identifier(kept) => kept.clone(),
                    _ => unreachable!("invariant violated: a call's results go to locals"),
                };
                let (value, inner_failure) = match kept.as_str() {
                    "_" => ("_".to_string(), "_".to_string()),
                    _ => self.fresh(&inner, names),
                };
                let shape = &self.shapes[&inner];
                if kept != "_" {
                    out.push(GoStatement::Variable {
                        name: value.clone(),
                        type_: shape.right.clone(),
                        value: None,
                    });
                    out.push(GoStatement::Variable {
                        name: inner_failure.clone(),
                        type_: shape.failure_type(),
                        value: None,
                    });
                }
                let failure = targets[1].clone();
                out.push(GoStatement::Assign {
                    targets: vec![
                        identifier_expression(&value),
                        identifier_expression(&inner_failure),
                        failure,
                    ],
                    values,
                });
                if kept != "_" {
                    let joined = self.joined(&inner, &value, &inner_failure);
                    out.push(GoStatement::Assign {
                        targets: vec![identifier_expression(&kept)],
                        values: vec![joined],
                    });
                }
            }
            GoStatement::Return(Some(value)) if let Some((outer, inner)) = own => {
                let (outer, inner) = (outer.clone(), inner.clone());
                self.returned(value, &outer, &inner, names, out);
            }
            GoStatement::If { condition, then, otherwise } => out.push(GoStatement::If {
                condition,
                then: self.block(then, own, names, changed),
                otherwise: self.block(otherwise, own, names, changed),
            }),
            GoStatement::Switch { value, cases, default } => out.push(GoStatement::Switch {
                value,
                cases: cases
                    .into_iter()
                    .map(|case| GoCase {
                        values: case.values,
                        body: self.block(case.body, own, names, changed),
                        line: case.line,
                    })
                    .collect(),
                default: default.map(|default| GoDefault {
                    covers: default.covers,
                    body: self.block(default.body, own, names, changed),
                    line: default.line,
                }),
            }),
            GoStatement::IfAssert { name, value, type_, then } => out.push(GoStatement::IfAssert {
                name,
                value,
                type_,
                then: self.block(then, own, names, changed),
            }),
            GoStatement::Loop(body) => {
                out.push(GoStatement::Loop(self.block(body, own, names, changed)))
            }
            GoStatement::LabeledLoop { label, body } => out.push(GoStatement::LabeledLoop {
                label,
                body: self.block(body, own, names, changed),
            }),
            GoStatement::Range { index, element, iterable, body } => out.push(GoStatement::Range {
                index,
                element,
                iterable,
                body: self.block(body, own, names, changed),
            }),
            GoStatement::Counting { variable, start, end, body } => {
                out.push(GoStatement::Counting {
                    variable,
                    start,
                    end,
                    body: self.block(body, own, names, changed),
                })
            }
            GoStatement::CountingDown { variable, start, body } => {
                out.push(GoStatement::CountingDown {
                    variable,
                    start,
                    body: self.block(body, own, names, changed),
                })
            }
            statement => out.push(statement),
        }
    }

    /// The `return` of a function returning a nested `Either`, returning its three results.
    fn returned(
        &mut self,
        value: GoExpression,
        outer: &str,
        inner: &str,
        names: &mut FxHashSet<String>,
        out: &mut Vec<GoStatement>,
    ) {
        if self.called(std::slice::from_ref(&value)).is_some_and(|(called, _)| called == outer) {
            out.push(GoStatement::Return(Some(value)));
            return;
        }
        let (kept, failure) = match value {
            GoExpression::Results(results) if results.len() == 2 => {
                let mut results = results.into_iter();
                let kept = results.next().expect("invariant violated: two results");
                (kept, results.next().expect("invariant violated: two results"))
            }
            value => {
                let (kept, failure) = self.fresh(outer, names);
                out.push(GoStatement::Define {
                    names: vec![kept.clone(), failure.clone()],
                    values: vec![value],
                });
                (identifier_expression(&kept), identifier_expression(&failure))
            }
        };
        let shape = &self.shapes[inner];
        let apart = match kept.unattributed() {
            GoExpression::Composite { fields, .. } if fields.is_empty() => {
                Some((self.zeros.zero(&shape.right), shape.no_failure()))
            }
            value => shape.construction(value).map(|(left, field)| {
                let side = if left { &shape.left } else { &shape.right };
                let field = field.unwrap_or_else(|| self.zeros.zero(side));
                match left {
                    true => (self.zeros.zero(&shape.right), shape.failed_with(field)),
                    false => (field, shape.no_failure()),
                }
            }),
        };
        let (value, inner_failure) = match apart {
            Some(apart) => apart,
            None => {
                let (value, inner_failure) = self.fresh(inner, names);
                let results = converter(self.converters, inner, Conversion::Results);
                out.push(GoStatement::Define {
                    names: vec![value.clone(), inner_failure.clone()],
                    values: vec![call(identifier_expression(&results), vec![kept])],
                });
                (identifier_expression(&value), identifier_expression(&inner_failure))
            }
        };
        out.push(GoStatement::Return(Some(GoExpression::Results(vec![
            value,
            inner_failure,
            failure,
        ]))));
    }

    /// The function returning a nested `Either` that the one value calls, with its inner type.
    fn called(&self, values: &[GoExpression]) -> Option<(String, String)> {
        let [GoExpression::Call { function, .. }] = values else {
            let [value] = values else { return None };
            let GoExpression::Attributed { value, .. } = value else { return None };
            return self.called(std::slice::from_ref(value.as_ref()));
        };
        let GoExpression::Identifier(name) = function.unattributed() else { return None };
        self.functions.get(name).cloned()
    }

    /// Names for the value and failure of an `Either` of the type.
    fn fresh(&self, shape: &str, names: &mut FxHashSet<String>) -> (String, String) {
        let value = super::inlining::fresh(&self.shapes[shape].value_name, names);
        let failure = super::inlining::fresh(&format!("err{NUMBERED}"), names);
        (value, failure)
    }

    fn joined(&mut self, shape: &str, value: &str, failure: &str) -> GoExpression {
        let from_results = converter(self.converters, shape, Conversion::FromResults);
        call(
            identifier_expression(&from_results),
            vec![identifier_expression(value), identifier_expression(failure)],
        )
    }
}

/// Drops the functions returning a nested `Either` that the code uses other than by calling them
/// and keeping both results, or returning them from another such function.
struct NestedUses<'n> {
    functions: &'n mut FxHashMap<String, (String, String)>,
    /// The top-level function whose own body the code is in, outside function literals.
    owner: Option<String>,
    changed: bool,
}

impl NestedUses<'_> {
    fn arguments(&mut self, value: &mut GoExpression) {
        match value {
            GoExpression::Attributed { value, .. } => self.arguments(value),
            GoExpression::Call { arguments, .. } => {
                arguments.iter_mut().for_each(|argument| self.expression(argument))
            }
            value => self.expression(value),
        }
    }

    fn called(&self, value: &GoExpression) -> Option<String> {
        let GoExpression::Call { function, .. } = value.unattributed() else { return None };
        let GoExpression::Identifier(name) = function.unattributed() else { return None };
        self.functions.contains_key(name).then(|| name.clone())
    }
}

impl Walk for NestedUses<'_> {
    fn statement(&mut self, statement: &mut GoStatement) {
        match statement {
            GoStatement::Define { names, values }
                if self.owner.is_some()
                    && names.len() == 2
                    && values.len() == 1
                    && self.called(&values[0]).is_some() =>
            {
                self.arguments(&mut values[0]);
            }
            GoStatement::Assign { targets, values }
                if self.owner.is_some()
                    && targets.len() == 2
                    && values.len() == 1
                    && matches!(targets[0].unattributed(), GoExpression::Identifier(_))
                    && self.called(&values[0]).is_some() =>
            {
                self.arguments(&mut values[0]);
            }
            GoStatement::Expression(value) if self.called(value).is_some() => {
                self.arguments(value);
            }
            GoStatement::Return(Some(value)) if let Some(called) = self.called(value) => {
                let outer = &self.functions[&called].0;
                let returned_as_is = self
                    .owner
                    .as_ref()
                    .and_then(|owner| self.functions.get(owner))
                    .is_some_and(|(owner_outer, _)| owner_outer == outer);
                if !returned_as_is {
                    self.functions.remove(&called);
                    self.changed = true;
                }
                self.arguments(value);
            }
            statement => go_traversal::statement(self, statement),
        }
    }

    fn expression(&mut self, value: &mut GoExpression) {
        match value {
            GoExpression::Function { .. } => {
                let owner = self.owner.take();
                go_traversal::expression(self, value);
                self.owner = owner;
            }
            GoExpression::Identifier(name) => {
                if self.functions.remove(name.as_str()).is_some() {
                    self.changed = true;
                }
            }
            value => go_traversal::expression(self, value),
        }
    }
}

/// Splits the locals of a rewritten body that still hold an `Either`, again while the value
/// locals that brings hold one themselves.
fn split_locals_again(
    body: &mut Vec<GoStatement>,
    shapes: &FxHashMap<String, EitherShape>,
    zeros: &Zeros,
    converters: &mut FxHashMap<(String, Conversion), String>,
    names: &mut FxHashSet<String>,
) {
    let none = Conventions::default();
    for _ in 0..4 {
        let mut inner = Rewrite {
            shapes,
            conventions: &none,
            callable: FxHashMap::default(),
            zeros,
            locals: FxHashSet::default(),
            converters: &mut *converters,
            names: std::mem::take(names),
            splits: FxHashMap::default(),
            reusable_failures: FxHashMap::default(),
            failure_names: FxHashSet::default(),
            failure_types: FxHashMap::default(),
        };
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

/// `EFromResults(value, err)` of two locals, with the `Either` type it builds.
fn joined_results(value: &GoExpression) -> Option<(String, String, String)> {
    let GoExpression::Call { function, arguments } = value.unattributed() else { return None };
    let GoExpression::Identifier(converter) = function.unattributed() else { return None };
    let shape = converter.strip_prefix('\u{0}')?.strip_suffix(Conversion::FromResults.suffix())?;
    let [value, failure] = arguments.as_slice() else { return None };
    let (GoExpression::Identifier(value), GoExpression::Identifier(failure)) =
        (value.unattributed(), failure.unattributed())
    else {
        return None;
    };
    Some((shape.to_string(), value.clone(), failure.clone()))
}

/// The body after a directive naming the line, when there is one.
fn with_line(line: Option<crate::syntax::SourceLine>, body: Vec<GoStatement>) -> Vec<GoStatement> {
    line.map(GoStatement::Line).into_iter().chain(body).collect()
}

/// `value, err = v, e` for the branches of a `switch` on the split `v, e` that store a `Left`'s
/// failure and a `Right`'s value unchanged: `err = e` and `value, err = v, F{}`.
fn moved_results(left: &[GoStatement], right: &[GoStatement], from: &Split) -> Option<GoStatement> {
    let only = |statements: &[GoStatement]| -> Option<(Vec<GoExpression>, Vec<GoExpression>)> {
        let mut rest =
            statements.iter().filter(|statement| !matches!(statement, GoStatement::Line(_)));
        let (Some(GoStatement::Assign { targets, values }), None) = (rest.next(), rest.next())
        else {
            return None;
        };
        Some((targets.clone(), values.clone()))
    };
    let (failure_targets, failure_values) = only(left)?;
    let (targets, values) = only(right)?;
    let is = |value: &GoExpression, name: &str| matches!(value.unattributed(), GoExpression::Identifier(found) if found == name);
    let ([failure_target], [failure], [value_target, other_failure_target], [value, nothing]) = (
        failure_targets.as_slice(),
        failure_values.as_slice(),
        targets.as_slice(),
        values.as_slice(),
    ) else {
        return None;
    };
    (is(failure, &from.failure)
        && is(value, &from.value)
        && is_no_failure(nothing)
        && failure_target == other_failure_target)
        .then(|| GoStatement::Assign {
            targets: vec![value_target.clone(), failure_target.clone()],
            values: vec![identifier_expression(&from.value), identifier_expression(&from.failure)],
        })
}

/// The locals `a, err := f()` binds, whose reads dropping an unread split local can remove.
fn call_results(body: &mut Vec<GoStatement>) -> FxHashSet<String> {
    let mut results = FxHashSet::default();
    every_block(body, &mut |block| {
        for statement in block.iter() {
            if let GoStatement::Define { names, values } = statement
                && names.len() > 1
                && values.len() == 1
            {
                results.extend(names.iter().filter(|name| *name != "_").cloned());
            }
        }
    });
    results
}

/// `a, b := f(); c, d = a, b` as `c, d = f()`, when nothing else reads `a` and `b`.
fn forward_moves(body: &mut Vec<GoStatement>, names: &FxHashSet<String>) {
    let mut uses: FxHashMap<String, usize> = FxHashMap::default();
    crate::syntax::statements_names(body, &mut |name| {
        if let Name::Reference(name) | Name::Written(name) = name {
            *uses.entry(name.clone()).or_default() += 1;
        }
    });
    every_block(body, &mut |block| {
        let mut index = 0;
        while index < block.len() {
            let next =
                (index + 1..block.len()).find(|&at| !matches!(block[at], GoStatement::Line(_)));
            if let Some(next) = next
                && let GoStatement::Define { names: defined, values: called } = &block[index]
                && let [call] = called.as_slice()
                && defined.len() > 1
                && defined.iter().all(|name| names.contains(name) && uses.get(name) == Some(&1))
                && let GoStatement::Assign { targets, values } = &block[next]
                && values.len() == defined.len()
                && values.iter().zip(defined).all(|(value, name)| {
                    matches!(value, GoExpression::Identifier(found) if found == name)
                })
            {
                let moved = GoStatement::Assign { targets: targets.clone(), values: vec![call.clone()] };
                block[index] = moved;
                block.remove(next);
            }
            index += 1;
        }
    });
}

/// Whether a `break` in the statements leaves the `switch` around them.
fn breaks_out(statements: &[GoStatement]) -> bool {
    statements.iter().any(|statement| match statement {
        GoStatement::Break => true,
        GoStatement::If { then, otherwise, .. } => breaks_out(then) || breaks_out(otherwise),
        GoStatement::IfAssert { then, .. } => breaks_out(then),
        _ => false,
    })
}

/// Whether control cannot fall out of the end of the statements.
fn terminates(statements: &[GoStatement]) -> bool {
    match statements.iter().rev().find(|statement| !matches!(statement, GoStatement::Line(_))) {
        Some(
            GoStatement::Return(_)
            | GoStatement::Continue
            | GoStatement::Break
            | GoStatement::BreakTo(_),
        ) => true,
        Some(statement) if statement.is_panic() => true,
        Some(GoStatement::If { then, otherwise, .. }) => terminates(then) && terminates(otherwise),
        Some(GoStatement::Switch { cases, default: Some(default), .. }) => {
            cases.iter().all(|case| terminates(&case.body)) && terminates(&default.body)
        }
        _ => false,
    }
}

/// `if err != nil { return … } else { rest }` as `if err != nil { return … }` followed by the
/// rest, when the rest's locals clash with nothing around the `if`.
fn return_early(block: &mut Vec<GoStatement>, failures: &FxHashSet<String>) {
    let mut index = 0;
    while index < block.len() {
        let GoStatement::If { condition, then, otherwise } = &block[index] else {
            index += 1;
            continue;
        };
        let tests_failure = matches!(tested_failure(condition, failures), Some((_, true)));
        if !tests_failure || otherwise.is_empty() || !terminates(then) {
            index += 1;
            continue;
        }
        let bound = top_level_binders(otherwise);
        let bound: Vec<String> = bound.into_iter().collect();
        if mentions(&block[..index], &bound) || mentions(&block[index + 1..], &bound) {
            index += 1;
            continue;
        }
        let GoStatement::If { otherwise, .. } = &mut block[index] else { unreachable!() };
        let rest = std::mem::take(otherwise);
        block.splice(index + 1..index + 1, rest);
        index += 1;
    }
}

fn top_level_binders(statements: &[GoStatement]) -> FxHashSet<String> {
    let mut bound = FxHashSet::default();
    for statement in statements {
        match statement {
            GoStatement::Define { names, .. } => bound.extend(names.iter().cloned()),
            GoStatement::Variable { name, .. } => {
                bound.insert(name.clone());
            }
            _ => {}
        }
    }
    bound.remove("_");
    bound
}

/// Names a split value after the local it is copied into, `b` in `value, err := f(); b :=
/// value`, when that copy is all that reads it.
fn adopt_copies(
    body: &mut Vec<GoStatement>,
    values: &FxHashSet<String>,
) -> FxHashMap<String, String> {
    let mut binders: FxHashMap<String, usize> = FxHashMap::default();
    let mut uses: FxHashMap<String, usize> = FxHashMap::default();
    let mut written: FxHashSet<String> = FxHashSet::default();
    crate::syntax::statements_names(body, &mut |name| match name {
        Name::Binder(name) => *binders.entry(name.clone()).or_default() += 1,
        Name::Reference(name) => *uses.entry(name.clone()).or_default() += 1,
        Name::Written(name) => {
            *uses.entry(name.clone()).or_default() += 1;
            written.insert(name.clone());
        }
    });
    let mut renamed: FxHashMap<String, String> = FxHashMap::default();
    every_block(body, &mut |block| {
        block.retain(|statement| {
            if let GoStatement::Define { names, values: copied } = statement
                && let ([copy], [GoExpression::Identifier(value)]) =
                    (names.as_slice(), copied.as_slice())
                && values.contains(value)
                && uses.get(value) == Some(&1)
                && binders.get(copy) == Some(&1)
                && binders.get(value) == Some(&1)
                && !written.contains(copy)
                && !written.contains(value)
                && !renamed.contains_key(value)
            {
                renamed.insert(value.clone(), copy.clone());
                return false;
            }
            true
        });
    });
    if !renamed.is_empty() {
        crate::syntax::statements_names(body, &mut |name| {
            let (Name::Reference(name) | Name::Written(name) | Name::Binder(name)) = name;
            if let Some(copy) = renamed.get(name.as_str()) {
                *name = copy.clone();
            }
        });
    }
    renamed
}

/// Visits every block of the statements, function literals' bodies included, outer ones first.
fn every_block(body: &mut Vec<GoStatement>, visit: &mut impl FnMut(&mut Vec<GoStatement>)) {
    struct Blocks<'v, F>(&'v mut F);
    impl<F: FnMut(&mut Vec<GoStatement>)> Walk for Blocks<'_, F> {
        fn block(&mut self, body: &mut Vec<GoStatement>) {
            (self.0)(body);
            body.iter_mut().for_each(|statement| self.statement(statement));
        }
    }
    Blocks(visit).block(body);
}

/// How often each of the names is read, not counting assignments to it.
fn reads(body: &mut [GoStatement], names: &FxHashSet<String>) -> FxHashMap<String, usize> {
    let mut reads = FxHashMap::default();
    crate::syntax::statements_names(body, &mut |name| {
        if let Name::Reference(name) = name
            && names.contains(name.as_str())
        {
            *reads.entry(name.clone()).or_default() += 1;
        }
    });
    reads
}

/// Writes `_` for the split locals nothing reads, and leaves out their declarations.
fn drop_unread(
    body: &mut Vec<GoStatement>,
    names: &FxHashSet<String>,
    reads: &FxHashMap<String, usize>,
) {
    let unread = |name: &str| names.contains(name) && !reads.contains_key(name);
    every_block(body, &mut |block| {
        block.retain(|statement| !matches!(statement, GoStatement::Variable { name, value: None, .. } if unread(name)));
        let mut kept = Vec::with_capacity(block.len());
        for mut statement in std::mem::take(block) {
            if let GoStatement::Variable { name, value: Some(value), .. } = &statement
                && unread(name)
            {
                if !is_plain(value) {
                    kept.push(GoStatement::Assign {
                        targets: vec![identifier_expression("_")],
                        values: vec![value.clone()],
                    });
                }
                continue;
            }
            let ignored = match &mut statement {
                GoStatement::Define { names, values } => {
                    for name in names.iter_mut() {
                        if unread(name) {
                            *name = "_".into();
                        }
                    }
                    names.iter().all(|name| name == "_") && values.len() == 1
                }
                GoStatement::Assign { targets, values } => {
                    for target in targets.iter_mut() {
                        if let GoExpression::Identifier(name) = target
                            && unread(name)
                        {
                            *name = "_".into();
                        }
                    }
                    let ignored = |target: &GoExpression| matches!(target, GoExpression::Identifier(name) if name == "_");
                    if values.len() == targets.len() && values.len() > 1 {
                        let pairs: Vec<(GoExpression, GoExpression)> = std::mem::take(targets)
                            .into_iter()
                            .zip(std::mem::take(values))
                            .filter(|(target, value)| !(ignored(target) && is_plain(value)))
                            .collect();
                        (*targets, *values) = pairs.into_iter().unzip();
                        if targets.is_empty() {
                            continue;
                        }
                    }
                    targets.iter().all(ignored) && values.len() == 1
                }
                _ => false,
            };
            let (
                true,
                GoStatement::Define { mut values, .. } | GoStatement::Assign { mut values, .. },
            ) = (ignored, statement.clone())
            else {
                kept.push(statement);
                continue;
            };
            let value = values.pop().expect("invariant violated: one value");
            match value.unattributed() {
                GoExpression::Call { .. } => kept.push(GoStatement::Expression(value)),
                _ if is_plain(&value) => {}
                _ => kept.push(GoStatement::Assign {
                    targets: vec![identifier_expression("_")],
                    values: vec![value],
                }),
            }
        }
        *block = kept;
    });
}

/// A value whose evaluation does nothing: a name, a literal, or a struct of those.
fn is_plain(value: &GoExpression) -> bool {
    match value.unattributed() {
        GoExpression::Identifier(_)
        | GoExpression::Qualified { .. }
        | GoExpression::Integer(_)
        | GoExpression::Float(_)
        | GoExpression::String(_)
        | GoExpression::Boolean(_)
        | GoExpression::Rune(_)
        | GoExpression::Function { .. } => true,
        GoExpression::Composite { fields, .. } => fields.iter().all(|(_, field)| is_plain(field)),
        _ => false,
    }
}

/// Names a failure local after an earlier one of its type in the same block that nothing reads
/// from there on, as Go code reuses `err`.
fn reuse_failure_names(body: &mut Vec<GoStatement>, reusable: &FxHashMap<String, String>) {
    let captured = captured(body);
    let mut renamed: FxHashMap<String, String> = FxHashMap::default();
    every_block(body, &mut |block| {
        let mut current: FxHashMap<&String, Vec<String>> = FxHashMap::default();
        for index in 0..block.len() {
            let GoStatement::Define { names, .. } = &block[index] else { continue };
            for name in names.clone() {
                let Some(kind) = reusable.get(&name) else { continue };
                if captured.contains(&name) {
                    continue;
                }
                match current.get_mut(kind) {
                    Some(group) if !mentions(&block[index + 1..], group) => {
                        renamed.insert(name.clone(), group[0].clone());
                        group.push(name);
                    }
                    _ => {
                        current.insert(kind, vec![name]);
                    }
                }
            }
        }
    });
    if renamed.is_empty() {
        return;
    }
    crate::syntax::statements_names(body, &mut |name| {
        let (Name::Reference(name) | Name::Written(name) | Name::Binder(name)) = name;
        if let Some(earlier) = renamed.get(name.as_str()) {
            *name = earlier.clone();
        }
    });
}

/// Whether the statements mention one of the names.
fn mentions(statements: &[GoStatement], wanted: &[String]) -> bool {
    let mut statements = statements.to_vec();
    let mut found = false;
    crate::syntax::statements_names(&mut statements, &mut |name| {
        let (Name::Reference(name) | Name::Written(name) | Name::Binder(name)) = name;
        found |= wanted.contains(name);
    });
    found
}

/// `_, err = f()` where `err` is already declared in the block, since `:=` declares something.
fn declare_each_once(body: &mut Vec<GoStatement>, names: &FxHashSet<String>) {
    every_block(body, &mut |block| {
        let mut declared: FxHashSet<String> = FxHashSet::default();
        for statement in block.iter_mut() {
            match statement {
                GoStatement::Define { names: defined, values } => {
                    let new = defined.iter().any(|name| name != "_" && !declared.contains(name));
                    if !new && defined.iter().any(|name| names.contains(name)) {
                        *statement = GoStatement::Assign {
                            targets: defined
                                .iter()
                                .map(|name| identifier_expression(name))
                                .collect(),
                            values: std::mem::take(values),
                        };
                        continue;
                    }
                    declared.extend(defined.iter().filter(|name| *name != "_").cloned());
                }
                GoStatement::Variable { name, .. } => {
                    declared.insert(name.clone());
                }
                _ => {}
            }
        }
    });
}

/// The locals of a function body that function literals in it refer to but do not bind.
fn captured(body: &mut [GoStatement]) -> FxHashSet<String> {
    struct Literals(FxHashSet<String>);
    impl Walk for Literals {
        fn expression(&mut self, value: &mut GoExpression) {
            if let GoExpression::Function { parameters, body, .. } = value {
                let mut bound: FxHashSet<String> =
                    parameters.iter().map(|(parameter, _)| parameter.clone()).collect();
                let mut referred = FxHashSet::default();
                crate::syntax::statements_names(body, &mut |name| match name {
                    Name::Binder(name) => {
                        bound.insert(name.clone());
                    }
                    Name::Reference(name) | Name::Written(name) => {
                        referred.insert(name.clone());
                    }
                });
                self.0.extend(referred.into_iter().filter(|name| !bound.contains(name)));
            }
            go_traversal::expression(self, value);
        }
    }
    let mut literals = Literals(FxHashSet::default());
    body.iter_mut().for_each(|statement| literals.statement(statement));
    literals.0
}

/// The survey of a function body for the locals that can become two.
struct Survey<'s> {
    shapes: &'s FxHashMap<String, EitherShape>,
    callable: &'s FxHashMap<String, String>,
    parameters: &'s FxHashMap<String, FxHashMap<usize, String>>,
    split_parameters: &'s FxHashMap<String, FxHashMap<usize, String>>,
    binders: &'s FxHashMap<String, usize>,
    candidates: FxHashMap<String, Candidate>,
    /// What the code knows about the candidates where it is.
    facts: Vec<Fact>,
}

/// That a candidate holds a `Left` or a `Right` where the code is.
struct Fact {
    local: String,
    left: bool,
    /// Whether an `if` that returned before tells.
    early: bool,
    /// Whether a statement since assigned the candidate, so that it no longer holds.
    stale: bool,
}

/// Marks a read of the field both sides of an `Either Int Int` share as one of the `Left` or the
/// `Right`, for the rewrite.
const SIDE_MARK: char = '\u{1}';

fn marked_side(field: &str, left: bool) -> String {
    format!("{SIDE_MARK}{}{field}", if left { 'L' } else { 'R' })
}

/// The side a marked field read reads, `true` for the `Left`, and the field.
fn read_side(field: &str) -> Option<(bool, &str)> {
    let rest = field.strip_prefix(SIDE_MARK)?;
    Some((rest.starts_with('L'), &rest[1..]))
}

/// Unmarks the shared field reads of the locals that stay `Either` structs.
fn unmark_sides(body: &mut [GoStatement], kept: &impl Fn(&str) -> bool) {
    for statement in body.iter_mut() {
        go_traversal::each_expression_in_statement(statement, |expression| {
            if let GoExpression::Field { value, name } = expression
                && let Some((_, field)) = read_side(name)
                && let GoExpression::Identifier(local) = value.unattributed()
                && !kept(local)
            {
                *name = field.to_string();
            }
        });
    }
}

/// The branches of one statement: each starts from what held before it, and after the statement
/// a fact holds only if no branch assigned its candidate.
struct Branches {
    before: Vec<bool>,
    after: Vec<bool>,
}

impl Branches {
    fn start(survey: &Survey<'_>) -> Branches {
        let before: Vec<bool> = survey.facts.iter().map(|fact| fact.stale).collect();
        Branches { after: before.clone(), before }
    }

    fn enter(&self, survey: &mut Survey<'_>) {
        for (fact, stale) in survey.facts.iter_mut().zip(&self.before) {
            fact.stale = *stale;
        }
    }

    fn leave(&mut self, survey: &Survey<'_>) {
        for (stale, fact) in self.after.iter_mut().zip(&survey.facts) {
            *stale |= fact.stale;
        }
    }

    fn end(self, survey: &mut Survey<'_>) {
        for (fact, stale) in survey.facts.iter_mut().zip(&self.after) {
            fact.stale = *stale;
        }
    }
}

/// The locals the statements assign to, in loops and branches too.
fn assigned_in(body: &mut [GoStatement]) -> FxHashSet<String> {
    let mut assigned = FxHashSet::default();
    crate::syntax::statements_names(body, &mut |name| {
        if let Name::Written(name) = name {
            assigned.insert(name.clone());
        }
    });
    assigned
}

impl Survey<'_> {
    fn block(&mut self, statements: &mut [GoStatement], own: Option<&str>) {
        let known = self.facts.len();
        for statement in statements {
            self.statement(statement, own);
            if let GoStatement::If { condition, then, otherwise } = statement
                && otherwise.is_empty()
                && terminates(then)
                && let Some((local, left)) = self.tag_test(condition)
            {
                self.facts.push(Fact { local, left: !left, early: true, stale: false });
            }
        }
        self.facts.truncate(known);
    }

    fn candidate_target(&self, target: &GoExpression) -> Option<String> {
        match target.unattributed() {
            GoExpression::Identifier(local) if self.candidates.contains_key(local) => {
                Some(local.clone())
            }
            _ => None,
        }
    }

    /// The tag test a condition starts with, `local.Tag == tag && …`, which holds wherever the
    /// whole condition does.
    fn leading_tag_test(&self, condition: &GoExpression) -> Option<(String, bool)> {
        match condition.unattributed() {
            GoExpression::Binary { operator: "&&", left, .. } => self.leading_tag_test(left),
            condition => self.tag_test(condition),
        }
    }

    /// Forgets what the code knew about the candidate.
    fn assigned(&mut self, local: &str) {
        for fact in self.facts.iter_mut().filter(|fact| fact.local == local) {
            fact.stale = true;
        }
    }

    /// The `Either` type of a value a local is defined as, when it can be split.
    fn source_shape(&self, value: &GoExpression) -> Option<String> {
        if let Some((shape, _, _)) = joined_results(value) {
            return self.shapes.contains_key(&shape).then_some(shape);
        }
        match value.unattributed() {
            GoExpression::Call { function, .. } => match function.unattributed() {
                GoExpression::Identifier(name) => self.callable.get(name).cloned(),
                _ => None,
            },
            GoExpression::Composite { type_: GoType::Named(name), .. }
                if self.shapes.contains_key(name) =>
            {
                Some(name.clone())
            }
            _ => None,
        }
    }

    fn consider(&mut self, local: &str, shape: String, joins: bool) {
        if self.binders.get(local) != Some(&1) {
            return;
        }
        self.candidates.insert(
            local.to_string(),
            Candidate {
                shape,
                calls: 0,
                reassigned: false,
                read_after_early_return: false,
                joins,
                escapes: false,
                results: None,
            },
        );
    }

    /// The body of a function literal that returns two results.
    fn converted_literal(&mut self, literal: &mut GoExpression, shape: &str) {
        match literal {
            GoExpression::Attributed { value, .. } => self.converted_literal(value, shape),
            GoExpression::Function { body, .. } => self.block(body, Some(shape)),
            value => self.expression(value),
        }
    }

    /// A value stored into a candidate: a fallible call or a construction of its type.
    fn source(&mut self, local: &str, value: &mut GoExpression) {
        let Some(candidate) = self.candidates.get(local) else {
            self.expression(value);
            return;
        };
        let shape = candidate.shape.clone();
        let is_call = self.source_shape(value).as_ref() == Some(&shape)
            && matches!(value.unattributed(), GoExpression::Call { .. });
        let construction = match self.source_shape(value).as_ref() == Some(&shape) {
            true => self.shapes[&shape].construction(value),
            false => None,
        };
        let is_construction = construction.is_some();
        let joined = joined_results(value);
        let candidate = self.candidates.get_mut(local).expect("invariant violated: a candidate");
        if is_call {
            candidate.calls += 1;
            candidate.results = joined.map(|(_, value, failure)| (value, failure));
            self.expression(value);
            return;
        } else if !is_construction {
            candidate.escapes = true;
            self.expression(value);
            return;
        }
        match value {
            GoExpression::Attributed { value, .. } => self.children(value),
            value => self.children(value),
        }
    }

    fn children(&mut self, value: &mut GoExpression) {
        struct Children<'a, 's>(&'a mut Survey<'s>);
        impl Walk for Children<'_, '_> {
            fn expression(&mut self, value: &mut GoExpression) {
                self.0.expression(value);
            }
            fn block(&mut self, _: &mut Vec<GoStatement>) {}
        }
        go_traversal::expression(&mut Children(self), value);
    }

    fn statement(&mut self, statement: &mut GoStatement, own: Option<&str>) {
        match statement {
            GoStatement::Define { names, values }
                if let ([local], [value]) = (names.as_slice(), values.as_slice())
                    && self.callable.contains_key(local)
                    && matches!(value.unattributed(), GoExpression::Function { .. }) =>
            {
                let shape = self.callable[&names[0]].clone();
                self.converted_literal(&mut values[0], &shape);
            }
            GoStatement::Define { names, values } if names.len() == 1 && values.len() == 1 => {
                if let Some(shape) = self.source_shape(&values[0]) {
                    self.consider(&names[0], shape, false);
                }
                let name = names[0].clone();
                self.source(&name, &mut values[0]);
            }
            GoStatement::Variable { name, type_, value } => {
                if let GoType::Named(shape) = type_
                    && self.shapes.contains_key(shape)
                {
                    self.consider(name, shape.clone(), true);
                }
                let name = name.clone();
                if let Some(value) = value {
                    self.source(&name, value);
                }
            }
            GoStatement::Assign { targets, values }
                if targets.len() == 1
                    && values.len() == 1
                    && let GoExpression::Identifier(target) = targets[0].unattributed()
                    && self.candidates.contains_key(target) =>
            {
                let target = target.clone();
                if let Some(candidate) = self.candidates.get_mut(&target) {
                    candidate.reassigned = true;
                }
                self.source(&target, &mut values[0]);
                self.assigned(&target);
            }
            GoStatement::Assign { targets, values }
                if targets.len() == values.len()
                    && targets.len() > 1
                    && targets.iter().any(|target| self.candidate_target(target).is_some()) =>
            {
                let mut stored = vec![];
                for (target, value) in targets.iter_mut().zip(values.iter_mut()) {
                    let Some(local) = self.candidate_target(target) else {
                        self.expression(target);
                        self.expression(value);
                        continue;
                    };
                    let shape = self.candidates[&local].shape.clone();
                    let constructs = self.shapes[&shape].construction(value).is_some();
                    let candidate =
                        self.candidates.get_mut(&local).expect("invariant violated: a candidate");
                    candidate.reassigned = true;
                    candidate.escapes |= !constructs;
                    self.source(&local, value);
                    stored.push(local);
                }
                for local in stored {
                    self.assigned(&local);
                }
            }
            GoStatement::Return(Some(value))
                if let GoExpression::Identifier(local) = value.unattributed()
                    && let Some(candidate) = self.candidates.get_mut(local) =>
            {
                if own != Some(candidate.shape.as_str()) {
                    candidate.escapes = true;
                }
            }
            GoStatement::Switch { value: Some(scrutinee), cases, default }
                if let Some(local) = self.tagged(scrutinee) =>
            {
                let shape = &self.shapes[&self.candidates[&local].shape];
                let sides: Vec<Option<bool>> = cases
                    .iter()
                    .map(|case| {
                        let sides: Vec<Option<bool>> =
                            case.values.iter().map(|value| shape.is_left_tag(value)).collect();
                        match sides.as_slice() {
                            [side] => *side,
                            _ => None,
                        }
                    })
                    .collect();
                let undecided = sides.iter().any(Option::is_none)
                    || cases.len() + usize::from(default.is_some()) != 2
                    || (default.is_none() && sides.iter().all(|side| *side == sides[0]));
                if undecided && let Some(candidate) = self.candidates.get_mut(&local) {
                    candidate.escapes = true;
                }
                let mut seen_left = false;
                let mut branches = Branches::start(self);
                for (case, side) in cases.iter_mut().zip(&sides) {
                    let side = side.unwrap_or(false);
                    seen_left |= side;
                    branches.enter(self);
                    self.with_fact(&local, side, |survey| survey.block(&mut case.body, own));
                    branches.leave(self);
                }
                if let Some(default) = default {
                    branches.enter(self);
                    self.with_fact(&local, !seen_left, |survey| {
                        survey.block(&mut default.body, own)
                    });
                    branches.leave(self);
                }
                branches.end(self);
            }
            GoStatement::If { condition, then, otherwise }
                if let Some((local, left)) = self.tag_test(condition) =>
            {
                let mut branches = Branches::start(self);
                branches.enter(self);
                self.with_fact(&local, left, |survey| survey.block(then, own));
                branches.leave(self);
                branches.enter(self);
                self.with_fact(&local, !left, |survey| survey.block(otherwise, own));
                branches.leave(self);
                branches.end(self);
            }
            GoStatement::If { condition, then, otherwise }
                if let Some((local, left)) = self.leading_tag_test(condition) =>
            {
                self.expression(condition);
                let mut branches = Branches::start(self);
                branches.enter(self);
                self.with_fact(&local, left, |survey| survey.block(then, own));
                branches.leave(self);
                branches.enter(self);
                self.block(otherwise, own);
                branches.leave(self);
                branches.end(self);
            }
            statement => {
                struct Inner<'a, 's> {
                    survey: &'a mut Survey<'s>,
                    own: Option<&'a str>,
                    branches: Branches,
                }
                impl Walk for Inner<'_, '_> {
                    fn expression(&mut self, value: &mut GoExpression) {
                        self.survey.expression(value);
                    }
                    fn block(&mut self, body: &mut Vec<GoStatement>) {
                        self.branches.enter(self.survey);
                        self.survey.block(body, self.own);
                        self.branches.leave(self.survey);
                    }
                }
                if let GoStatement::Loop(body)
                | GoStatement::LabeledLoop { body, .. }
                | GoStatement::Range { body, .. }
                | GoStatement::Counting { body, .. }
                | GoStatement::CountingDown { body, .. } = &mut *statement
                {
                    for local in assigned_in(body) {
                        self.assigned(&local);
                    }
                }
                let branches = Branches::start(self);
                let mut inner = Inner { survey: self, own, branches };
                go_traversal::statement(&mut inner, statement);
                let Inner { branches, .. } = inner;
                branches.end(self);
            }
        }
    }

    fn with_fact(&mut self, local: &str, left: bool, visit: impl FnOnce(&mut Self)) {
        self.facts.push(Fact { local: local.to_string(), left, early: false, stale: false });
        visit(self);
        self.facts.pop();
    }

    /// Whether the local holds a `Left` (`true`) or a `Right` where the code is, and whether an
    /// early return tells.
    fn known_side(&self, local: &str) -> Option<(bool, bool)> {
        let fact = self.facts.iter().rev().find(|fact| fact.local == local)?;
        (!fact.stale).then_some((fact.left, fact.early))
    }

    /// The candidate whose tag the value reads.
    fn tagged(&self, value: &GoExpression) -> Option<String> {
        let GoExpression::Field { value, name } = value.unattributed() else { return None };
        let GoExpression::Identifier(local) = value.unattributed() else { return None };
        (name == "Tag" && self.candidates.contains_key(local)).then(|| local.clone())
    }

    /// `local.Tag == tag` of a candidate, with whether it holds when the local is a `Left`.
    fn tag_test(&self, condition: &GoExpression) -> Option<(String, bool)> {
        let GoExpression::Binary { operator, left, right } = condition.unattributed() else {
            return None;
        };
        if !matches!(*operator, "==" | "!=") {
            return None;
        }
        let (local, tag) = match self.tagged(left) {
            Some(local) => (local, right),
            None => (self.tagged(right)?, left),
        };
        let is_left = self.shapes[&self.candidates[&local].shape].is_left_tag(tag)?;
        Some((local, (*operator == "==") == is_left))
    }

    fn expression(&mut self, value: &mut GoExpression) {
        match value {
            GoExpression::Identifier(name) => {
                if let Some(candidate) = self.candidates.get_mut(name.as_str()) {
                    candidate.escapes = true;
                }
            }
            GoExpression::Field { value: inner, name }
                if let GoExpression::Identifier(local) = inner.unattributed()
                    && self.candidates.contains_key(local) =>
            {
                let local = local.clone();
                let shape = &self.shapes[&self.candidates[&local].shape];
                let known = self.known_side(&local);
                let shared = shape.shares_field() && *name == shape.left_field;
                let left_read = *name == shape.left_field;
                let right_read = *name == shape.right_field;
                let Some(candidate) = self.candidates.get_mut(&local) else { return };
                match known {
                    Some((true, early)) if left_read => {
                        candidate.read_after_early_return |= early;
                        if shared {
                            *name = marked_side(name, true);
                        }
                    }
                    Some((false, _)) if right_read && shared => *name = marked_side(name, false),
                    _ if right_read && !shared => {}
                    _ => candidate.escapes = true,
                }
            }
            GoExpression::Function { body, .. } => self.block(body, None),
            GoExpression::Call { function, arguments }
                if let GoExpression::Identifier(head) = function.unattributed()
                    && (self.parameters.contains_key(head)
                        || self.split_parameters.contains_key(head)) =>
            {
                let empty = FxHashMap::default();
                let slots = self.parameters.get(head).unwrap_or(&empty);
                let split = self.split_parameters.get(head).unwrap_or(&empty);
                for (index, argument) in arguments.iter_mut().enumerate() {
                    match (slots.get(&index), split.get(&index)) {
                        (Some(shape), _) => self.converted_literal(argument, shape),
                        (None, Some(shape)) => match argument {
                            GoExpression::Identifier(local)
                                if self
                                    .candidates
                                    .get(local.as_str())
                                    .is_some_and(|candidate| candidate.shape == *shape) => {}
                            GoExpression::Attributed { value, .. } => self.children(value),
                            argument => self.children(argument),
                        },
                        (None, None) => self.expression(argument),
                    }
                }
            }
            GoExpression::Binary { operator: "&&", left, right }
                if let Some((local, side)) = self.leading_tag_test(left) =>
            {
                self.expression(left);
                self.with_fact(&local, side, |survey| survey.expression(right));
            }
            value if self.tag_test(value).is_some() => {}
            value => self.children(value),
        }
    }
}
