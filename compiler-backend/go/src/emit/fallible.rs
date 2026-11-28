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
//! Function values do the same where only generated code makes and calls them, as `values`
//! says. Foreign functions and the function types they fix go on passing `Either` structs.
//! Where one meets the other, a function for each `Either` type converts:
//! `EitherTFromResults(f(x))` builds the struct from a call's results, and `EitherTResults(e)`
//! takes a struct apart for a `return`.

mod conventions;
mod nested;
mod rewrite;
mod survey;
mod syntax;
mod values;
mod variants;
mod zeros;

use rustc_hash::{FxHashMap, FxHashSet};
pub(super) use values::lower_type;

use super::packages::Spelling;
use super::{DataKind, Emitter, binary, identifier_expression};
use crate::error::GoResult;
use crate::go_traversal::{self};
use crate::monotype::DataType;
use crate::syntax::{GoDeclaration, GoExpression, GoStatement, GoType, Reference, StructField};
use conventions::Conventions;
use nested::NestedResults;
use rewrite::Rewrite;
use zeros::Zeros;

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
        let mut shapes = self.either_shapes()?;
        if shapes.is_empty() {
            return Ok(());
        }
        let support = SupportFunctions::take(&mut self.type_declarations, declarations);
        let variants = variants::Variants::provided(self.foreign_packages);
        self.lowered_function_types = values::lower_function_values(
            declarations,
            &mut self.type_declarations,
            &shapes,
            self.foreign_packages,
            &variants,
        );
        let lowered = !self.lowered_function_types.is_empty();
        for shape in shapes.values_mut() {
            lower_type(&mut shape.left, &self.lowered_function_types);
            lower_type(&mut shape.right, &self.lowered_function_types);
        }
        let called = variants.call(declarations, &shapes);
        let marks: FxHashMap<String, String> = match lowered || called {
            true => shapes
                .keys()
                .map(|shape| (format!("{}{shape}", values::CALL_MARK), shape.clone()))
                .collect(),
            false => FxHashMap::default(),
        };
        let conventions = Conventions::choose(declarations, &shapes, marks, &support.names);
        let zeros = Zeros::new(&self.type_declarations);
        let mut converters: FxHashMap<(String, Conversion), String> = FxHashMap::default();
        for (position, declaration) in declarations.iter_mut().enumerate() {
            let mut rewrite = Rewrite::new(
                &shapes,
                &conventions,
                conventions.callable(position, declaration),
                &zeros,
                &mut converters,
                declaration.all_names(),
            );
            rewrite.declaration(declaration);
        }
        NestedResults::new(&shapes, &zeros, &mut converters).flatten(declarations, &conventions);
        values::unmark(declarations);
        let mut wanted: Vec<((String, Conversion), String)> = converters.into_iter().collect();
        wanted.sort_by(|left, right| left.1.cmp(&right.1));
        for ((shape, conversion), placeholder) in wanted {
            let shape = &shapes[&shape];
            let name = self.declare_converter(shape, conversion, &zeros, declarations)?;
            rename_global(declarations, &placeholder, &name);
        }
        support.restore(&mut self.type_declarations, declarations);
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
        for declaration in declarations.iter_mut().chain(self.type_declarations.iter_mut()) {
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

    /// A converter's parameter, named so that no global it would shadow is renamed in its body.
    pub(super) fn parameter_name(&self, base: &str) -> String {
        crate::naming::numbered(base, |name| self.global_names.contains(name))
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
                let value_name = self.parameter_name("value");
                let err_name = self.parameter_name("err");
                let value = identifier_expression(&value_name);
                let left = GoExpression::Field {
                    value: Box::new(identifier_expression(&err_name)),
                    name: LEFT.into(),
                };
                GoDeclaration::Function {
                    name: name.clone(),
                    parameters: vec![
                        (value_name, shape.right.clone()),
                        (err_name.clone(), shape.failure_type()),
                    ],
                    result: Some(either),
                    body: vec![
                        GoStatement::If {
                            condition: failure_test_of(&err_name, true),
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
                let either_name = self.parameter_name("either");
                let either_value = identifier_expression(&either_name);
                let side = |field: &str| GoExpression::Field {
                    value: Box::new(either_value.clone()),
                    name: field.to_string(),
                };
                let is_left = binary("==", side("Tag"), identifier_expression(&shape.left_tag));
                GoDeclaration::Function {
                    name: name.clone(),
                    parameters: vec![(either_name, either)],
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
                let either_name = self.parameter_name("either");
                let either_value = identifier_expression(&either_name);
                let side = |field: &str| GoExpression::Field {
                    value: Box::new(either_value.clone()),
                    name: field.to_string(),
                };
                let is_left = binary("==", side("Tag"), identifier_expression(&shape.left_tag));
                GoDeclaration::Function {
                    name: name.clone(),
                    parameters: vec![(either_name, either)],
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

struct SupportFunctions {
    names: FxHashSet<String>,
    positions: Vec<usize>,
}

impl SupportFunctions {
    fn take(
        type_declarations: &mut Vec<GoDeclaration>,
        declarations: &mut Vec<GoDeclaration>,
    ) -> SupportFunctions {
        let mut names = FxHashSet::default();
        let mut positions = vec![];
        let mut kept = vec![];
        for (position, declaration) in std::mem::take(type_declarations).into_iter().enumerate() {
            match &declaration {
                GoDeclaration::Function { name, .. } => {
                    names.insert(name.clone());
                    positions.push(position);
                    declarations.push(declaration);
                }
                _ => kept.push(declaration),
            }
        }
        *type_declarations = kept;
        SupportFunctions { names, positions }
    }

    fn restore(
        self,
        type_declarations: &mut Vec<GoDeclaration>,
        declarations: &mut Vec<GoDeclaration>,
    ) {
        let is_support = |declaration: &GoDeclaration| match declaration {
            GoDeclaration::Function { name, .. } => self.names.contains(name),
            _ => false,
        };
        let (support, program): (Vec<GoDeclaration>, Vec<GoDeclaration>) =
            std::mem::take(declarations).into_iter().partition(is_support);
        *declarations = program;
        let mut support = self.positions.iter().copied().zip(support).peekable();
        let mut restored = Vec::with_capacity(type_declarations.len() + self.positions.len());
        for declaration in std::mem::take(type_declarations) {
            while let Some((_, function)) =
                support.next_if(|(position, _)| *position == restored.len())
            {
                restored.push(function);
            }
            restored.push(declaration);
        }
        restored.extend(support.map(|(_, function)| function));
        *type_declarations = restored;
    }
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
