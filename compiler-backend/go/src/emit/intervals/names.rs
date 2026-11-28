use rustc_hash::{FxHashMap, FxHashSet};

use super::program::FunctionTable;
use super::syntax::{each_subexpression, is_bounds_test, is_test};
use super::written_field;
use crate::emit::{aliases, headers};
use crate::go_traversal::{self, Walk};
use crate::syntax::{GoBuiltin, GoExpression, GoPackage, GoStatement, GoType, GoUnaryOperator};

#[derive(Clone, Copy, PartialEq, Debug)]
pub(super) enum Shape {
    /// A slice or a string: its length changes only when the local is assigned.
    Fixed,
    /// A pointer to a slice, whose length a push changes.
    Pointer,
}

pub(super) fn shape_of_type(type_: &GoType) -> Option<Shape> {
    match type_ {
        GoType::Slice(_) | GoType::String => Some(Shape::Fixed),
        GoType::Pointer(inner) if matches!(**inner, GoType::Slice(_)) => Some(Shape::Pointer),
        _ => None,
    }
}

/// Facts about a function's names that hold wherever they are bound.
#[derive(Default)]
pub(super) struct Names {
    /// Assigned by a closure or addressed: no constraints.
    pub(super) untracked: FxHashSet<String>,
    /// Assigned somewhere: a condition bound to such a name is not remembered.
    pub(super) assigned: FxHashSet<String>,
    /// The array shape of names bound exactly once.
    pub(super) shapes: FxHashMap<String, Shape>,
    pub(super) relevant: FxHashSet<String>,
}

impl Names {
    pub(super) fn of(
        parameters: &[(String, GoType)],
        body: &mut Vec<GoStatement>,
        program: &FunctionTable,
    ) -> Names {
        let mut collect = Collect { program: Some(program), ..Collect::default() };
        for (name, type_) in parameters {
            collect.bind(name, shape_of_type(type_));
        }
        collect.block(body);
        let mut shapes: FxHashMap<String, Shape> = FxHashMap::default();
        for (name, shape) in collect.declared.iter().chain(&collect.evidence) {
            if collect.binders.get(name) == Some(&1)
                && let Some(shape) = shape
            {
                shapes.entry(name.clone()).or_insert(*shape);
            }
        }
        for name in &collect.measured_through_pointers {
            if collect.binders.get(name) == Some(&1) {
                shapes.entry(name.clone()).or_insert(Shape::Pointer);
            }
        }
        // Shapes flow through definitions and from the parameters of the functions called.
        loop {
            let before = shapes.len();
            // `name := source` and `name := *source` share their array.
            for (name, source, through_pointer) in &collect.copies {
                if collect.binders.get(name) != Some(&1) || collect.binders.get(source) != Some(&1)
                {
                    continue;
                }
                let (from, to) = if *through_pointer {
                    (Shape::Pointer, Shape::Fixed)
                } else {
                    (Shape::Fixed, Shape::Fixed)
                };
                if shapes.get(source) == Some(&from) {
                    shapes.entry(name.clone()).or_insert(to);
                }
                if shapes.get(name) == Some(&to) {
                    shapes.entry(source.clone()).or_insert(from);
                }
            }
            if shapes.len() == before {
                break;
            }
        }
        let relevant = relevant_names(body, &program.fields);
        Names { untracked: collect.untracked, assigned: collect.assigned, shapes, relevant }
    }
}

/// The names whose constraints can reach a proof: those that bounds tests, divisions and
/// internal calls read, and those that the definitions and tests of relevant names read.
/// Tracking only these keeps the states of large functions small.
fn relevant_names(body: &mut Vec<GoStatement>, fields: &FxHashSet<String>) -> FxHashSet<String> {
    struct Relevance<'f> {
        fields: &'f FxHashSet<String>,
        relevant: FxHashSet<String>,
        /// When any of the first names is relevant, so are the second.
        edges: Vec<(Vec<String>, Vec<String>)>,
    }
    impl Relevance<'_> {
        fn related(&mut self, names: Vec<String>) {
            self.edges.push((names.clone(), names));
        }
    }
    impl Walk for Relevance<'_> {
        fn statement(&mut self, statement: &mut GoStatement) {
            match statement {
                GoStatement::Define { names, values } => {
                    for (position, value) in values.iter().enumerate() {
                        let targets = if names.len() == values.len() {
                            vec![names[position].clone()]
                        } else {
                            names.clone()
                        };
                        if is_bounds_test(value) {
                            self.relevant.extend(targets.iter().cloned());
                            self.relevant.extend(identifiers(value));
                        } else if is_test(value) {
                            self.related(targets.into_iter().chain(identifiers(value)).collect());
                        } else {
                            self.edges.push((targets, identifiers(value)));
                        }
                    }
                }
                GoStatement::Variable { name, value: Some(value), .. } => {
                    self.edges.push((vec![name.clone()], identifiers(value)))
                }
                GoStatement::Assign { targets, values } => {
                    for (target, value) in targets.iter().zip(values.iter()) {
                        let target = match target {
                            GoExpression::Unary {
                                operator: GoUnaryOperator::Dereference,
                                operand,
                            } => &**operand,
                            target => target,
                        };
                        if let GoExpression::Identifier(name) = target {
                            self.edges.push((vec![name.clone()], identifiers(value)));
                        }
                        if written_field(target, self.fields).is_some() {
                            self.relevant.extend(identifiers(value));
                        }
                    }
                }
                GoStatement::If { condition, .. } => {
                    if is_bounds_test(condition) || matches!(condition, GoExpression::Identifier(_))
                    {
                        self.relevant.extend(identifiers(condition));
                    }
                    self.related(identifiers(condition));
                }
                GoStatement::Switch { value: None, cases, .. } => {
                    for case in cases.iter() {
                        case.values.iter().for_each(|test| self.related(identifiers(test)));
                    }
                }
                GoStatement::Counting { variable, start, end, .. } => {
                    let mut names = identifiers(start);
                    names.extend(identifiers(end));
                    names.push(variable.clone());
                    self.related(names);
                }
                GoStatement::CountingDown { variable, start, .. } => {
                    self.edges.push((vec![variable.clone()], identifiers(start)))
                }
                GoStatement::Range { index: Some(index), iterable, .. } => {
                    self.edges.push((vec![index.clone()], identifiers(iterable)))
                }
                _ => {}
            }
            go_traversal::statement(self, statement);
        }

        fn expression(&mut self, value: &mut GoExpression) {
            if let GoExpression::Call { function, arguments } = value
                && matches!(
                    &**function,
                    GoExpression::Identifier(_) | GoExpression::Qualified { .. }
                )
            {
                arguments.iter().for_each(|argument| self.relevant.extend(identifiers(argument)));
            }
            if let GoExpression::Composite { fields, .. } = value {
                for (label, field) in fields.iter() {
                    if label.as_ref().is_some_and(|label| self.fields.contains(label)) {
                        self.relevant.extend(identifiers(field));
                    }
                }
            }
            go_traversal::expression(self, value);
        }
    }
    let mut relevance = Relevance { fields, relevant: FxHashSet::default(), edges: vec![] };
    relevance.block(body);
    loop {
        let before = relevance.relevant.len();
        for (from, to) in &relevance.edges {
            if from.iter().any(|name| relevance.relevant.contains(name)) {
                relevance.relevant.extend(to.iter().cloned());
            }
        }
        if relevance.relevant.len() == before {
            return relevance.relevant;
        }
    }
}

/// The names an expression reads, function literals' bodies aside.
fn identifiers(value: &GoExpression) -> Vec<String> {
    let mut names = vec![];
    each_subexpression(value, &mut |value| {
        if let GoExpression::Identifier(name) = value {
            names.push(name.clone());
        }
    });
    names
}

fn shape_of_expression(
    value: &GoExpression,
    shapes: &FxHashMap<String, Shape>,
    program: &FunctionTable,
) -> Option<Shape> {
    match value {
        GoExpression::Identifier(name) => shapes.get(name).copied(),
        GoExpression::Unary { operator: GoUnaryOperator::Dereference, operand } => match &**operand
        {
            GoExpression::Identifier(name) if shapes.get(name) == Some(&Shape::Pointer) => {
                Some(Shape::Fixed)
            }
            _ => None,
        },
        GoExpression::String(_) | GoExpression::Utf16(_) => Some(Shape::Fixed),
        GoExpression::Composite { type_: GoType::Slice(_), .. } => Some(Shape::Fixed),
        GoExpression::Address(inner)
            if matches!(&**inner, GoExpression::Composite { type_: GoType::Slice(_), .. }) =>
        {
            Some(Shape::Pointer)
        }
        GoExpression::Conversion { type_, .. } => {
            shape_of_type(type_).filter(|shape| *shape == Shape::Fixed)
        }
        GoExpression::Call { function, arguments } => match &**function {
            _ if function.is_builtin(GoBuiltin::Append) => Some(Shape::Fixed),
            _ if function.is_qualified(GoPackage::Array, "Bounded") => Some(Shape::Fixed),
            _ if function.is_builtin(GoBuiltin::Make) => match arguments.first() {
                Some(GoExpression::Type(GoType::Slice(_))) => Some(Shape::Fixed),
                _ => None,
            },
            GoExpression::Identifier(name) => {
                program.signatures.get(name)?.result.as_ref().and_then(shape_of_type)
            }
            _ => None,
        },
        _ => None,
    }
}

#[derive(Default)]
struct Collect<'p> {
    program: Option<&'p FunctionTable>,
    binders: FxHashMap<String, usize>,
    declared: Vec<(String, Option<Shape>)>,
    /// `name := source` or, when true, `name := *source`.
    copies: Vec<(String, String, bool)>,
    /// Arrays passed for a parameter of an array type.
    evidence: Vec<(String, Option<Shape>)>,
    untracked: FxHashSet<String>,
    assigned: FxHashSet<String>,
    /// Names measured or indexed through: `len(*xs)`, `(*xs)[i]`. The backend's only map type
    /// is an object's index, a struct field nothing points to, so such a name points to a
    /// slice, or to a string that only a store through the pointer changes.
    measured_through_pointers: FxHashSet<String>,
    closures: usize,
}

impl Collect<'_> {
    fn bind(&mut self, name: &str, shape: Option<Shape>) {
        *self.binders.entry(name.to_string()).or_default() += 1;
        self.declared.push((name.to_string(), shape));
    }
}

impl Walk for Collect<'_> {
    fn statement(&mut self, statement: &mut GoStatement) {
        match statement {
            GoStatement::Define { names, values } => {
                for (position, name) in names.iter().enumerate() {
                    let value = (names.len() == values.len()).then(|| &values[position]);
                    let shape = match value {
                        Some(GoExpression::Identifier(source)) => {
                            self.copies.push((name.clone(), source.clone(), false));
                            None
                        }
                        Some(GoExpression::Unary {
                            operator: GoUnaryOperator::Dereference,
                            operand,
                        }) => {
                            if let GoExpression::Identifier(source) = &**operand {
                                self.copies.push((name.clone(), source.clone(), true));
                            }
                            None
                        }
                        Some(value) => self.program.and_then(|program| {
                            shape_of_expression(value, &FxHashMap::default(), program)
                        }),
                        None => None,
                    };
                    self.bind(name, shape);
                }
            }
            GoStatement::Variable { name, type_, .. } => self.bind(name, shape_of_type(type_)),
            GoStatement::IfAssert { name, .. } => self.bind(name, None),
            GoStatement::Range { index, element, .. } => {
                index.iter().for_each(|index| self.bind(index, None));
                self.bind(element, None);
            }
            GoStatement::Counting { variable, .. } | GoStatement::CountingDown { variable, .. } => {
                self.bind(variable, None)
            }
            GoStatement::Assign { targets, .. } => {
                for target in targets.iter() {
                    if let Some(root) = headers::assigned_root(target) {
                        self.assigned.insert(root.to_string());
                        if self.closures > 0 {
                            self.untracked.insert(root.to_string());
                        }
                    }
                }
            }
            _ => {}
        }
        go_traversal::statement(self, statement);
    }

    fn expression(&mut self, value: &mut GoExpression) {
        match value {
            GoExpression::Address(inner) => {
                if let Some(root) = aliases::target_root(inner) {
                    self.untracked.insert(root.to_string());
                }
            }
            GoExpression::Function { parameters, .. } => {
                parameters.iter().for_each(|(name, type_)| self.bind(name, shape_of_type(type_)));
                self.closures += 1;
                go_traversal::expression(self, value);
                self.closures -= 1;
                return;
            }
            GoExpression::Call { function, arguments } => {
                if let GoExpression::Identifier(callee) = &**function {
                    let parameters = self
                        .program
                        .and_then(|program| program.signatures.get(callee))
                        .map(|signature| signature.parameters.as_slice())
                        .unwrap_or(&[]);
                    for (argument, type_) in arguments.iter().zip(parameters) {
                        let evidence = match (argument, shape_of_type(type_)) {
                            (GoExpression::Identifier(name), Some(shape)) => Some((name, shape)),
                            (
                                GoExpression::Unary {
                                    operator: GoUnaryOperator::Dereference,
                                    operand,
                                },
                                Some(Shape::Fixed),
                            ) => match &**operand {
                                GoExpression::Identifier(name) => Some((name, Shape::Pointer)),
                                _ => None,
                            },
                            _ => None,
                        };
                        if let Some((name, shape)) = evidence {
                            self.evidence.push((name.clone(), Some(shape)));
                        }
                    }
                    if function.is_builtin(GoBuiltin::Len)
                        && let [
                            GoExpression::Unary { operator: GoUnaryOperator::Dereference, operand },
                        ] = arguments.as_slice()
                        && let GoExpression::Identifier(pointer) = &**operand
                    {
                        self.measured_through_pointers.insert(pointer.clone());
                    }
                }
            }
            GoExpression::Index { value: indexed, .. } => {
                if let GoExpression::Unary { operator: GoUnaryOperator::Dereference, operand } =
                    &**indexed
                    && let GoExpression::Identifier(pointer) = &**operand
                {
                    self.measured_through_pointers.insert(pointer.clone());
                }
            }
            _ => {}
        }
        go_traversal::expression(self, value);
    }
}
