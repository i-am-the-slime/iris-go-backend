use rustc_hash::FxHashSet;

use super::{GoBuiltin, GoDeclaration, GoExpression, GoStatement, GoType};
use crate::go_traversal::{self, Walk};

/// A name as a declaration uses it: a reference to another declaration or a
/// local, or a local the declaration binds.
pub enum Name<'a> {
    Reference(&'a mut String),
    /// A reference the code may change the value of: an assignment's target
    /// or a variable whose address it takes.
    Written(&'a mut String),
    Binder(&'a mut String),
}

impl GoDeclaration {
    /// The name the declaration declares, if it declares exactly one.
    pub fn name(&self) -> Option<&str> {
        match self {
            GoDeclaration::Type { name, .. }
            | GoDeclaration::Alias { name, .. }
            | GoDeclaration::Source { name, .. }
            | GoDeclaration::Written { name, .. }
            | GoDeclaration::GenericType { name, .. }
            | GoDeclaration::Constant { name, .. }
            | GoDeclaration::Variable { name, .. }
            | GoDeclaration::Function { name, .. } => Some(name),
            GoDeclaration::Constants { .. } => None,
        }
    }

    /// Visits every name in the declaration's value or body, and the
    /// parameters it binds; not its own name, types or field labels.
    pub fn for_each_name_mut(&mut self, visit: &mut impl FnMut(Name<'_>)) {
        match self {
            GoDeclaration::Constant { value, .. } | GoDeclaration::Variable { value, .. } => {
                expression_names(value, visit)
            }
            GoDeclaration::Function { parameters, body, .. } => {
                for (parameter, _) in parameters.iter_mut() {
                    visit(Name::Binder(parameter));
                }
                statements_names(body, visit);
            }
            GoDeclaration::Source { .. }
            | GoDeclaration::Written { .. }
            | GoDeclaration::Type { .. }
            | GoDeclaration::Alias { .. }
            | GoDeclaration::GenericType { .. }
            | GoDeclaration::Constants { .. } => {}
        }
    }

    /// Every name the declaration's code uses or binds, so that a new one can avoid them all.
    pub fn all_names(&mut self) -> FxHashSet<String> {
        self.declared_names().names
    }

    pub fn declared_names(&mut self) -> DeclarationNames {
        let mut names = FxHashSet::default();
        let mut locals = FxHashSet::default();
        self.for_each_name_mut(&mut |name| {
            if let Name::Binder(name) = &name {
                locals.insert(name.to_string());
            }
            let (Name::Reference(name) | Name::Written(name) | Name::Binder(name)) = name;
            names.insert(name.clone());
        });
        DeclarationNames { names, locals }
    }
}

pub struct DeclarationNames {
    pub names: FxHashSet<String>,
    pub locals: FxHashSet<String>,
}

/// A place where a declaration names something: a value, a type, or a local
/// it binds. Values and types may refer to other declarations.
pub enum Reference<'a> {
    /// An identifier or a qualified identifier expression.
    Value(&'a mut GoExpression),
    /// The name of a named or generic type.
    Type(&'a mut String),
    Binder(&'a mut String),
}

impl GoDeclaration {
    /// Visits every value, type and binder the declaration names, apart from
    /// the names it declares itself.
    pub fn for_each_reference_mut(&mut self, visit: &mut impl FnMut(Reference<'_>)) {
        match self {
            GoDeclaration::Source { .. } | GoDeclaration::Written { .. } => {}
            GoDeclaration::Type { type_, .. } | GoDeclaration::Alias { type_, .. } => {
                type_references(type_, visit)
            }
            GoDeclaration::GenericType { parameter, type_, .. } => {
                let parameter = parameter.clone();
                type_references(type_, &mut |reference| match reference {
                    Reference::Type(name) if *name == parameter => {}
                    reference => visit(reference),
                });
            }
            GoDeclaration::Constants { type_name, .. } => {
                if let Some(type_name) = type_name {
                    visit(Reference::Type(type_name));
                }
            }
            GoDeclaration::Constant { type_, value, .. }
            | GoDeclaration::Variable { type_, value, .. } => {
                if let Some(type_) = type_ {
                    type_references(type_, visit);
                }
                expression_references(value, visit);
            }
            GoDeclaration::Function { parameters, result, body, .. } => {
                for (parameter, type_) in parameters.iter_mut() {
                    visit(Reference::Binder(parameter));
                    type_references(type_, visit);
                }
                if let Some(result) = result {
                    type_references(result, visit);
                }
                statements_references(body, visit);
            }
        }
    }
}

fn type_references(type_: &mut GoType, visit: &mut impl FnMut(Reference<'_>)) {
    match type_ {
        GoType::Named(name) => visit(Reference::Type(name)),
        GoType::Generic { name, arguments } => {
            visit(Reference::Type(name));
            arguments.iter_mut().for_each(|argument| type_references(argument, visit));
        }
        GoType::Slice(element) | GoType::Pointer(element) => type_references(element, visit),
        GoType::Map(key, value) => {
            type_references(key, visit);
            type_references(value, visit);
        }
        GoType::Function { parameters, result } => {
            parameters.iter_mut().for_each(|parameter| type_references(parameter, visit));
            if let Some(result) = result {
                type_references(result, visit);
            }
        }
        GoType::Struct(fields) => {
            fields.iter_mut().for_each(|field| type_references(&mut field.type_, visit));
        }
        GoType::Results(results) => {
            results.iter_mut().for_each(|result| type_references(result, visit));
        }
        GoType::Int
        | GoType::Float64
        | GoType::Bool
        | GoType::Rune
        | GoType::String
        | GoType::EmptyStruct
        | GoType::Any
        | GoType::Erased(_) => {}
    }
}

/// The references of statements, in order.
struct References<'v, F>(&'v mut F);

fn statements_references(statements: &mut [GoStatement], visit: &mut impl FnMut(Reference<'_>)) {
    let mut references = References(visit);
    statements.iter_mut().for_each(|statement| references.statement(statement));
}

fn expression_references(expression: &mut GoExpression, visit: &mut impl FnMut(Reference<'_>)) {
    References(visit).expression(expression)
}

impl<F: FnMut(Reference<'_>)> Walk for References<'_, F> {
    fn statement(&mut self, statement: &mut GoStatement) {
        match statement {
            GoStatement::Define { names, .. } => {
                names.iter_mut().for_each(|name| (self.0)(Reference::Binder(name)))
            }
            GoStatement::Variable { name, type_, .. } => {
                (self.0)(Reference::Binder(name));
                type_references(type_, self.0);
            }
            GoStatement::IfAssert { name, type_, .. } => {
                (self.0)(Reference::Binder(name));
                type_references(type_, self.0);
            }
            GoStatement::Range { index, element, .. } => {
                index.iter_mut().for_each(|index| (self.0)(Reference::Binder(index)));
                (self.0)(Reference::Binder(element));
            }
            GoStatement::Counting { variable, .. } | GoStatement::CountingDown { variable, .. } => {
                (self.0)(Reference::Binder(variable))
            }
            _ => {}
        }
        go_traversal::statement(self, statement);
    }

    fn expression(&mut self, expression: &mut GoExpression) {
        match expression {
            GoExpression::Identifier(_) | GoExpression::Qualified { .. } => {
                (self.0)(Reference::Value(expression))
            }
            GoExpression::Type(type_)
            | GoExpression::Conversion { type_, .. }
            | GoExpression::TypeAssertion { type_, .. }
            | GoExpression::Composite { type_, .. } => type_references(type_, self.0),
            GoExpression::Function { parameters, result, .. } => {
                for (parameter, type_) in parameters.iter_mut() {
                    (self.0)(Reference::Binder(parameter));
                    type_references(type_, self.0);
                }
                if let Some(result) = result {
                    type_references(result, self.0);
                }
            }
            _ => {}
        }
        go_traversal::expression(self, expression);
        if let GoExpression::Instantiation { arguments, .. } = expression {
            arguments.iter_mut().for_each(|argument| type_references(argument, self.0));
        }
    }
}

/// Visits every name the statements use or bind, in order.
pub fn statements_names(statements: &mut [GoStatement], visit: &mut impl FnMut(Name<'_>)) {
    let mut names = Names(visit);
    statements.iter_mut().for_each(|statement| names.statement(statement));
}

fn expression_names(expression: &mut GoExpression, visit: &mut impl FnMut(Name<'_>)) {
    Names(visit).expression(expression)
}

struct Names<'v, F>(&'v mut F);

impl<F: FnMut(Name<'_>)> Names<'_, F> {
    /// The names in an assignment's target or under `&`: the variable whose
    /// value changes, and the names read to find the place within it.
    fn written(&mut self, target: &mut GoExpression) {
        match target {
            GoExpression::Identifier(name) => (self.0)(Name::Written(name)),
            GoExpression::Field { value, .. } => self.written(value),
            GoExpression::Index { value, index } => {
                self.written(value);
                self.expression(index);
            }
            target => self.expression(target),
        }
    }
}

impl<F: FnMut(Name<'_>)> Walk for Names<'_, F> {
    fn statement(&mut self, statement: &mut GoStatement) {
        match statement {
            GoStatement::Define { names, .. } => {
                names.iter_mut().for_each(|name| (self.0)(Name::Binder(name)))
            }
            GoStatement::Variable { name, .. } | GoStatement::IfAssert { name, .. } => {
                (self.0)(Name::Binder(name))
            }
            GoStatement::Range { index, element, .. } => {
                index.iter_mut().for_each(|index| (self.0)(Name::Binder(index)));
                (self.0)(Name::Binder(element));
            }
            GoStatement::Counting { variable, .. } | GoStatement::CountingDown { variable, .. } => {
                (self.0)(Name::Binder(variable))
            }
            GoStatement::Assign { targets, values } => {
                targets.iter_mut().for_each(|target| self.written(target));
                return values.iter_mut().for_each(|value| self.expression(value));
            }
            _ => {}
        }
        go_traversal::statement(self, statement);
    }

    fn expression(&mut self, expression: &mut GoExpression) {
        match expression {
            GoExpression::Identifier(name) => (self.0)(Name::Reference(name)),
            GoExpression::Address(value) => self.written(value),
            // `delete(m, k)` and `clear(m)` change the map `m` in place.
            GoExpression::Call { function, arguments }
                if (function.is_builtin(GoBuiltin::Delete)
                    || function.is_builtin(GoBuiltin::Clear))
                    && !arguments.is_empty() =>
            {
                self.expression(function);
                let (changed, rest) = arguments.split_at_mut(1);
                self.written(&mut changed[0]);
                rest.iter_mut().for_each(|argument| self.expression(argument));
            }
            GoExpression::Function { parameters, .. } => {
                for (parameter, _) in parameters.iter_mut() {
                    (self.0)(Name::Binder(parameter));
                }
                go_traversal::expression(self, expression);
            }
            expression => go_traversal::expression(self, expression),
        }
    }
}
