//! A small Go syntax tree with a printer that follows `gofmt` layout.

use std::fmt::Write;

use rayon::prelude::*;

use crate::walk::{self, Walk};

#[derive(Debug, Clone, Eq)]
pub enum GoType {
    Named(String),
    Int,
    Float64,
    Bool,
    Rune,
    String,
    EmptyStruct,
    Any,
    /// `any` standing for a type erased for the given reason.
    Erased(crate::erasure::Erasure),
    Slice(Box<GoType>),
    Pointer(Box<GoType>),
    Function {
        parameters: Vec<GoType>,
        result: Option<Box<GoType>>,
    },
    Struct(Vec<(String, GoType)>),
    /// A generic type instantiated at type arguments, `name[arguments]`.
    Generic {
        name: String,
        arguments: Vec<GoType>,
    },
}

/// Types compare as Go sees them: every flavour of `any` is the same type.
impl PartialEq for GoType {
    fn eq(&self, other: &GoType) -> bool {
        use GoType::*;
        match (self, other) {
            (Any | Erased(_), Any | Erased(_)) => true,
            (Named(left), Named(right)) => left == right,
            (Int, Int) | (Float64, Float64) | (Bool, Bool) | (Rune, Rune) => true,
            (String, String) | (EmptyStruct, EmptyStruct) => true,
            (Slice(left), Slice(right)) | (Pointer(left), Pointer(right)) => left == right,
            (
                Function { parameters: left, result: left_result },
                Function { parameters: right, result: right_result },
            ) => left == right && left_result == right_result,
            (Struct(left), Struct(right)) => left == right,
            (
                Generic { name: left, arguments: left_arguments },
                Generic { name: right, arguments: right_arguments },
            ) => left == right && left_arguments == right_arguments,
            _ => false,
        }
    }
}

#[derive(Debug, Clone)]
pub enum GoExpression {
    Identifier(String),
    Qualified {
        package: String,
        name: String,
    },
    Integer(i64),
    Float(String),
    String(String),
    Rune(char),
    Boolean(bool),
    Call {
        function: Box<GoExpression>,
        arguments: Vec<GoExpression>,
    },
    Binary {
        operator: &'static str,
        left: Box<GoExpression>,
        right: Box<GoExpression>,
    },
    Unary {
        operator: &'static str,
        operand: Box<GoExpression>,
    },
    Field {
        value: Box<GoExpression>,
        name: String,
    },
    Index {
        value: Box<GoExpression>,
        index: Box<GoExpression>,
    },
    Composite {
        type_: GoType,
        fields: Vec<(Option<String>, GoExpression)>,
    },
    Address(Box<GoExpression>),
    Conversion {
        type_: GoType,
        value: Box<GoExpression>,
    },
    TypeAssertion {
        value: Box<GoExpression>,
        type_: GoType,
    },
    Type(GoType),
    Spread(Box<GoExpression>),
    Function {
        parameters: Vec<(String, GoType)>,
        result: Option<GoType>,
        body: Vec<GoStatement>,
    },
    /// A generic function instantiated at type arguments, `function[arguments]`.
    Instantiation {
        function: Box<GoExpression>,
        arguments: Vec<GoType>,
    },
}

#[derive(Debug, Clone)]
pub enum GoStatement {
    Define {
        names: Vec<String>,
        values: Vec<GoExpression>,
    },
    Variable {
        name: String,
        type_: GoType,
        value: Option<GoExpression>,
    },
    Assign {
        targets: Vec<GoExpression>,
        values: Vec<GoExpression>,
    },
    Expression(GoExpression),
    Defer(GoExpression),
    Return(Option<GoExpression>),
    If {
        condition: GoExpression,
        then: Vec<GoStatement>,
        otherwise: Vec<GoStatement>,
    },
    Switch {
        value: Option<GoExpression>,
        cases: Vec<GoCase>,
        default: Option<GoDefault>,
    },
    /// `if name, ok := value.(T); ok { then }`
    IfAssert {
        name: String,
        value: GoExpression,
        type_: GoType,
        then: Vec<GoStatement>,
    },
    Loop(Vec<GoStatement>),
    Range {
        index: Option<String>,
        element: String,
        iterable: GoExpression,
        body: Vec<GoStatement>,
    },
    Counting {
        variable: String,
        start: GoExpression,
        end: GoExpression,
        body: Vec<GoStatement>,
    },
    CountingDown {
        variable: String,
        start: GoExpression,
        body: Vec<GoStatement>,
    },
    Continue,
    Break,
    BreakTo(String),
    LabeledLoop {
        label: String,
        body: Vec<GoStatement>,
    },
    Block(Vec<GoStatement>),
}

#[derive(Debug, Clone)]
pub struct GoCase {
    pub values: Vec<GoExpression>,
    pub body: Vec<GoStatement>,
}

#[derive(Debug, Clone)]
pub struct GoDefault {
    pub covers: Vec<GoExpression>,
    pub body: Vec<GoStatement>,
}

impl GoDefault {
    pub fn covering(cases: &mut Vec<GoCase>) -> GoDefault {
        let GoCase { values, body } =
            cases.pop().expect("invariant violated: a total switch has a case");
        GoDefault { covers: values, body }
    }
}

#[derive(Debug, Clone)]
pub enum GoDeclaration {
    /// Fixed support code that generated programs share, declaring `name`
    /// where its template says `{name}`.
    Source {
        name: String,
        template: &'static str,
    },
    Type {
        name: String,
        type_: GoType,
    },
    /// `type name = type_`: another spelling of the same type, for a recursive
    /// newtype whose cycle already passes through a named type.
    Alias {
        name: String,
        type_: GoType,
    },
    /// `type name[parameter any] type_`.
    GenericType {
        name: String,
        parameter: String,
        type_: GoType,
    },
    Constants {
        type_name: Option<String>,
        names: Vec<String>,
    },
    /// `var name T`, zero-initialised.
    Declared {
        name: String,
        type_: GoType,
    },
    Variable {
        name: String,
        type_: Option<GoType>,
        value: GoExpression,
    },
    Function {
        name: String,
        parameters: Vec<(String, GoType)>,
        result: Option<GoType>,
        body: Vec<GoStatement>,
    },
}

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
            | GoDeclaration::GenericType { name, .. }
            | GoDeclaration::Declared { name, .. }
            | GoDeclaration::Variable { name, .. }
            | GoDeclaration::Function { name, .. } => Some(name),
            GoDeclaration::Constants { .. } => None,
        }
    }

    /// Visits every name in the declaration's value or body, and the
    /// parameters it binds; not its own name, types or field labels.
    pub fn for_each_name_mut(&mut self, visit: &mut impl FnMut(Name<'_>)) {
        match self {
            GoDeclaration::Variable { value, .. } => expression_names(value, visit),
            GoDeclaration::Function { parameters, body, .. } => {
                for (parameter, _) in parameters.iter_mut() {
                    visit(Name::Binder(parameter));
                }
                statements_names(body, visit);
            }
            GoDeclaration::Source { .. }
            | GoDeclaration::Type { .. }
            | GoDeclaration::Alias { .. }
            | GoDeclaration::GenericType { .. }
            | GoDeclaration::Constants { .. }
            | GoDeclaration::Declared { .. } => {}
        }
    }

    pub fn render(&self) -> String {
        let mut printer =
            Printer { output: String::new(), indentation: 0, census: Default::default() };
        printer.declaration(self);
        printer.output
    }
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
            GoDeclaration::Source { .. } => {}
            GoDeclaration::Type { type_, .. }
            | GoDeclaration::Alias { type_, .. }
            | GoDeclaration::Declared { type_, .. } => type_references(type_, visit),
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
            GoDeclaration::Variable { type_, value, .. } => {
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
        GoType::Function { parameters, result } => {
            parameters.iter_mut().for_each(|parameter| type_references(parameter, visit));
            if let Some(result) = result {
                type_references(result, visit);
            }
        }
        GoType::Struct(fields) => {
            fields.iter_mut().for_each(|(_, field)| type_references(field, visit));
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
        walk::statement(self, statement);
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
        walk::expression(self, expression);
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
        walk::statement(self, statement);
    }

    fn expression(&mut self, expression: &mut GoExpression) {
        match expression {
            GoExpression::Identifier(name) => (self.0)(Name::Reference(name)),
            GoExpression::Address(value) => self.written(value),
            GoExpression::Function { parameters, .. } => {
                for (parameter, _) in parameters.iter_mut() {
                    (self.0)(Name::Binder(parameter));
                }
                walk::expression(self, expression);
            }
            expression => walk::expression(self, expression),
        }
    }
}

impl GoType {
    /// The type as Go spells it, on one line.
    pub fn render(&self) -> String {
        let mut printer =
            Printer { output: String::new(), indentation: 0, census: Default::default() };
        printer.type_argument(self)
    }
}

pub struct GoFile {
    pub package: String,
    pub imports: Vec<GoImport>,
    pub declarations: Vec<GoDeclaration>,
}

/// `import alias "path"`, or `import "path"` when the package's own name will do.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct GoImport {
    pub path: String,
    pub alias: Option<String>,
}

impl GoFile {
    pub fn render(&self) -> String {
        self.render_with_census().0
    }

    /// The source together with a count of the `any` it contains, by cause.
    pub fn render_with_census(&self) -> (String, crate::erasure::Census) {
        let mut printer =
            Printer { output: String::new(), indentation: 0, census: Default::default() };
        let _ = writeln!(printer.output, "package {}", self.package);
        let imports: Vec<String> = self
            .imports
            .iter()
            .map(|GoImport { path, alias }| match alias {
                Some(alias) => format!("{alias} \"{path}\""),
                None => format!("\"{path}\""),
            })
            .collect();
        match imports.as_slice() {
            [] => {}
            [import] => {
                let _ = writeln!(printer.output, "\nimport {import}");
            }
            imports => {
                printer.output.push_str("\nimport (\n");
                for import in imports {
                    let _ = writeln!(printer.output, "\t{import}");
                }
                printer.output.push_str(")\n");
            }
        }
        // Declarations render independently, so they render in parallel and
        // join in order.
        let rendered: Vec<(String, crate::erasure::Census)> = self
            .declarations
            .par_iter()
            .map(|declaration| {
                let mut printer =
                    Printer { output: String::new(), indentation: 0, census: Default::default() };
                printer.output.push('\n');
                printer.declaration(declaration);
                (printer.output, printer.census)
            })
            .collect();
        for (output, census) in rendered {
            printer.output.push_str(&output);
            printer.census.absorb(census);
        }
        (printer.output, printer.census)
    }
}

struct Printer {
    output: String,
    indentation: usize,
    census: crate::erasure::Census,
}

impl Printer {
    fn line(&mut self, text: &str) {
        for _ in 0..self.indentation {
            self.output.push('\t');
        }
        self.output.push_str(text);
        self.output.push('\n');
    }

    fn declaration(&mut self, declaration: &GoDeclaration) {
        match declaration {
            GoDeclaration::Source { name, template } => {
                self.output.push_str(&template.replace("{name}", name));
            }
            GoDeclaration::Type { name, type_ } => {
                let rendered = self.type_(type_);
                self.line(&format!("type {name} {rendered}"));
            }
            GoDeclaration::Alias { name, type_ } => {
                let rendered = self.type_(type_);
                self.line(&format!("type {name} = {rendered}"));
            }
            GoDeclaration::GenericType { name, parameter, type_ } => {
                let rendered = self.type_(type_);
                self.line(&format!("type {name}[{parameter} any] {rendered}"));
            }
            GoDeclaration::Constants { type_name, names } => {
                self.line("const (");
                self.indentation += 1;
                for (position, name) in names.iter().enumerate() {
                    if position == 0 {
                        match type_name {
                            Some(type_name) => self.line(&format!("{name} {type_name} = iota")),
                            None => self.line(&format!("{name} = iota")),
                        }
                    } else {
                        self.line(name);
                    }
                }
                self.indentation -= 1;
                self.line(")");
            }
            GoDeclaration::Declared { name, type_ } => {
                let type_ = self.type_(type_);
                self.line(&format!("var {name} {type_}"));
            }
            GoDeclaration::Variable { name, type_, value } => {
                let value = self.expression(value, 0);
                match type_ {
                    Some(type_) => {
                        let type_ = self.type_(type_);
                        self.line(&format!("var {name} {type_} = {value}"));
                    }
                    None => self.line(&format!("var {name} = {value}")),
                }
            }
            GoDeclaration::Function { name, parameters, result, body } => {
                let signature = self.signature(parameters, result.as_ref());
                self.line(&format!("func {name}{signature} {{"));
                self.block(body);
                self.line("}");
            }
        }
    }

    fn signature(&mut self, parameters: &[(String, GoType)], result: Option<&GoType>) -> String {
        let parameters: Vec<String> = parameters
            .iter()
            .map(|(name, type_)| format!("{name} {}", self.type_(type_)))
            .collect();
        match result {
            Some(result) => format!("({}) {}", parameters.join(", "), self.type_(result)),
            None => format!("({})", parameters.join(", ")),
        }
    }

    fn block(&mut self, statements: &[GoStatement]) {
        self.indentation += 1;
        for statement in statements {
            self.statement(statement);
        }
        self.indentation -= 1;
    }

    fn statement(&mut self, statement: &GoStatement) {
        match statement {
            GoStatement::Define { names, values } => {
                let values: Vec<String> =
                    values.iter().map(|value| self.expression(value, 0)).collect();
                self.line(&format!("{} := {}", names.join(", "), values.join(", ")));
            }
            GoStatement::Variable { name, type_, value } => {
                let type_ = self.type_(type_);
                match value {
                    Some(value) => {
                        let value = self.expression(value, 0);
                        self.line(&format!("var {name} {type_} = {value}"));
                    }
                    None => self.line(&format!("var {name} {type_}")),
                }
            }
            GoStatement::Assign { targets, values } => {
                let targets: Vec<String> =
                    targets.iter().map(|target| self.expression(target, 0)).collect();
                let values: Vec<String> =
                    values.iter().map(|value| self.expression(value, 0)).collect();
                self.line(&format!("{} = {}", targets.join(", "), values.join(", ")));
            }
            GoStatement::Expression(expression) => {
                let expression = self.expression(expression, 0);
                self.line(&expression);
            }
            GoStatement::Defer(expression) => {
                let expression = self.expression(expression, 0);
                self.line(&format!("defer {expression}"));
            }
            GoStatement::Return(None) => self.line("return"),
            GoStatement::Return(Some(value)) => {
                let value = self.expression(value, 0);
                self.line(&format!("return {value}"));
            }
            GoStatement::If { condition, then, otherwise } => {
                let condition = self.expression(condition, 0);
                self.line(&format!("if {condition} {{"));
                self.block(then);
                self.else_chain(otherwise);
            }
            GoStatement::IfAssert { name, value, type_, then } => {
                self.census.assertions += 1;
                let value = self.expression(value, 6);
                let type_ = self.type_(type_);
                self.line(&format!("if {name}, ok := {value}.({type_}); ok {{"));
                self.block(then);
                self.line("}");
            }
            GoStatement::Switch { value, cases, default } => {
                match value {
                    Some(value) => {
                        let value = self.expression(value, 0);
                        self.line(&format!("switch {value} {{"));
                    }
                    None => self.line("switch {"),
                }
                for case in cases {
                    let values: Vec<String> =
                        case.values.iter().map(|value| self.expression(value, 0)).collect();
                    self.line(&format!("case {}:", values.join(", ")));
                    self.block(&case.body);
                }
                if let Some(GoDefault { covers, body }) = default {
                    if covers.is_empty() {
                        self.line("default:");
                    } else {
                        let covers: Vec<String> =
                            covers.iter().map(|value| self.expression(value, 0)).collect();
                        self.line(&format!("default: // {}", covers.join(", ")));
                    }
                    self.block(body);
                }
                self.line("}");
            }
            GoStatement::Loop(body) => {
                self.line("for {");
                self.block(body);
                self.line("}");
            }
            GoStatement::Range { index, element, iterable, body } => {
                let iterable = self.expression(iterable, 0);
                match (index, element.as_str()) {
                    (None, "_") => self.line(&format!("for range {iterable} {{")),
                    (None, element) => {
                        self.line(&format!("for _, {element} := range {iterable} {{"))
                    }
                    (Some(index), "_") => self.line(&format!("for {index} := range {iterable} {{")),
                    (Some(index), element) => {
                        self.line(&format!("for {index}, {element} := range {iterable} {{"))
                    }
                }
                self.block(body);
                self.line("}");
            }
            GoStatement::Counting { variable, start, end, body } => {
                let start = self.expression(start, 0);
                let end = self.expression(end, 0);
                self.line(&format!(
                    "for {variable} := {start}; {variable} < {end}; {variable}++ {{"
                ));
                self.block(body);
                self.line("}");
            }
            GoStatement::CountingDown { variable, start, body } => {
                let start = self.expression(start, 0);
                self.line(&format!("for {variable} := {start}; {variable} >= 0; {variable}-- {{"));
                self.block(body);
                self.line("}");
            }
            GoStatement::Continue => self.line("continue"),
            GoStatement::Break => self.line("break"),
            GoStatement::BreakTo(label) => self.line(&format!("break {label}")),
            GoStatement::LabeledLoop { label, body } => {
                let indentation = self.indentation;
                self.indentation = indentation.saturating_sub(1);
                self.line(&format!("{label}:"));
                self.indentation = indentation;
                self.line("for {");
                self.block(body);
                self.line("}");
            }
            GoStatement::Block(body) => {
                self.line("{");
                self.block(body);
                self.line("}");
            }
        }
    }

    fn else_chain(&mut self, otherwise: &[GoStatement]) {
        match otherwise {
            [] => self.line("}"),
            [GoStatement::If { condition, then, otherwise }] => {
                let condition = self.expression(condition, 0);
                self.line(&format!("}} else if {condition} {{"));
                self.block(then);
                self.else_chain(otherwise);
            }
            _ => {
                self.line("} else {");
                self.block(otherwise);
                self.line("}");
            }
        }
    }

    fn type_(&mut self, type_: &GoType) -> String {
        match type_ {
            GoType::Named(name) => name.clone(),
            GoType::Int => "int".into(),
            GoType::Float64 => "float64".into(),
            GoType::Bool => "bool".into(),
            GoType::Rune => "rune".into(),
            GoType::String => "string".into(),
            GoType::EmptyStruct => "struct{}".into(),
            GoType::Any => {
                self.census.record(crate::erasure::Erasure::Runtime);
                "any".into()
            }
            GoType::Erased(erasure) => {
                self.census.record(*erasure);
                "any".into()
            }
            GoType::Slice(element) => format!("[]{}", self.type_(element)),
            GoType::Pointer(element) => format!("*{}", self.type_(element)),
            GoType::Function { parameters, result } => {
                let parameters: Vec<String> =
                    parameters.iter().map(|parameter| self.type_(parameter)).collect();
                match result {
                    Some(result) => {
                        format!("func({}) {}", parameters.join(", "), self.type_(result))
                    }
                    None => format!("func({})", parameters.join(", ")),
                }
            }
            GoType::Struct(fields) => {
                if fields.is_empty() {
                    return "struct{}".into();
                }
                let mut rendered = String::from("struct {\n");
                let width = fields.iter().map(|(name, _)| name.len()).max().unwrap_or(0);
                for (name, field_type) in fields {
                    let field_type = self.type_(field_type);
                    for _ in 0..=self.indentation {
                        rendered.push('\t');
                    }
                    let _ = writeln!(rendered, "{name:width$} {field_type}");
                }
                for _ in 0..self.indentation {
                    rendered.push('\t');
                }
                rendered.push('}');
                rendered
            }
            GoType::Generic { name, arguments } => {
                let arguments: Vec<String> =
                    arguments.iter().map(|argument| self.type_argument(argument)).collect();
                format!("{name}[{}]", arguments.join(", "))
            }
        }
    }

    /// A type as a type argument: on one line, since `[...]` cannot span lines.
    fn type_argument(&mut self, type_: &GoType) -> String {
        let indentation = std::mem::take(&mut self.indentation);
        let rendered = self.type_(type_);
        self.indentation = indentation;
        let parts: Vec<&str> =
            rendered.lines().map(str::trim).filter(|line| !line.is_empty()).collect();
        parts.join("; ").replace("{; ", "{ ").replace("; }", " }")
    }

    fn expression(&mut self, expression: &GoExpression, parent_precedence: u8) -> String {
        match expression {
            GoExpression::Identifier(name) => name.clone(),
            GoExpression::Qualified { package, name } => format!("{package}.{name}"),
            GoExpression::Integer(value) => value.to_string(),
            GoExpression::Float(value) => value.clone(),
            GoExpression::String(value) => go_string(value),
            GoExpression::Rune(value) => go_rune(*value),
            GoExpression::Boolean(value) => value.to_string(),
            GoExpression::Call { function, arguments } => {
                let function = self.expression(function, 6);
                let arguments: Vec<String> =
                    arguments.iter().map(|argument| self.expression(argument, 0)).collect();
                format!("{function}({})", arguments.join(", "))
            }
            GoExpression::Binary { operator, left, right } => {
                let precedence = binary_precedence(operator);
                let left = self.expression(left, precedence);
                let right = self.expression(right, precedence + 1);
                let rendered = format!("{left} {operator} {right}");
                if precedence < parent_precedence { format!("({rendered})") } else { rendered }
            }
            GoExpression::Unary { operator, operand } => {
                let operand = self.expression(operand, 6);
                format!("{operator}{operand}")
            }
            GoExpression::Field { value, name } => {
                // A composite literal is ambiguous in if/for/switch headers.
                let composite = matches!(value.as_ref(), GoExpression::Composite { .. });
                let value = self.expression(value, 6);
                if composite {
                    return format!("({value}).{name}");
                }
                format!("{value}.{name}")
            }
            GoExpression::Index { value, index } => {
                let value = self.expression(value, 6);
                let index = self.expression(index, 0);
                format!("{value}[{index}]")
            }
            GoExpression::Composite { type_, fields } => {
                let type_ = self.type_(type_);
                let fields: Vec<String> = fields
                    .iter()
                    .map(|(name, value)| {
                        let value = self.expression(value, 0);
                        match name {
                            Some(name) => format!("{name}: {value}"),
                            None => value,
                        }
                    })
                    .collect();
                format!("{type_}{{{}}}", fields.join(", "))
            }
            GoExpression::Address(value) => {
                let value = self.expression(value, 6);
                format!("&{value}")
            }
            GoExpression::Conversion { type_, value } => {
                let type_ = self.type_(type_);
                let value = self.expression(value, 0);
                format!("{type_}({value})")
            }
            GoExpression::TypeAssertion { value, type_ } => {
                self.census.assertions += 1;
                let value = self.expression(value, 6);
                let type_ = self.type_(type_);
                format!("{value}.({type_})")
            }
            GoExpression::Type(type_) => self.type_(type_),
            GoExpression::Spread(value) => format!("{}...", self.expression(value, 0)),
            GoExpression::Instantiation { function, arguments } => {
                let function = self.expression(function, 6);
                let arguments: Vec<String> =
                    arguments.iter().map(|argument| self.type_argument(argument)).collect();
                format!("{function}[{}]", arguments.join(", "))
            }
            GoExpression::Function { parameters, result, body } => {
                let signature = self.signature(parameters, result.as_ref());
                let mut rendered = format!("func{signature} {{\n");
                let saved = std::mem::take(&mut self.output);
                self.block(body);
                let inner = std::mem::replace(&mut self.output, saved);
                rendered.push_str(&inner);
                for _ in 0..self.indentation {
                    rendered.push('\t');
                }
                rendered.push('}');
                rendered
            }
        }
    }
}

fn binary_precedence(operator: &str) -> u8 {
    match operator {
        "||" => 1,
        "&&" => 2,
        "==" | "!=" | "<" | "<=" | ">" | ">=" => 3,
        "+" | "-" | "|" | "^" => 4,
        _ => 5,
    }
}

fn go_string(value: &str) -> String {
    let mut rendered = String::from("\"");
    for character in value.chars() {
        match character {
            '"' => rendered.push_str("\\\""),
            '\\' => rendered.push_str("\\\\"),
            '\n' => rendered.push_str("\\n"),
            '\r' => rendered.push_str("\\r"),
            '\t' => rendered.push_str("\\t"),
            character if needs_escape(character) => {
                let _ = write!(rendered, "\\u{:04x}", character as u32);
            }
            character => rendered.push(character),
        }
    }
    rendered.push('"');
    rendered
}

/// Control characters, and the byte order mark, which Go rejects anywhere in a
/// source file but at its start.
fn needs_escape(character: char) -> bool {
    character.is_control() || character == '\u{feff}'
}

fn go_rune(value: char) -> String {
    match value {
        '\'' => "'\\''".into(),
        '\\' => "'\\\\'".into(),
        '\n' => "'\\n'".into(),
        '\t' => "'\\t'".into(),
        character if needs_escape(character) => format!("'\\u{:04x}'", character as u32),
        character => format!("'{character}'"),
    }
}
