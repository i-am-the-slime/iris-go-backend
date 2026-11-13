//! A small Go syntax tree with a printer that follows `gofmt` layout.

use std::fmt::Write;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum GoType {
    Named(String),
    Int,
    Float64,
    Bool,
    Rune,
    String,
    EmptyStruct,
    Any,
    Slice(Box<GoType>),
    Pointer(Box<GoType>),
    Function { parameters: Vec<GoType>, result: Option<Box<GoType>> },
    Struct(Vec<(String, GoType)>),
}

#[derive(Debug, Clone)]
pub enum GoExpression {
    Identifier(String),
    Qualified { package: &'static str, name: String },
    Integer(i64),
    Float(String),
    String(String),
    Rune(char),
    Boolean(bool),
    Call { function: Box<GoExpression>, arguments: Vec<GoExpression> },
    Binary { operator: &'static str, left: Box<GoExpression>, right: Box<GoExpression> },
    Unary { operator: &'static str, operand: Box<GoExpression> },
    Field { value: Box<GoExpression>, name: String },
    Index { value: Box<GoExpression>, index: Box<GoExpression> },
    Composite { type_: GoType, fields: Vec<(Option<String>, GoExpression)> },
    Address(Box<GoExpression>),
    Conversion { type_: GoType, value: Box<GoExpression> },
    Function { parameters: Vec<(String, GoType)>, result: Option<GoType>, body: Vec<GoStatement> },
}

#[derive(Debug, Clone)]
pub enum GoStatement {
    Define { names: Vec<String>, values: Vec<GoExpression> },
    Variable { name: String, type_: GoType, value: Option<GoExpression> },
    Assign { targets: Vec<GoExpression>, values: Vec<GoExpression> },
    Expression(GoExpression),
    Return(Option<GoExpression>),
    If { condition: GoExpression, then: Vec<GoStatement>, otherwise: Vec<GoStatement> },
    Switch { value: Option<GoExpression>, cases: Vec<GoCase>, default: Option<Vec<GoStatement>> },
    Loop(Vec<GoStatement>),
    Range { element: String, iterable: GoExpression, body: Vec<GoStatement> },
    Continue,
    Block(Vec<GoStatement>),
}

#[derive(Debug, Clone)]
pub struct GoCase {
    pub values: Vec<GoExpression>,
    pub body: Vec<GoStatement>,
}

#[derive(Debug, Clone)]
pub enum GoDeclaration {
    /// Fixed support code that generated programs share.
    Source(&'static str),
    Type {
        name: String,
        type_: GoType,
    },
    Constants {
        type_name: Option<String>,
        names: Vec<String>,
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

pub struct GoFile {
    pub imports: Vec<&'static str>,
    pub declarations: Vec<GoDeclaration>,
}

impl GoFile {
    pub fn render(&self) -> String {
        let mut printer = Printer { output: String::new(), indentation: 0 };
        printer.output.push_str("package main\n");
        if !self.imports.is_empty() {
            printer.output.push_str("\nimport (\n");
            for import in &self.imports {
                let _ = writeln!(printer.output, "\t\"{import}\"");
            }
            printer.output.push_str(")\n");
        }
        for declaration in &self.declarations {
            printer.output.push('\n');
            printer.declaration(declaration);
        }
        printer.output
    }
}

struct Printer {
    output: String,
    indentation: usize,
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
            GoDeclaration::Source(source) => self.output.push_str(source),
            GoDeclaration::Type { name, type_ } => {
                let rendered = self.type_(type_);
                self.line(&format!("type {name} {rendered}"));
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
                if let Some(default) = default {
                    self.line("default:");
                    self.block(default);
                }
                self.line("}");
            }
            GoStatement::Loop(body) => {
                self.line("for {");
                self.block(body);
                self.line("}");
            }
            GoStatement::Range { element, iterable, body } => {
                let iterable = self.expression(iterable, 0);
                self.line(&format!("for _, {element} := range {iterable} {{"));
                self.block(body);
                self.line("}");
            }
            GoStatement::Continue => self.line("continue"),
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
            GoType::Any => "any".into(),
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
        }
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
                let value = self.expression(value, 6);
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
            character if character.is_control() => {
                let _ = write!(rendered, "\\u{:04x}", character as u32);
            }
            character => rendered.push(character),
        }
    }
    rendered.push('"');
    rendered
}

fn go_rune(value: char) -> String {
    match value {
        '\'' => "'\\''".into(),
        '\\' => "'\\\\'".into(),
        '\n' => "'\\n'".into(),
        '\t' => "'\\t'".into(),
        character if character.is_control() => format!("'\\u{:04x}'", character as u32),
        character => format!("'{character}'"),
    }
}
