use std::fmt::Write;
use std::path::{Component, Path, PathBuf};
use std::sync::Arc;

use rayon::prelude::*;

use super::directives::{
    GO_LINE_PLACEHOLDER, INLINE_DIRECTIVE_MARK, directive, name_go_lines, settle_line_directives,
};
use super::{GoDeclaration, GoDefault, GoExpression, GoStatement, GoType, SourceLine, StructField};
use crate::foreign::LineCoverage;

impl GoDeclaration {
    pub fn render(&self) -> String {
        let mut printer = Printer::default();
        printer.declaration(self);
        printer.output
    }
}

impl GoType {
    /// The type as Go spells it, on one line.
    pub fn render(&self) -> String {
        let mut printer = Printer::default();
        printer.type_argument(self)
    }
}

pub struct GoFile {
    /// The `//go:build` constraint the file builds under, if any.
    pub constraint: Option<&'static str>,
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
    /// The source together with a count of the `any` it contains, by cause.
    pub fn render_with_census(&self) -> (String, crate::erasure::Census) {
        self.render_at(None, LineCoverage::Sparse)
    }

    /// [`Self::render_with_census`] for the file at `path`, whose `//line` directives name the
    /// PureScript relative to the file's directory, and the file itself in front of a
    /// declaration that follows PureScript code and comes from none itself, so that Go
    /// attributes that declaration to the Go file again. With [`LineCoverage::Every`] every
    /// statement and declaration names its line, the Go file's own for those from no PureScript.
    pub fn render_at(
        &self,
        path: Option<&Path>,
        coverage: LineCoverage,
    ) -> (String, crate::erasure::Census) {
        let directory = path.map(|path| Arc::from(path.parent().unwrap_or(Path::new(""))));
        let file_name = path.and_then(Path::file_name).map(|name| name.to_string_lossy());
        let mut printer = Printer::default();
        if let Some(constraint) = self.constraint {
            let _ = writeln!(printer.output, "//go:build {constraint}\n");
        }
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
                let every = coverage == LineCoverage::Every && file_name.is_some();
                let mut printer =
                    Printer { directory: directory.clone(), every, ..Printer::default() };
                printer.output.push('\n');
                printer.declaration(declaration);
                (printer.output, printer.census)
            })
            .collect();
        for (output, census) in rendered {
            printer.output.push_str(&output);
            printer.census.absorb(census);
        }
        match (file_name, coverage) {
            (Some(file_name), LineCoverage::Sparse) => {
                (settle_line_directives(&printer.output, &file_name), printer.census)
            }
            (Some(file_name), LineCoverage::Every) => {
                (name_go_lines(&printer.output, &file_name), printer.census)
            }
            (None, _) => (printer.output, printer.census),
        }
    }
}

#[derive(Default)]
struct Printer {
    output: String,
    indentation: usize,
    census: crate::erasure::Census,
    /// The PureScript line the statements being printed come from.
    attribution: Option<SourceLine>,
    /// Whether the emitter put the attribution in front of the next statement; any other
    /// statement is named only where it does work, which a trace or a profile shows.
    placed: bool,
    /// The directory of the Go file, which directives name the PureScript relative to.
    directory: Option<Arc<Path>>,
    /// Whether every statement and declaration names its line, as [`LineCoverage::Every`] says.
    every: bool,
    /// Whether the statement being printed is the last one of a function that returns nothing,
    /// where a `return` says nothing.
    ends_procedure: bool,
    member_lines: Vec<(String, SourceLine)>,
}

impl Printer {
    /// Names the line the next statement comes from: [`settle_line_directives`] leaves out the
    /// directives that name the line Go would count to anyway.
    fn name_attribution(&mut self) {
        let Some(SourceLine { path, line, column }) = &self.attribution else { return };
        let shown = self.shown_path(path);
        let _ = writeln!(self.output, "//line {shown}:{line}:{column}");
    }

    fn shown_path(&self, path: &str) -> String {
        let shown = match &self.directory {
            Some(directory) => relative_path(directory, Path::new(path)),
            None => PathBuf::from(path),
        };
        shown.to_string_lossy().replace('\\', "/")
    }

    fn inline_directive(&self, line: Option<&SourceLine>) -> String {
        match line {
            Some(SourceLine { path, line, column }) => {
                format!("{INLINE_DIRECTIVE_MARK}/*line {}:{line}:{column}*/", self.shown_path(path))
            }
            None => format!("{INLINE_DIRECTIVE_MARK}/*line */"),
        }
    }

    fn attributes_elsewhere(&self, line: &SourceLine) -> bool {
        self.every
            && self.attribution.as_ref().is_none_or(|attribution| {
                attribution.path != line.path || attribution.line != line.line
            })
    }

    /// Names the line the next statement or declaration comes from, or with none the Go file's
    /// own line, which [`name_go_lines`] fills in.
    fn name_every_line(&mut self) {
        match self.attribution {
            Some(_) => self.name_attribution(),
            None => self.output.push_str(GO_LINE_PLACEHOLDER),
        }
    }

    fn branch_line(&mut self, text: &str, line: Option<&SourceLine>) {
        let enclosing = self.attribution.clone();
        if self.every
            && let Some(line) = line
        {
            self.attribution = Some(line.clone());
        }
        self.line(text);
        self.attribution = enclosing;
    }

    fn line(&mut self, text: &str) {
        if self.every {
            return self.named_lines(text);
        }
        for _ in 0..self.indentation {
            self.output.push('\t');
        }
        self.output.push_str(text);
        self.output.push('\n');
    }

    fn named_lines(&mut self, text: &str) {
        for (index, segment) in text.split('\n').enumerate() {
            if directive(segment).is_none() && segment != GO_LINE_PLACEHOLDER.trim_end() {
                if !self.follows_directive() {
                    self.name_every_line();
                }
                if index == 0 {
                    for _ in 0..self.indentation {
                        self.output.push('\t');
                    }
                }
            }
            self.output.push_str(segment);
            self.output.push('\n');
        }
    }

    fn follows_directive(&self) -> bool {
        let Some(written) = self.output.strip_suffix('\n') else { return false };
        let last = written.rsplit('\n').next().unwrap_or(written);
        directive(last).is_some() || last == GO_LINE_PLACEHOLDER.trim_end()
    }

    fn declaration(&mut self, declaration: &GoDeclaration) {
        if self.every {
            self.attribution = match declaration {
                GoDeclaration::Function { body, .. } => match body.first() {
                    Some(GoStatement::Line(line)) => Some(line.clone()),
                    _ => None,
                },
                GoDeclaration::Type { line, .. }
                | GoDeclaration::Alias { line, .. }
                | GoDeclaration::Constants { line, .. }
                | GoDeclaration::Variable { line, .. }
                | GoDeclaration::Written { line, .. } => line.clone(),
                _ => None,
            };
            self.name_every_line();
        }
        match declaration {
            GoDeclaration::Source { name, template } => {
                self.output.push_str(&template.replace("{name}", name));
            }
            GoDeclaration::Written { source, line: Some(_), .. } if self.every => {
                self.named_lines(source.strip_suffix('\n').unwrap_or(source))
            }
            GoDeclaration::Written { source, .. } => self.output.push_str(source),
            GoDeclaration::Type { name, type_, member_lines, .. } => {
                if self.every {
                    self.member_lines = member_lines.clone();
                }
                let rendered = self.type_(type_);
                self.member_lines.clear();
                self.line(&format!("type {name} {rendered}"));
            }
            GoDeclaration::Alias { name, type_, .. } => {
                let rendered = self.type_(type_);
                self.line(&format!("type {name} = {rendered}"));
            }
            GoDeclaration::GenericType { name, parameter, type_ } => {
                let rendered = self.type_(type_);
                self.line(&format!("type {name}[{parameter} any] {rendered}"));
            }
            GoDeclaration::Constants { type_name, names, member_lines, .. } => {
                self.line("const (");
                self.indentation += 1;
                let declared = self.attribution.clone();
                for (position, name) in names.iter().enumerate() {
                    let member = member_lines.iter().find(|(member, _)| member == name);
                    self.attribution = match member {
                        Some((_, line)) => Some(line.clone()),
                        None => declared.clone(),
                    };
                    if position == 0 {
                        match type_name {
                            Some(type_name) => self.line(&format!("{name} {type_name} = iota")),
                            None => self.line(&format!("{name} = iota")),
                        }
                    } else {
                        self.line(name);
                    }
                }
                self.attribution = declared;
                self.indentation -= 1;
                self.line(")");
            }
            GoDeclaration::Constant { name, type_, value } => {
                let value = self.expression(value, 0);
                match type_ {
                    Some(type_) => {
                        let type_ = self.type_(type_);
                        self.line(&format!("const {name} {type_} = {value}"));
                    }
                    None => self.line(&format!("const {name} = {value}")),
                }
            }
            GoDeclaration::Variable { name, type_, value, .. } => {
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
                if let (false, Some(GoStatement::Line(line))) = (self.every, body.first()) {
                    self.attribution = Some(line.clone());
                    self.name_attribution();
                }
                let signature = self.signature(parameters, result.as_ref());
                self.line(&format!("func {name}{signature} {{"));
                self.procedure_body(body, result.is_none());
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

    fn procedure_body(&mut self, statements: &[GoStatement], returns_nothing: bool) {
        let enclosing = std::mem::replace(&mut self.ends_procedure, returns_nothing);
        self.block(statements);
        self.ends_procedure = enclosing;
    }

    fn block(&mut self, statements: &[GoStatement]) {
        let enclosing = self.attribution.clone();
        let ends_procedure = std::mem::take(&mut self.ends_procedure);
        let last =
            statements.iter().rposition(|statement| !matches!(statement, GoStatement::Line(_)));
        self.indentation += 1;
        for (position, statement) in statements.iter().enumerate() {
            self.ends_procedure = ends_procedure && Some(position) == last;
            self.statement(statement);
        }
        self.ends_procedure = ends_procedure;
        self.indentation -= 1;
        self.attribution = enclosing;
    }

    fn statement(&mut self, statement: &GoStatement) {
        let ends_procedure = std::mem::take(&mut self.ends_procedure);
        if ends_procedure && matches!(statement, GoStatement::Return(None)) {
            return;
        }
        if let GoStatement::Line(line) = statement {
            self.attribution = Some(line.clone());
            self.placed = true;
            return;
        }
        // A loop does nothing of its own: the statements in it name their lines.
        let looping = matches!(statement, GoStatement::Loop(_) | GoStatement::LabeledLoop { .. });
        if self.every {
            self.name_every_line();
        } else if (std::mem::take(&mut self.placed) && !looping) || statement.does_work() {
            self.name_attribution();
        }
        match statement {
            GoStatement::Line(_) => {}
            GoStatement::Define { names, values } => {
                let depth = if names.len() > 1 && values.len() > 1 { 2 } else { 1 };
                let values: Vec<String> =
                    values.iter().map(|value| self.expression_at(value, 0, depth)).collect();
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
                if let ([target], [value]) = (targets.as_slice(), values.as_slice())
                    && let GoExpression::Binary { operator, left, right } = value.unattributed()
                    && COMPOUND_OPERATORS.contains(operator)
                    && is_plain_place(target)
                    && same_place(target, left)
                {
                    let target = self.expression(target, 0);
                    let right = match value {
                        GoExpression::Attributed { line, .. } => self.attributed(line, right, 0, 1),
                        _ => self.expression(right, 0),
                    };
                    self.line(&format!("{target} {operator}= {right}"));
                    return;
                }
                let depth = if targets.len() > 1 && values.len() > 1 { 2 } else { 1 };
                let targets: Vec<String> =
                    targets.iter().map(|target| self.expression_at(target, 0, depth)).collect();
                let values: Vec<String> =
                    values.iter().map(|value| self.expression_at(value, 0, depth)).collect();
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
                self.ends_procedure = ends_procedure;
                self.block(then);
                self.ends_procedure = ends_procedure;
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
                    self.branch_line(&format!("case {}:", values.join(", ")), case.line.as_ref());
                    self.ends_procedure = ends_procedure;
                    self.block(&case.body);
                }
                if let Some(GoDefault { covers, body, line }) = default {
                    if covers.is_empty() {
                        self.branch_line("default:", line.as_ref());
                    } else {
                        let covers: Vec<String> =
                            covers.iter().map(|value| self.expression(value, 0)).collect();
                        let text = format!("default: // {}", covers.join(", "));
                        self.branch_line(&text, line.as_ref());
                    }
                    self.ends_procedure = ends_procedure;
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
        }
    }

    fn else_chain(&mut self, otherwise: &[GoStatement]) {
        let ends_procedure = std::mem::take(&mut self.ends_procedure);
        match otherwise {
            otherwise
                if otherwise.iter().all(|statement| matches!(statement, GoStatement::Line(_))) =>
            {
                self.line("}")
            }
            [GoStatement::If { condition, then, otherwise }] => {
                if self.every {
                    self.name_every_line();
                }
                let condition = self.expression(condition, 0);
                self.line(&format!("}} else if {condition} {{"));
                self.ends_procedure = ends_procedure;
                self.block(then);
                self.ends_procedure = ends_procedure;
                self.else_chain(otherwise);
            }
            [GoStatement::Line(line), chained @ GoStatement::If { .. }] => {
                let enclosing = self.attribution.replace(line.clone());
                if !self.every {
                    self.name_attribution();
                }
                self.ends_procedure = ends_procedure;
                self.else_chain(std::slice::from_ref(chained));
                self.attribution = enclosing;
            }
            _ => {
                let line = match otherwise.first() {
                    Some(GoStatement::Line(line)) => Some(line),
                    _ => None,
                };
                self.branch_line("} else {", line);
                self.ends_procedure = ends_procedure;
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
            GoType::Map(key, value) => format!("map[{}]{}", self.type_(key), self.type_(value)),
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
                let width =
                    fields.iter().map(|field| field.name.chars().count()).max().unwrap_or(0);
                let member_lines = std::mem::take(&mut self.member_lines);
                let field_types: Vec<String> =
                    fields.iter().map(|field| self.type_(&field.type_)).collect();
                let type_widths = tagged_type_widths(fields, &field_types);
                let rows = fields.iter().zip(&field_types).zip(type_widths);
                for ((field, field_type), type_width) in rows {
                    if let Some((_, SourceLine { path, line, column })) =
                        member_lines.iter().find(|(member, _)| *member == field.name)
                    {
                        let shown = self.shown_path(path);
                        let _ = writeln!(rendered, "//line {shown}:{line}:{column}");
                    }
                    for _ in 0..=self.indentation {
                        rendered.push('\t');
                    }
                    let name = &field.name;
                    match &field.label {
                        Some(label) => {
                            let tag = struct_tag(label);
                            let _ =
                                writeln!(rendered, "{name:width$} {field_type:type_width$} {tag}");
                        }
                        None => {
                            let _ = writeln!(rendered, "{name:width$} {field_type}");
                        }
                    }
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
            GoType::Results(results) => {
                let results: Vec<String> =
                    results.iter().map(|result| self.type_(result)).collect();
                format!("({})", results.join(", "))
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
        self.expression_at(expression, parent_precedence, 1)
    }

    /// An expression `depth` levels into the list it is part of, which decides, as it does for
    /// `gofmt`, which binary operators get blanks around them: `f(a+b, c)` but `x := a + b`.
    fn expression_at(
        &mut self,
        expression: &GoExpression,
        parent_precedence: u8,
        depth: usize,
    ) -> String {
        match expression {
            GoExpression::Identifier(name) => name.clone(),
            GoExpression::Qualified { package, name } => format!("{package}.{name}"),
            GoExpression::Integer(value) => value.to_string(),
            GoExpression::Float(value) => value.clone(),
            GoExpression::String(value) => go_string(value),
            GoExpression::Utf16(units) => go_utf16_string(units),
            GoExpression::Rune(value) => go_rune(*value),
            GoExpression::Boolean(value) => value.to_string(),
            GoExpression::Call { function, arguments } => {
                let depth = if arguments.len() > 1 { depth + 1 } else { depth };
                let function = self.expression_at(function, 6, depth);
                let arguments: Vec<String> = arguments
                    .iter()
                    .map(|argument| self.expression_at(argument, 0, depth))
                    .collect();
                format!("{function}({})", arguments.join(", "))
            }
            GoExpression::Binary { operator, left, right } => {
                let precedence = binary_precedence(operator);
                let parenthesised = precedence < parent_precedence;
                let depth = if parenthesised { depth.saturating_sub(1).max(1) } else { depth };
                let blank = precedence < binary_cutoff(expression, depth);
                let left_depth = match left.unattributed() {
                    GoExpression::Binary { operator, .. }
                        if binary_precedence(operator) == precedence =>
                    {
                        depth
                    }
                    _ => depth + 1,
                };
                let left = self.expression_at(left, precedence, left_depth);
                let right = self.expression_at(right, precedence + 1, depth + 1);
                let rendered = if blank {
                    format!("{left} {operator} {right}")
                } else {
                    format!("{left}{operator}{right}")
                };
                if parenthesised { format!("({rendered})") } else { rendered }
            }
            GoExpression::Unary { operator, operand } => {
                let operand = self.expression_at(operand, 6, depth);
                let rendered = format!("{operator}{operand}");
                if parent_precedence > 5 { format!("({rendered})") } else { rendered }
            }
            GoExpression::Field { value, name } => {
                // A composite literal is ambiguous in if/for/switch headers.
                let composite = matches!(value.unattributed(), GoExpression::Composite { .. });
                let value = self.expression_at(value, 6, depth);
                if composite {
                    return format!("({value}).{name}");
                }
                format!("{value}.{name}")
            }
            GoExpression::Index { value, index } => {
                let value = self.expression_at(value, 6, 1);
                let index = self.expression_at(index, 0, depth + 1);
                format!("{value}[{index}]")
            }
            GoExpression::Slice { value, low, high } => {
                let value = self.expression_at(value, 6, 1);
                let mut bound = |bound: &Option<Box<GoExpression>>| match bound {
                    Some(bound) => self.expression_at(bound, 0, depth + 1),
                    None => String::new(),
                };
                let (low, high) = (bound(low), bound(high));
                format!("{value}[{low}:{high}]")
            }
            GoExpression::Composite { type_, fields } => {
                let rendered = self.type_(type_);
                format!("{rendered}{}", self.composite_fields(type_, fields))
            }
            GoExpression::Address(value) => {
                let value = self.expression_at(value, 6, depth);
                format!("&{value}")
            }
            GoExpression::Conversion { type_, value } => {
                let rendered = self.type_(type_);
                let value = self.expression_at(value, 0, depth);
                match type_ {
                    GoType::Pointer(_) | GoType::Function { .. } => {
                        format!("({rendered})({value})")
                    }
                    _ => format!("{rendered}({value})"),
                }
            }
            GoExpression::TypeAssertion { value, type_ } => {
                self.census.assertions += 1;
                let value = self.expression_at(value, 6, depth);
                let type_ = self.type_(type_);
                format!("{value}.({type_})")
            }
            GoExpression::Type(type_) => self.type_(type_),
            GoExpression::Spread(value) => format!("{}...", self.expression_at(value, 0, depth)),
            GoExpression::Instantiation { function, arguments } => {
                let function = self.expression_at(function, 6, depth);
                let arguments: Vec<String> =
                    arguments.iter().map(|argument| self.type_argument(argument)).collect();
                format!("{function}[{}]", arguments.join(", "))
            }
            GoExpression::Function { parameters, result, body } => {
                let signature = self.signature(parameters, result.as_ref());
                let mut rendered = format!("func{signature} {{\n");
                let saved = std::mem::take(&mut self.output);
                self.procedure_body(body, result.is_none());
                let inner = std::mem::replace(&mut self.output, saved);
                rendered.push_str(&inner);
                for _ in 0..self.indentation {
                    rendered.push('\t');
                }
                rendered.push('}');
                rendered
            }
            GoExpression::Attributed { line, value } => {
                self.attributed(line, value, parent_precedence, depth)
            }
            GoExpression::Results(values) => {
                let depth = if values.len() > 1 { depth + 1 } else { depth };
                let values: Vec<String> =
                    values.iter().map(|value| self.expression_at(value, 0, depth)).collect();
                values.join(", ")
            }
        }
    }

    fn attributed(
        &mut self,
        line: &SourceLine,
        value: &GoExpression,
        parent_precedence: u8,
        depth: usize,
    ) -> String {
        if !self.attributes_elsewhere(line) {
            return self.expression_at(value, parent_precedence, depth);
        }
        let opening = self.inline_directive(Some(line));
        let enclosing = self.attribution.replace(line.clone());
        let value = self.expression_at(value, parent_precedence, depth);
        self.attribution = enclosing;
        let closing = self.inline_directive(self.attribution.as_ref());
        format!("{opening}{value}{closing}")
    }

    /// The braces and fields of a composite literal of `type_`. The elements of a slice leave out
    /// the type `gofmt -s` leaves out: `[]T{{...}}` and `[]*T{{...}}` rather than `[]T{T{...}}`
    /// and `[]*T{&T{...}}`.
    fn composite_fields(
        &mut self,
        type_: &GoType,
        fields: &[(Option<String>, GoExpression)],
    ) -> String {
        let element_type = match type_ {
            GoType::Slice(element) => Some(element.as_ref()),
            _ => None,
        };
        let fields: Vec<String> = fields
            .iter()
            .map(|(name, value)| match (name, element_type) {
                (Some(name), _) => format!("{name}: {}", self.expression(value, 0)),
                (None, Some(element_type)) => self.element(value, element_type),
                (None, None) => self.expression(value, 0),
            })
            .collect();
        format!("{{{}}}", fields.join(", "))
    }

    fn element(&mut self, value: &GoExpression, element_type: &GoType) -> String {
        match (value, element_type) {
            (GoExpression::Composite { type_, fields }, _) if type_ == element_type => {
                self.composite_fields(type_, fields)
            }
            (GoExpression::Address(pointed), GoType::Pointer(pointee)) => match pointed.as_ref() {
                GoExpression::Composite { type_, fields } if type_ == pointee.as_ref() => {
                    self.composite_fields(type_, fields)
                }
                _ => self.expression(value, 0),
            },
            _ => self.expression(value, 0),
        }
    }
}

/// The lowest precedence whose operators `gofmt` prints without blanks in `expression`, a binary
/// expression `depth` levels into its list: the operators that bind tighter than the loosest
/// one lose their blanks, `a + b*c`, and inside an argument list every `+` and `*` does.
fn binary_cutoff(expression: &GoExpression, depth: usize) -> u8 {
    let (has_sums, has_products, problem) = walk_binary(expression);
    if problem > 0 {
        return problem + 1;
    }
    match (has_sums && has_products, depth == 1) {
        (true, true) => 5,
        (true, false) => 4,
        (false, true) => 6,
        (false, false) => 4,
    }
}

/// Whether the operands of `expression` that print without parentheses use precedence 4 or 5,
/// and the precedence below which blanks must stay to keep `a / *p` or `a - -b` from reading as
/// a comment or a decrement.
fn walk_binary(expression: &GoExpression) -> (bool, bool, u8) {
    let GoExpression::Binary { operator, left, right } = expression.unattributed() else {
        return (false, false, 0);
    };
    let precedence = binary_precedence(operator);
    let mut has_sums = precedence == 4;
    let mut has_products = precedence == 5;
    let mut problem = 0;
    let mut absorb = |operand: &GoExpression| {
        let (sums, products, operand_problem) = walk_binary(operand);
        has_sums |= sums;
        has_products |= products;
        problem = problem.max(operand_problem);
    };
    if let GoExpression::Binary { operator: left_operator, .. } = left.unattributed()
        && binary_precedence(left_operator) >= precedence
    {
        absorb(left);
    }
    match right.unattributed() {
        GoExpression::Binary { operator: right_operator, .. }
            if binary_precedence(right_operator) > precedence =>
        {
            absorb(right)
        }
        GoExpression::Unary { operator: unary, .. } => match (*operator, *unary) {
            ("/", "*") | ("&", "&") | ("&", "^") => problem = 5,
            ("+", "+") | ("-", "-") => problem = problem.max(4),
            _ => {}
        },
        GoExpression::Address(_) if *operator == "&" => problem = 5,
        _ => {}
    }
    (has_sums, has_products, problem)
}

/// The operators Go has an assignment form of, `x += y` for `x = x + y`.
const COMPOUND_OPERATORS: [&str; 10] = ["+", "-", "*", "/", "%", "&", "|", "^", "<<", ">>"];

/// A variable, or a field or element of one at a constant or variable index: a place whose
/// address works out the same however often Go evaluates it, so `x = x + y` and `x += y`,
/// which evaluates it once, do the same.
fn is_plain_place(place: &GoExpression) -> bool {
    match place {
        GoExpression::Identifier(_) => true,
        GoExpression::Field { value, .. } => is_plain_place(value),
        GoExpression::Index { value, index } => {
            is_plain_place(value)
                && matches!(index.as_ref(), GoExpression::Identifier(_) | GoExpression::Integer(_))
        }
        _ => false,
    }
}

fn same_place(place: &GoExpression, other: &GoExpression) -> bool {
    match (place, other) {
        (GoExpression::Identifier(left), GoExpression::Identifier(right)) => left == right,
        (GoExpression::Integer(left), GoExpression::Integer(right)) => left == right,
        (
            GoExpression::Field { value: left, name: left_name },
            GoExpression::Field { value: right, name: right_name },
        ) => left_name == right_name && same_place(left, right),
        (
            GoExpression::Index { value: left, index: left_index },
            GoExpression::Index { value: right, index: right_index },
        ) => same_place(left, right) && same_place(left_index, right_index),
        _ => false,
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

fn tagged_type_widths(fields: &[StructField], field_types: &[String]) -> Vec<usize> {
    let mut widths = vec![0; fields.len()];
    let mut start = 0;
    while start < fields.len() {
        if fields[start].label.is_none() {
            start += 1;
            continue;
        }
        let end = (start..fields.len()).find(|&index| fields[index].label.is_none());
        let end = end.unwrap_or(fields.len());
        let width = field_types[start..end].iter().map(|type_| type_.chars().count()).max();
        widths[start..end].fill(width.unwrap_or(0));
        start = end;
    }
    widths
}

fn struct_tag(label: &str) -> String {
    let tag = format!("purescript:{}", go_string(label));
    if tag.contains('`') { go_string(&tag) } else { format!("`{tag}`") }
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

/// A Go string literal of UTF-16 code units: each lone surrogate as the three bytes of its WTF-8
/// encoding, everything else as `go_string` writes it.
fn go_utf16_string(units: &[u16]) -> String {
    let mut rendered = String::from("\"");
    for decoded in char::decode_utf16(units.iter().copied()) {
        match decoded {
            Ok(character) => {
                let quoted = go_string(character.encode_utf8(&mut [0; 4]));
                rendered.push_str(&quoted[1..quoted.len() - 1]);
            }
            Err(error) => {
                let unit = error.unpaired_surrogate();
                let bytes = [0xED, 0x80 | ((unit >> 6) & 0x3F) as u8, 0x80 | (unit & 0x3F) as u8];
                for byte in bytes {
                    let _ = write!(rendered, "\\x{byte:02x}");
                }
            }
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

/// `path` as seen from `directory`, both absolute or both relative to the same directory.
fn relative_path(directory: &Path, path: &Path) -> PathBuf {
    let directory: Vec<Component> = directory.components().collect();
    let path: Vec<Component> = path.components().collect();
    let common = directory.iter().zip(&path).take_while(|(left, right)| left == right).count();
    // Two trees that share no more than the root are named absolutely.
    if directory
        .first()
        .is_some_and(|first| matches!(first, Component::RootDir | Component::Prefix(_)))
        && common <= 1 + usize::from(matches!(directory.first(), Some(Component::Prefix(_))))
    {
        return path.iter().collect();
    }
    let mut relative = PathBuf::new();
    for _ in common..directory.len() {
        relative.push("..");
    }
    path[common..].iter().for_each(|component| relative.push(component));
    relative
}
