//! Rendering of the simplified monomorphic tree as Go.
//!
//! Values of type `Effect a` are Go `func() A`, and a function `a -> Effect b` is a
//! Go `func(A) B` that performs its effects when called. Effectful code is emitted
//! in perform mode, where binds become statements and `pure x` becomes `x`; an
//! effect only turns into a closure where it is used as a first-class value.

use std::collections::BTreeSet;

use rustc_hash::{FxHashMap, FxHashSet};

use crate::context::{Context, capitalise};
use crate::error::{GoError, GoResult};
use crate::foreign::{Comparison, Foreign, Operator};
use crate::mono::{
    Alternative, Binding, Expression, ExpressionKind, Function, FunctionId, Guard, Guarded,
    Literal, Local, LocalId, Pattern, PatternKind, Program, RecordUpdate,
};
use crate::monotype::{DataType, Monotype, MonotypeId, Monotypes};
use crate::simplify::visit;
use crate::syntax::{GoCase, GoDeclaration, GoExpression, GoFile, GoStatement, GoType};

pub fn emit_program<Q>(
    program: &Program,
    monotypes: &mut Monotypes,
    queries: &Q,
) -> GoResult<String>
where
    Q: checking::ExternalQueries,
{
    let mut emitter = Emitter {
        program,
        monotypes,
        context: Context::new(queries),
        imports: BTreeSet::new(),
        function_names: vec![],
        global_names: FxHashSet::default(),
        record_names: FxHashMap::default(),
        data_layouts: FxHashMap::default(),
        type_declarations: vec![],
        reference_declared: false,
        range_declared: false,
        locals: FxHashMap::default(),
        local_names: FxHashSet::default(),
        tail_loop: None,
        current: None,
    };
    emitter.assign_function_names();
    let mut declarations = vec![];
    for index in 0..program.functions.len() {
        declarations.extend(emitter.function(FunctionId(index as u32))?);
    }
    declarations.extend(emitter.main()?);
    let mut all = std::mem::take(&mut emitter.type_declarations);
    all.extend(declarations);
    let file = GoFile { imports: emitter.imports.into_iter().collect(), declarations: all };
    Ok(file.render())
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Mode {
    Value,
    Perform,
}

#[derive(Clone)]
enum Sink {
    Return,
    Assign(String),
    Define(String),
    Discard,
}

struct TailLoop {
    function: FunctionId,
    parameters: Vec<String>,
}

#[derive(Clone)]
struct DataLayout {
    name: String,
    kind: DataKind,
    constructors: Vec<ConstructorLayout>,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum DataKind {
    Enumeration,
    Tagged,
    Product,
}

#[derive(Clone)]
struct ConstructorLayout {
    tag: String,
    fields: Vec<(String, MonotypeId)>,
}

struct Emitter<'p, 'm, 'q, Q> {
    program: &'p Program,
    monotypes: &'m mut Monotypes,
    context: Context<'q, Q>,
    imports: BTreeSet<&'static str>,
    function_names: Vec<String>,
    global_names: FxHashSet<String>,
    record_names: FxHashMap<MonotypeId, String>,
    data_layouts: FxHashMap<DataType, DataLayout>,
    type_declarations: Vec<GoDeclaration>,
    reference_declared: bool,
    range_declared: bool,
    locals: FxHashMap<LocalId, GoExpression>,
    local_names: FxHashSet<String>,
    tail_loop: Option<TailLoop>,
    current: Option<FunctionId>,
}

const RESERVED: &[&str] = &[
    "break",
    "case",
    "chan",
    "const",
    "continue",
    "default",
    "defer",
    "else",
    "fallthrough",
    "for",
    "func",
    "go",
    "goto",
    "if",
    "import",
    "interface",
    "map",
    "package",
    "range",
    "return",
    "select",
    "struct",
    "switch",
    "type",
    "var",
    "append",
    "bool",
    "byte",
    "cap",
    "clear",
    "close",
    "complex",
    "copy",
    "delete",
    "error",
    "false",
    "float64",
    "imag",
    "int",
    "int32",
    "iota",
    "len",
    "make",
    "max",
    "min",
    "new",
    "nil",
    "panic",
    "print",
    "println",
    "real",
    "recover",
    "rune",
    "string",
    "true",
    "any",
    "main",
    "init",
    "fmt",
    "prim",
    "array",
    "Ref",
];

fn identifier(name: &str) -> String {
    let mut sanitized: String = name
        .chars()
        .map(
            |character| {
                if character.is_alphanumeric() || character == '_' { character } else { '_' }
            },
        )
        .collect();
    if sanitized.is_empty() || sanitized.starts_with(|character: char| character.is_ascii_digit()) {
        sanitized.insert(0, '_');
    }
    if RESERVED.contains(&sanitized.as_str()) {
        sanitized.push('_');
    }
    sanitized
}

fn unique(base: String, taken: &mut FxHashSet<String>) -> String {
    if taken.insert(base.clone()) {
        return base;
    }
    let mut counter = 2;
    loop {
        let candidate = format!("{base}{counter}");
        if taken.insert(candidate.clone()) {
            return candidate;
        }
        counter += 1;
    }
}

fn call(function: GoExpression, arguments: Vec<GoExpression>) -> GoExpression {
    GoExpression::Call { function: Box::new(function), arguments }
}

fn identifier_expression(name: &str) -> GoExpression {
    GoExpression::Identifier(name.to_string())
}

fn field(value: GoExpression, name: &str) -> GoExpression {
    GoExpression::Field { value: Box::new(value), name: name.to_string() }
}

fn binary(operator: &'static str, left: GoExpression, right: GoExpression) -> GoExpression {
    GoExpression::Binary { operator, left: Box::new(left), right: Box::new(right) }
}

fn unit_value() -> GoExpression {
    GoExpression::Composite { type_: GoType::EmptyStruct, fields: vec![] }
}

fn panic_statement(message: &str) -> GoStatement {
    GoStatement::Expression(call(
        identifier_expression("panic"),
        vec![GoExpression::String(message.to_string())],
    ))
}

fn conjunction(tests: Vec<GoExpression>) -> Option<GoExpression> {
    tests.into_iter().reduce(|left, right| binary("&&", left, right))
}

fn is_simple(expression: &GoExpression) -> bool {
    if let GoExpression::Composite { fields, .. } = expression {
        return fields.is_empty();
    }
    matches!(
        expression,
        GoExpression::Identifier(_)
            | GoExpression::Integer(_)
            | GoExpression::Float(_)
            | GoExpression::String(_)
            | GoExpression::Rune(_)
            | GoExpression::Boolean(_)
    ) || matches!(expression, GoExpression::Field { value, .. } if is_simple(value))
}

fn is_effectful_call(expression: &GoExpression) -> bool {
    match expression {
        GoExpression::Call { function, .. } => {
            !matches!(function.as_ref(), GoExpression::Identifier(name) if name == "len")
        }
        GoExpression::Conversion { value, .. } => is_effectful_call(value),
        _ => false,
    }
}

fn uses_local(expression: &Expression, local: LocalId) -> bool {
    let mut found = false;
    visit(expression, &mut |node| {
        if let ExpressionKind::Local(id) = node.kind
            && id == local
        {
            found = true;
        }
    });
    found
}

fn path_root(path: &GoExpression) -> Option<&String> {
    match path {
        GoExpression::Identifier(name) => Some(name),
        GoExpression::Field { value, .. } => path_root(value),
        _ => None,
    }
}

fn local_uses(expression: &Expression, local: LocalId) -> usize {
    let mut uses = 0;
    visit(expression, &mut |node| {
        if let ExpressionKind::Local(id) = node.kind
            && id == local
        {
            uses += 1;
        }
    });
    uses
}

fn guarded_local_uses(guarded: &Guarded, local: LocalId) -> usize {
    match guarded {
        Guarded::Unconditional(body) => local_uses(body, local),
        Guarded::Guards(branches) => branches
            .iter()
            .map(|branch| {
                let guards: usize = branch
                    .guards
                    .iter()
                    .map(|guard| match guard {
                        Guard::Boolean(condition) => local_uses(condition, local),
                        Guard::Pattern { value, .. } => local_uses(value, local),
                    })
                    .sum();
                guards + local_uses(&branch.body, local)
            })
            .sum(),
    }
}

impl<'q, Q> Emitter<'_, '_, 'q, Q>
where
    Q: checking::ExternalQueries,
{
    fn assign_function_names(&mut self) {
        let entry = self.program.entry;
        let entry_function = self.program.function(entry);
        let entry_is_procedure = entry_function.parameters.is_empty()
            && matches!(self.monotypes.get(entry_function.result), Monotype::Effect(result)
                if matches!(self.monotypes.get(*result), Monotype::Unit));
        for (index, function) in self.program.functions.iter().enumerate() {
            let name = if FunctionId(index as u32) == entry && entry_is_procedure {
                self.global_names.insert("main".into());
                "main".to_string()
            } else {
                unique(identifier(&function.name), &mut self.global_names)
            };
            self.function_names.push(name);
        }
    }

    fn main(&mut self) -> GoResult<Option<GoDeclaration>> {
        let entry = self.program.entry;
        let name = self.function_names[entry.0 as usize].clone();
        if name == "main" {
            return Ok(None);
        }
        let function = self.program.function(entry);
        let body = if function.parameters.is_empty()
            && let Monotype::Effect(_) = self.monotypes.get(function.result)
        {
            vec![GoStatement::Expression(call(identifier_expression(&name), vec![]))]
        } else {
            self.imports.insert("fmt");
            let value = identifier_expression(&name);
            let print = GoExpression::Qualified { package: "fmt", name: "Println".into() };
            vec![GoStatement::Expression(call(print, vec![value]))]
        };
        Ok(Some(GoDeclaration::Function {
            name: "main".into(),
            parameters: vec![],
            result: None,
            body,
        }))
    }

    fn function(&mut self, id: FunctionId) -> GoResult<Vec<GoDeclaration>> {
        let function: &Function = self.program.function(id);
        let name = self.function_names[id.0 as usize].clone();
        self.current = Some(id);
        self.locals.clear();
        self.local_names.clear();
        self.tail_loop = None;
        let mut parameters = vec![];
        for parameter in &function.parameters {
            let parameter_name = self.bind_local(parameter);
            let parameter_type = self.go_type(parameter.monotype)?;
            parameters.push((parameter_name, parameter_type));
        }
        let effect_result = self.monotypes.effect_result(function.result);
        let mode = if effect_result.is_some() { Mode::Perform } else { Mode::Value };
        if function.parameters.is_empty() && mode == Mode::Value {
            return self.constant(&name, function);
        }
        let result = self.go_result(effect_result.unwrap_or(function.result))?;
        let loops = !function.parameters.is_empty()
            && has_tail_call(&function.body, id, function.parameters.len(), mode)
            && !captures_parameters(&function.body, &function.parameters, mode, self.monotypes);
        if loops {
            let parameter_names = parameters.iter().map(|(name, _)| name.clone()).collect();
            self.tail_loop = Some(TailLoop { function: id, parameters: parameter_names });
        }
        let mut body = vec![];
        self.sink(&function.body, mode, Sink::Return, &mut body)?;
        if loops {
            if let Some(GoStatement::Continue) = body.last() {
                body.pop();
            }
            body = vec![GoStatement::Loop(body)];
        }
        if let Some(GoStatement::Return(None)) = body.last() {
            body.pop();
        }
        self.tail_loop = None;
        Ok(vec![GoDeclaration::Function { name, parameters, result, body }])
    }

    fn constant(&mut self, name: &str, function: &Function) -> GoResult<Vec<GoDeclaration>> {
        let type_ = self.go_type(function.result)?;
        let mut statements = vec![];
        let value = self.value(&function.body, &mut statements)?;
        if statements.is_empty() {
            return Ok(vec![GoDeclaration::Variable {
                name: name.into(),
                type_: Some(type_),
                value,
            }]);
        }
        let initializer = unique(format!("initialize{}", capitalise(name)), &mut self.global_names);
        statements.push(GoStatement::Return(Some(value)));
        let result = self.go_result(function.result)?;
        Ok(vec![
            GoDeclaration::Variable {
                name: name.into(),
                type_: None,
                value: call(identifier_expression(&initializer), vec![]),
            },
            GoDeclaration::Function {
                name: initializer,
                parameters: vec![],
                result,
                body: statements,
            },
        ])
    }

    fn current_definition(&self) -> String {
        match self.current {
            Some(id) => format!("code generation of {}", self.program.function(id).name),
            None => "code generation".into(),
        }
    }

    fn is_total(&mut self, pattern: &Pattern) -> bool {
        match &pattern.kind {
            PatternKind::Wildcard | PatternKind::Variable(_) => true,
            PatternKind::Named { pattern, .. } => self.is_total(pattern),
            PatternKind::Record(fields) => fields.iter().all(|(_, field)| self.is_total(field)),
            PatternKind::Constructor { data, arguments, .. } => {
                let product =
                    self.data_layout(data).is_ok_and(|layout| layout.kind == DataKind::Product);
                product && arguments.iter().all(|argument| self.is_total(argument))
            }
            PatternKind::Literal(_) | PatternKind::Array(_) => false,
        }
    }

    fn bind_pattern_local(
        &mut self,
        local: &Local,
        path: &GoExpression,
        uses: usize,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<()> {
        let reassigned = |name: &String| {
            self.tail_loop.as_ref().is_some_and(|tail_loop| tail_loop.parameters.contains(name))
        };
        let aliased = match path_root(path) {
            Some(root) if !reassigned(root) => {
                matches!(path, GoExpression::Identifier(_)) || uses == 1
            }
            _ => false,
        };
        if aliased {
            self.locals.insert(local.id, path.clone());
            return Ok(());
        }
        let name = self.bind_local(local);
        out.push(self.define(name, path.clone(), local.monotype)?);
        Ok(())
    }

    fn bind_local(&mut self, local: &Local) -> String {
        let name = unique(identifier(&local.name), &mut self.local_names);
        self.locals.insert(local.id, identifier_expression(&name));
        name
    }

    fn temporary(&mut self, base: &str) -> String {
        unique(base.to_string(), &mut self.local_names)
    }

    fn local(&self, id: LocalId) -> GoResult<GoExpression> {
        self.locals.get(&id).cloned().ok_or_else(|| GoError::Unsupported {
            definition: self.current_definition(),
            state: crate::error::UnsupportedState::Construct { construct: "unbound local" },
        })
    }

    fn go_type(&mut self, monotype: MonotypeId) -> GoResult<GoType> {
        Ok(match self.monotypes.get(monotype).clone() {
            Monotype::Int => GoType::Named("int32".into()),
            Monotype::Number => GoType::Float64,
            Monotype::Boolean => GoType::Bool,
            Monotype::Char => GoType::Rune,
            Monotype::String => GoType::String,
            Monotype::Unit => GoType::EmptyStruct,
            Monotype::Erased => GoType::Any,
            Monotype::Array(element) => GoType::Slice(Box::new(self.go_type(element)?)),
            Monotype::Record(_) => GoType::Named(self.record_name(monotype)?),
            Monotype::Function(argument, result) => {
                let argument = self.go_type(argument)?;
                let result = match self.monotypes.get(result) {
                    Monotype::Effect(inner) => self.go_result(*inner)?,
                    _ => self.go_result(result)?,
                };
                GoType::Function { parameters: vec![argument], result: result.map(Box::new) }
            }
            Monotype::Effect(result) => {
                let result = self.go_result(result)?;
                GoType::Function { parameters: vec![], result: result.map(Box::new) }
            }
            Monotype::Reference(value) => {
                self.declare_reference();
                let value = self.go_type(value)?;
                let rendered = render_type(&value);
                GoType::Pointer(Box::new(GoType::Named(format!("Ref[{rendered}]"))))
            }
            Monotype::Data(data) => {
                let layout = self.data_layout(&data)?;
                match layout.kind {
                    DataKind::Enumeration => GoType::Named(layout.name),
                    DataKind::Tagged | DataKind::Product => {
                        GoType::Pointer(Box::new(GoType::Named(layout.name)))
                    }
                }
            }
        })
    }

    fn go_result(&mut self, monotype: MonotypeId) -> GoResult<Option<GoType>> {
        if let Monotype::Unit = self.monotypes.get(monotype) {
            return Ok(None);
        }
        Ok(Some(self.go_type(monotype)?))
    }

    fn is_unit(&self, monotype: MonotypeId) -> bool {
        matches!(self.monotypes.get(monotype), Monotype::Unit)
    }

    fn declare_reference(&mut self) {
        if std::mem::replace(&mut self.reference_declared, true) {
            return;
        }
        self.type_declarations.push(GoDeclaration::Type {
            name: "Ref[T any]".into(),
            type_: GoType::Struct(vec![("Value".into(), GoType::Named("T".into()))]),
        });
    }

    fn record_name(&mut self, monotype: MonotypeId) -> GoResult<String> {
        if let Some(name) = self.record_names.get(&monotype) {
            return Ok(name.clone());
        }
        let Monotype::Record(fields) = self.monotypes.get(monotype).clone() else {
            unreachable!("invariant violated: record name requested for a non-record")
        };
        let base: String = if fields.is_empty() {
            "Empty".into()
        } else {
            fields.iter().map(|field| capitalise(&identifier(&field.label))).collect()
        };
        let name = unique(base, &mut self.global_names);
        self.record_names.insert(monotype, name.clone());
        let mut go_fields = vec![];
        for field in fields.iter() {
            go_fields.push((identifier(&field.label), self.go_type(field.monotype)?));
        }
        self.type_declarations
            .push(GoDeclaration::Type { name: name.clone(), type_: GoType::Struct(go_fields) });
        Ok(name)
    }

    fn data_layout(&mut self, data: &DataType) -> GoResult<DataLayout> {
        if let Some(layout) = self.data_layouts.get(data) {
            return Ok(layout.clone());
        }
        let mut base = self.context.type_name(data.file_id, data.item)?.to_string();
        for &argument in data.arguments.iter() {
            self.context.type_suffix(argument, &mut base)?;
        }
        let name = unique(identifier(&base), &mut self.global_names);
        let constructors = match self.monotypes.constructors(&mut self.context, data)? {
            Ok(constructors) => constructors,
            Err(state) => return Err(GoError::Unsupported { definition: name, state }),
        };
        let kind = if constructors.iter().all(|constructor| constructor.fields.is_empty()) {
            DataKind::Enumeration
        } else if constructors.len() == 1 {
            DataKind::Product
        } else {
            DataKind::Tagged
        };
        let mut layouts = vec![];
        for constructor in constructors.iter() {
            let tag =
                unique(format!("{name}{}", identifier(&constructor.name)), &mut self.global_names);
            let fields = constructor
                .fields
                .iter()
                .enumerate()
                .map(|(position, &monotype)| {
                    (format!("{}{position}", identifier(&constructor.name)), monotype)
                })
                .collect();
            layouts.push(ConstructorLayout { tag, fields });
        }
        let layout = DataLayout { name: name.clone(), kind, constructors: layouts.clone() };
        self.data_layouts.insert(data.clone(), layout.clone());
        match kind {
            DataKind::Enumeration => {
                self.type_declarations.push(GoDeclaration::Type {
                    name: name.clone(),
                    type_: GoType::Named("int".into()),
                });
                let names = layouts.iter().map(|constructor| constructor.tag.clone()).collect();
                self.type_declarations
                    .push(GoDeclaration::Constants { type_name: Some(name), names });
            }
            DataKind::Tagged | DataKind::Product => {
                let mut fields = vec![];
                if kind == DataKind::Tagged {
                    fields.push(("Tag".to_string(), GoType::Int));
                }
                for constructor in &layouts {
                    for (field_name, monotype) in &constructor.fields {
                        fields.push((field_name.clone(), self.go_type(*monotype)?));
                    }
                }
                self.type_declarations.push(GoDeclaration::Type {
                    name: name.clone(),
                    type_: GoType::Struct(fields),
                });
                if kind == DataKind::Tagged {
                    let names = layouts.iter().map(|constructor| constructor.tag.clone()).collect();
                    self.type_declarations
                        .push(GoDeclaration::Constants { type_name: None, names });
                }
            }
        }
        Ok(layout)
    }

    fn sink(
        &mut self,
        expression: &Expression,
        mode: Mode,
        sink: Sink,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<()> {
        match &expression.kind {
            ExpressionKind::Let { bindings, body } => {
                self.bindings(bindings, out)?;
                self.sink(body, mode, sink, out)
            }
            ExpressionKind::If { condition, then, otherwise } => {
                let condition = self.value(condition, out)?;
                let sink = self.prepare_branching_sink(sink, expression, mode, out)?;
                let mut then_statements = vec![];
                self.sink(then, mode, sink.clone(), &mut then_statements)?;
                let mut otherwise_statements = vec![];
                self.sink(otherwise, mode, sink.clone(), &mut otherwise_statements)?;
                if let Sink::Return = sink
                    && ends_in_jump(&then_statements)
                {
                    out.push(GoStatement::If {
                        condition,
                        then: then_statements,
                        otherwise: vec![],
                    });
                    out.extend(otherwise_statements);
                } else {
                    out.push(GoStatement::If {
                        condition,
                        then: then_statements,
                        otherwise: otherwise_statements,
                    });
                }
                Ok(())
            }
            ExpressionKind::Case { scrutinees, alternatives } => {
                self.case(expression, scrutinees, alternatives, mode, sink, out)
            }
            ExpressionKind::Fail(message) => {
                out.push(panic_statement(message));
                Ok(())
            }
            ExpressionKind::Apply { function, arguments } if matches!(sink, Sink::Return) => {
                if let ExpressionKind::Function(id) = function.kind
                    && let Some(tail_loop) = &self.tail_loop
                    && tail_loop.function == id
                    && tail_loop.parameters.len() == arguments.len()
                {
                    let parameters = tail_loop.parameters.clone();
                    return self.tail_call(&parameters, arguments, out);
                }
                self.leaf(expression, mode, sink, out)
            }
            _ => self.leaf(expression, mode, sink, out),
        }
    }

    fn tail_call(
        &mut self,
        parameters: &[String],
        arguments: &[Expression],
        out: &mut Vec<GoStatement>,
    ) -> GoResult<()> {
        let mut targets = vec![];
        let mut values = vec![];
        for (parameter, argument) in parameters.iter().zip(arguments) {
            let value = self.value(argument, out)?;
            if let GoExpression::Identifier(name) = &value
                && name == parameter
            {
                continue;
            }
            targets.push(identifier_expression(parameter));
            values.push(value);
        }
        if !targets.is_empty() {
            out.push(GoStatement::Assign { targets, values });
        }
        out.push(GoStatement::Continue);
        Ok(())
    }

    fn prepare_branching_sink(
        &mut self,
        sink: Sink,
        expression: &Expression,
        mode: Mode,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<Sink> {
        let Sink::Define(name) = sink else { return Ok(sink) };
        let monotype = match mode {
            Mode::Perform => {
                self.monotypes.effect_result(expression.monotype).unwrap_or(expression.monotype)
            }
            Mode::Value => expression.monotype,
        };
        if self.is_unit(monotype) {
            return Ok(Sink::Discard);
        }
        let type_ = self.go_type(monotype)?;
        out.push(GoStatement::Variable { name: name.clone(), type_, value: None });
        Ok(Sink::Assign(name))
    }

    fn leaf(
        &mut self,
        expression: &Expression,
        mode: Mode,
        sink: Sink,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<()> {
        if mode == Mode::Value {
            let value = self.value(expression, out)?;
            return self.deliver(value, expression.monotype, sink, out);
        }
        let result =
            self.monotypes.effect_result(expression.monotype).unwrap_or(expression.monotype);
        match &expression.kind {
            ExpressionKind::EffectPure(value) => {
                let value = self.value(value, out)?;
                self.deliver(value, result, sink, out)
            }
            ExpressionKind::EffectBind { action, local, body } => {
                let action_sink = if uses_local(body, local.id) && !self.is_unit(local.monotype) {
                    Sink::Define(self.bind_local(local))
                } else {
                    self.locals.insert(local.id, unit_value());
                    Sink::Discard
                };
                self.sink(action, Mode::Perform, action_sink, out)?;
                self.sink(body, Mode::Perform, sink, out)
            }
            ExpressionKind::EffectEach { array, element, body } => {
                let array = self.value(array, out)?;
                let saved = self.tail_loop.take();
                let element_name = if uses_local(body, element.id) {
                    self.bind_local(element)
                } else {
                    "_".to_string()
                };
                let mut statements = vec![];
                self.sink(body, Mode::Perform, Sink::Discard, &mut statements)?;
                self.tail_loop = saved;
                out.push(GoStatement::Range {
                    element: element_name,
                    iterable: array,
                    body: statements,
                });
                self.deliver(unit_value(), result, sink, out)
            }
            ExpressionKind::EffectWhen { condition, action } => {
                let condition = self.value(condition, out)?;
                let mut statements = vec![];
                self.sink(action, Mode::Perform, Sink::Discard, &mut statements)?;
                out.push(GoStatement::If { condition, then: statements, otherwise: vec![] });
                self.deliver(unit_value(), result, sink, out)
            }
            ExpressionKind::Foreign { foreign, arguments } if foreign.is_effectful() => {
                self.perform_foreign(*foreign, arguments, result, sink, out)
            }
            ExpressionKind::Apply { function, arguments } => {
                let performed = self.perform_application(function, arguments, out)?;
                self.deliver(performed, result, sink, out)
            }
            _ => {
                let action = self.value(expression, out)?;
                self.deliver(call(action, vec![]), result, sink, out)
            }
        }
    }

    fn perform_application(
        &mut self,
        function: &Expression,
        arguments: &[Expression],
        out: &mut Vec<GoStatement>,
    ) -> GoResult<GoExpression> {
        if let ExpressionKind::Function(id) = function.kind {
            let arity = self.program.function(id).parameters.len();
            if arity == arguments.len() {
                let mut values = vec![];
                for argument in arguments {
                    values.push(self.value(argument, out)?);
                }
                return Ok(call(
                    identifier_expression(&self.function_names[id.0 as usize].clone()),
                    values,
                ));
            }
        }
        let (last, leading) =
            arguments.split_last().expect("invariant violated: application without arguments");
        let partial_monotype = self.monotypes.function(
            last.monotype,
            self.monotypes.result_after(function.monotype, arguments.len()),
        );
        let partial = if leading.is_empty() {
            self.value(function, out)?
        } else {
            let partial = Expression::new(
                ExpressionKind::Apply {
                    function: Box::new(function.clone()),
                    arguments: leading.to_vec(),
                },
                partial_monotype,
            );
            self.value(&partial, out)?
        };
        let last = self.value(last, out)?;
        Ok(call(partial, vec![last]))
    }

    fn perform_foreign(
        &mut self,
        foreign: Foreign,
        arguments: &[Expression],
        result: MonotypeId,
        sink: Sink,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<()> {
        let mut values = vec![];
        for argument in arguments {
            values.push(self.value(argument, out)?);
        }
        match foreign {
            Foreign::Print => {
                self.imports.insert("fmt");
                let print = GoExpression::Qualified { package: "fmt", name: "Println".into() };
                out.push(GoStatement::Expression(call(print, values)));
                self.deliver(unit_value(), result, sink, out)
            }
            Foreign::ReferenceNew => {
                let value_type = self.go_type(arguments[0].monotype)?;
                self.declare_reference();
                let reference = GoExpression::Address(Box::new(GoExpression::Composite {
                    type_: GoType::Named(format!("Ref[{}]", render_type(&value_type))),
                    fields: vec![(Some("Value".into()), values.remove(0))],
                }));
                self.deliver(reference, result, sink, out)
            }
            Foreign::ReferenceRead => {
                let value = field(values.remove(0), "Value");
                self.deliver(value, result, sink, out)
            }
            Foreign::ReferenceWrite => {
                let value = values.remove(0);
                let reference = values.remove(0);
                out.push(GoStatement::Assign {
                    targets: vec![field(reference, "Value")],
                    values: vec![value],
                });
                self.deliver(unit_value(), result, sink, out)
            }
            Foreign::ReferenceModify => {
                let reference = values.remove(1);
                let reference = self.hoist(reference, "reference", out);
                let modified = self.temporary("modified");
                if let ExpressionKind::Lambda { parameters, body } = &arguments[0].kind
                    && let [state] = parameters.as_slice()
                {
                    let name = self.bind_local(state);
                    out.push(GoStatement::Define {
                        names: vec![name],
                        values: vec![field(reference.clone(), "Value")],
                    });
                    self.sink(body, Mode::Value, Sink::Define(modified.clone()), out)?;
                } else {
                    let update = values.remove(0);
                    out.push(GoStatement::Define {
                        names: vec![modified.clone()],
                        values: vec![call(update, vec![field(reference.clone(), "Value")])],
                    });
                }
                out.push(GoStatement::Assign {
                    targets: vec![field(reference, "Value")],
                    values: vec![field(identifier_expression(&modified), "state")],
                });
                self.deliver(field(identifier_expression(&modified), "value"), result, sink, out)
            }
            Foreign::EffectCall { function, .. } => {
                self.imports.insert(function.package.path());
                let function = GoExpression::Qualified {
                    package: function.package.name(),
                    name: function.name.into(),
                };
                self.deliver(call(call(function, values), vec![]), result, sink, out)
            }
            Foreign::EffectPure => self.deliver(values.remove(0), result, sink, out),
            _ => Err(GoError::Unsupported {
                definition: self.current_definition(),
                state: crate::error::UnsupportedState::Construct {
                    construct: "unsaturated effect primitives",
                },
            }),
        }
    }

    fn hoist(
        &mut self,
        value: GoExpression,
        base: &str,
        out: &mut Vec<GoStatement>,
    ) -> GoExpression {
        if is_simple(&value) {
            return value;
        }
        let name = self.temporary(base);
        out.push(GoStatement::Define { names: vec![name.clone()], values: vec![value] });
        identifier_expression(&name)
    }

    fn deliver(
        &mut self,
        value: GoExpression,
        monotype: MonotypeId,
        sink: Sink,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<()> {
        let unit = self.is_unit(monotype);
        match sink {
            Sink::Return => {
                if unit {
                    if is_effectful_call(&value) {
                        out.push(GoStatement::Expression(value));
                    }
                    out.push(GoStatement::Return(None));
                } else {
                    out.push(GoStatement::Return(Some(value)));
                }
            }
            Sink::Assign(name) => {
                if unit {
                    if is_effectful_call(&value) {
                        out.push(GoStatement::Expression(value));
                    }
                } else {
                    out.push(GoStatement::Assign {
                        targets: vec![identifier_expression(&name)],
                        values: vec![value],
                    });
                }
            }
            Sink::Define(name) => {
                if unit {
                    if is_effectful_call(&value) {
                        out.push(GoStatement::Expression(value));
                    }
                } else {
                    out.push(self.define(name, value, monotype)?);
                }
            }
            Sink::Discard => {
                if is_effectful_call(&value) {
                    out.push(GoStatement::Expression(value));
                }
            }
        }
        Ok(())
    }

    /// `x := 4` would give `x` Go's default `int`; constants need their declared type.
    fn define(
        &mut self,
        name: String,
        value: GoExpression,
        monotype: MonotypeId,
    ) -> GoResult<GoStatement> {
        if is_untyped_constant(&value)
            && !matches!(self.monotypes.get(monotype), Monotype::String | Monotype::Boolean)
        {
            let type_ = self.go_type(monotype)?;
            return Ok(GoStatement::Variable { name, type_, value: Some(value) });
        }
        Ok(GoStatement::Define { names: vec![name], values: vec![value] })
    }

    fn bindings(&mut self, bindings: &[Binding], out: &mut Vec<GoStatement>) -> GoResult<()> {
        let recursive = bindings
            .iter()
            .any(|binding| bindings.iter().any(|other| uses_local(&binding.value, other.local.id)));
        if recursive {
            let mut names = vec![];
            for binding in bindings {
                let name = self.bind_local(&binding.local);
                let type_ = self.go_type(binding.local.monotype)?;
                out.push(GoStatement::Variable { name: name.clone(), type_, value: None });
                names.push(name);
            }
            for (binding, name) in bindings.iter().zip(names) {
                let value = self.value(&binding.value, out)?;
                out.push(GoStatement::Assign {
                    targets: vec![identifier_expression(&name)],
                    values: vec![value],
                });
            }
            return Ok(());
        }
        for binding in bindings {
            if self.is_unit(binding.local.monotype) {
                let value = self.value(&binding.value, out)?;
                if is_effectful_call(&value) {
                    out.push(GoStatement::Expression(value));
                }
                self.locals.insert(binding.local.id, unit_value());
                continue;
            }
            let mut statements = vec![];
            let name = self.bind_local(&binding.local);
            self.sink(&binding.value, Mode::Value, Sink::Define(name), &mut statements)?;
            out.extend(statements);
        }
        Ok(())
    }

    fn value(
        &mut self,
        expression: &Expression,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<GoExpression> {
        if self.monotypes.effect_result(expression.monotype).is_some() && is_effect_node(expression)
        {
            return self.thunk(expression);
        }
        Ok(match &expression.kind {
            ExpressionKind::Literal(literal) => self.literal(literal, expression.monotype),
            ExpressionKind::Unit => unit_value(),
            ExpressionKind::Array(elements) => {
                let type_ = self.go_type(expression.monotype)?;
                let mut fields = vec![];
                for element in elements {
                    fields.push((None, self.value(element, out)?));
                }
                GoExpression::Composite { type_, fields }
            }
            ExpressionKind::Record(fields) => {
                let name = self.record_name(expression.monotype)?;
                let mut values = vec![];
                for (label, value) in fields {
                    values.push((Some(identifier(label)), self.value(value, out)?));
                }
                GoExpression::Composite { type_: GoType::Named(name), fields: values }
            }
            ExpressionKind::Access { record, label } => {
                let record = self.value(record, out)?;
                field(record, &identifier(label))
            }
            ExpressionKind::Update { record, updates } => {
                let record = self.value(record, out)?;
                let name = self.temporary("updated");
                out.push(GoStatement::Define { names: vec![name.clone()], values: vec![record] });
                self.updates(identifier_expression(&name), updates, out)?;
                identifier_expression(&name)
            }
            ExpressionKind::Local(id) => self.local(*id)?,
            ExpressionKind::Function(id) => self.function_value(*id)?,
            ExpressionKind::Construct { data, constructor, arguments } => {
                let mut values = vec![];
                for argument in arguments {
                    values.push(self.value(argument, out)?);
                }
                self.construct(data, *constructor, values)?
            }
            ExpressionKind::Foreign { foreign, arguments } => {
                self.foreign_value(*foreign, arguments, expression.monotype, out)?
            }
            ExpressionKind::Apply { function, arguments } => {
                let applied = self.application_value(function, arguments, out)?;
                if self.is_unit(expression.monotype) && is_effectful_call(&applied) {
                    out.push(GoStatement::Expression(applied));
                    return Ok(unit_value());
                }
                applied
            }
            ExpressionKind::Lambda { parameters, body } => self.lambda(parameters, body)?,
            ExpressionKind::Let { bindings, body } => {
                self.bindings(bindings, out)?;
                self.value(body, out)?
            }
            ExpressionKind::Case { scrutinees, alternatives }
                if alternatives.first().is_some_and(|first| {
                    matches!(first.body, Guarded::Unconditional(_))
                        && first.patterns.iter().all(|pattern| self.is_total(pattern))
                }) =>
            {
                let first = &alternatives[0];
                let mut paths = vec![];
                for (scrutinee, pattern) in scrutinees.iter().zip(&first.patterns) {
                    if let PatternKind::Wildcard = pattern.kind {
                        paths.push(unit_value());
                        continue;
                    }
                    let value = self.value(scrutinee, out)?;
                    paths.push(self.hoist(value, "scrutinee", out));
                }
                let Guarded::Unconditional(body) = &first.body else { unreachable!() };
                let (_, bindings) = self.alternative_tests(&paths, &first.patterns)?;
                for (local, path) in &bindings {
                    let uses = local_uses(body, local.id);
                    if uses > 0 {
                        self.bind_pattern_local(local, path, uses, out)?;
                    }
                }
                self.value(body, out)?
            }
            ExpressionKind::If { .. } | ExpressionKind::Case { .. } => {
                if self.is_unit(expression.monotype) {
                    self.sink(expression, Mode::Value, Sink::Discard, out)?;
                    return Ok(unit_value());
                }
                let name = self.temporary("result");
                self.sink(expression, Mode::Value, Sink::Define(name.clone()), out)?;
                identifier_expression(&name)
            }
            ExpressionKind::Fail(message) => {
                out.push(panic_statement(message));
                let type_ = self.go_type(expression.monotype)?;
                let name = self.temporary("unreachable");
                out.push(GoStatement::Variable { name: name.clone(), type_, value: None });
                identifier_expression(&name)
            }
            ExpressionKind::EffectPure(_)
            | ExpressionKind::EffectBind { .. }
            | ExpressionKind::EffectEach { .. }
            | ExpressionKind::EffectWhen { .. } => self.thunk(expression)?,
        })
    }

    fn construct(
        &mut self,
        data: &DataType,
        constructor: usize,
        values: Vec<GoExpression>,
    ) -> GoResult<GoExpression> {
        let layout = self.data_layout(data)?;
        let constructor_layout = layout.constructors[constructor].clone();
        Ok(match layout.kind {
            DataKind::Enumeration => identifier_expression(&constructor_layout.tag),
            DataKind::Tagged | DataKind::Product => {
                let mut fields = vec![];
                if layout.kind == DataKind::Tagged {
                    fields.push((
                        Some("Tag".to_string()),
                        identifier_expression(&constructor_layout.tag),
                    ));
                }
                for ((field_name, _), value) in constructor_layout.fields.iter().zip(values) {
                    fields.push((Some(field_name.clone()), value));
                }
                GoExpression::Address(Box::new(GoExpression::Composite {
                    type_: GoType::Named(layout.name),
                    fields,
                }))
            }
        })
    }

    fn constructor_named(
        &mut self,
        monotype: MonotypeId,
        name: &str,
    ) -> GoResult<(DataType, usize)> {
        let Monotype::Data(data) = self.monotypes.get(monotype).clone() else {
            return Err(GoError::Unsupported {
                definition: self.current_definition(),
                state: crate::error::UnsupportedState::Construct {
                    construct: "Maybe results of a non-Maybe type",
                },
            });
        };
        let constructors = match self.monotypes.constructors(&mut self.context, &data)? {
            Ok(constructors) => constructors,
            Err(state) => {
                return Err(GoError::Unsupported { definition: self.current_definition(), state });
            }
        };
        let index =
            constructors.iter().position(|constructor| constructor.name == name).unwrap_or(0);
        Ok((data, index))
    }

    /// `xs !! i` as a bounds check rather than a call through Just and Nothing closures.
    fn maybe_index(
        &mut self,
        arguments: &[Expression],
        monotype: MonotypeId,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<GoExpression> {
        let elements = self.value(&arguments[2], out)?;
        let elements = self.hoist(elements, "elements", out);
        let index = self.value(&arguments[3], out)?;
        let index = self.hoist(index, "index", out);
        let (data, just) = self.constructor_named(monotype, "Just")?;
        let (_, nothing) = self.constructor_named(monotype, "Nothing")?;
        let element = GoExpression::Index {
            value: Box::new(elements.clone()),
            index: Box::new(index.clone()),
        };
        let found = self.construct(&data, just, vec![element])?;
        let missing = self.construct(&data, nothing, vec![])?;
        let name = self.temporary("element");
        let type_ = self.go_type(monotype)?;
        out.push(GoStatement::Variable { name: name.clone(), type_, value: None });
        let length = call(identifier_expression("len"), vec![elements]);
        let widened =
            GoExpression::Conversion { type_: GoType::Int, value: Box::new(index.clone()) };
        let condition = binary(
            "&&",
            binary(">=", index, GoExpression::Integer(0)),
            binary("<", widened, length),
        );
        let target = vec![identifier_expression(&name)];
        out.push(GoStatement::If {
            condition,
            then: vec![GoStatement::Assign { targets: target.clone(), values: vec![found] }],
            otherwise: vec![GoStatement::Assign { targets: target, values: vec![missing] }],
        });
        Ok(identifier_expression(&name))
    }

    fn updates(
        &mut self,
        target: GoExpression,
        updates: &[RecordUpdate],
        out: &mut Vec<GoStatement>,
    ) -> GoResult<()> {
        for update in updates {
            match update {
                RecordUpdate::Leaf { label, value } => {
                    let value = self.value(value, out)?;
                    out.push(GoStatement::Assign {
                        targets: vec![field(target.clone(), &identifier(label))],
                        values: vec![value],
                    });
                }
                RecordUpdate::Branch { label, updates } => {
                    self.updates(field(target.clone(), &identifier(label)), updates, out)?;
                }
            }
        }
        Ok(())
    }

    fn literal(&mut self, literal: &Literal, monotype: MonotypeId) -> GoExpression {
        match literal {
            Literal::Int(value) => GoExpression::Integer(*value),
            Literal::Number(value) => {
                let mut value = value.to_string();
                if !value.contains(['.', 'e', 'E'])
                    && matches!(self.monotypes.get(monotype), Monotype::Number)
                {
                    value.push_str(".0");
                }
                GoExpression::Float(value)
            }
            Literal::String(value) => GoExpression::String(value.clone()),
            Literal::Char(value) => GoExpression::Rune(*value),
            Literal::Boolean(value) => GoExpression::Boolean(*value),
        }
    }

    /// A first-class effect: the only place an `Effect` becomes a Go closure.
    fn thunk(&mut self, expression: &Expression) -> GoResult<GoExpression> {
        let result =
            self.monotypes.effect_result(expression.monotype).unwrap_or(expression.monotype);
        let result_type = self.go_result(result)?;
        let saved = self.tail_loop.take();
        let mut body = vec![];
        self.sink(expression, Mode::Perform, Sink::Return, &mut body)?;
        self.tail_loop = saved;
        if let Some(GoStatement::Return(None)) = body.last() {
            body.pop();
        }
        Ok(GoExpression::Function { parameters: vec![], result: result_type, body })
    }

    fn lambda(&mut self, parameters: &[Local], body: &Expression) -> GoResult<GoExpression> {
        let (first, rest) =
            parameters.split_first().expect("invariant violated: lambda without parameters");
        let name =
            if uses_local(body, first.id) { self.bind_local(first) } else { "_".to_string() };
        let parameter_type = self.go_type(first.monotype)?;
        let saved = self.tail_loop.take();
        let mut statements = vec![];
        let result_monotype;
        if rest.is_empty() {
            let mode = if self.monotypes.effect_result(body.monotype).is_some() {
                Mode::Perform
            } else {
                Mode::Value
            };
            result_monotype = self.monotypes.effect_result(body.monotype).unwrap_or(body.monotype);
            self.sink(body, mode, Sink::Return, &mut statements)?;
        } else {
            let mut inner_monotype = body.monotype;
            for parameter in rest.iter().rev() {
                inner_monotype = self.monotypes.function(parameter.monotype, inner_monotype);
            }
            result_monotype = inner_monotype;
            let inner = self.lambda(rest, body)?;
            statements.push(GoStatement::Return(Some(inner)));
        }
        self.tail_loop = saved;
        if let Some(GoStatement::Return(None)) = statements.last() {
            statements.pop();
        }
        let result = self.go_result(result_monotype)?;
        Ok(GoExpression::Function {
            parameters: vec![(name, parameter_type)],
            result,
            body: statements,
        })
    }

    fn function_value(&mut self, id: FunctionId) -> GoResult<GoExpression> {
        let function = self.program.function(id);
        let name = self.function_names[id.0 as usize].clone();
        if function.parameters.len() <= 1 {
            return Ok(identifier_expression(&name));
        }
        let parameters: Vec<Local> = function.parameters.clone();
        self.curried_wrapper(identifier_expression(&name), vec![], &parameters, function.result)
    }

    /// Partial applications of uncurried Go functions become curried closures.
    fn curried_wrapper(
        &mut self,
        function: GoExpression,
        supplied: Vec<GoExpression>,
        remaining: &[Local],
        result: MonotypeId,
    ) -> GoResult<GoExpression> {
        let (first, rest) =
            remaining.split_first().expect("invariant violated: wrapper without parameters");
        let name = self.temporary(&identifier(&first.name));
        let parameter_type = self.go_type(first.monotype)?;
        let mut supplied = supplied;
        supplied.push(identifier_expression(&name));
        let (body, result_monotype) = if rest.is_empty() {
            let call = call(function, supplied);
            let effect_result = self.monotypes.effect_result(result);
            let returned = effect_result.unwrap_or(result);
            if self.is_unit(returned) {
                (vec![GoStatement::Expression(call)], returned)
            } else {
                (vec![GoStatement::Return(Some(call))], returned)
            }
        } else {
            let mut inner_monotype = result;
            for parameter in rest.iter().rev() {
                inner_monotype = self.monotypes.function(parameter.monotype, inner_monotype);
            }
            let inner = self.curried_wrapper(function, supplied, rest, result)?;
            (vec![GoStatement::Return(Some(inner))], inner_monotype)
        };
        let result_type = self.go_result(result_monotype)?;
        Ok(GoExpression::Function {
            parameters: vec![(name, parameter_type)],
            result: result_type,
            body,
        })
    }

    fn application_value(
        &mut self,
        function: &Expression,
        arguments: &[Expression],
        out: &mut Vec<GoStatement>,
    ) -> GoResult<GoExpression> {
        let mut values = vec![];
        for argument in arguments {
            values.push(self.value(argument, out)?);
        }
        if let ExpressionKind::Function(id) = function.kind {
            let callee = self.program.function(id);
            let arity = callee.parameters.len();
            let name = identifier_expression(&self.function_names[id.0 as usize].clone());
            if arity > values.len() {
                let remaining = callee.parameters[values.len()..].to_vec();
                return self.curried_wrapper(name, values, &remaining, callee.result);
            }
            if arity > 0 {
                let rest = values.split_off(arity);
                let mut result = call(name, values);
                for value in rest {
                    result = call(result, vec![value]);
                }
                return Ok(result);
            }
        }
        let mut result = self.value(function, out)?;
        for value in values {
            result = call(result, vec![value]);
        }
        Ok(result)
    }

    fn foreign_value(
        &mut self,
        foreign: Foreign,
        arguments: &[Expression],
        monotype: MonotypeId,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<GoExpression> {
        if foreign.is_effectful() {
            let expression = Expression::new(
                ExpressionKind::Foreign { foreign, arguments: arguments.to_vec() },
                monotype,
            );
            return self.thunk(&expression);
        }
        if let Foreign::Range = foreign {
            if !std::mem::replace(&mut self.range_declared, true) {
                self.type_declarations.push(GoDeclaration::Source(RANGE_SOURCE));
            }
            let mut values = vec![];
            for argument in arguments {
                values.push(self.value(argument, out)?);
            }
            return Ok(call(identifier_expression("rangeInt32"), values));
        }
        if let Foreign::MaybeIndex = foreign {
            return self.maybe_index(arguments, monotype, out);
        }
        if let Foreign::RunEffect = foreign {
            if self.is_unit(monotype) {
                self.sink(&arguments[0], Mode::Perform, Sink::Discard, out)?;
                return Ok(unit_value());
            }
            let name = self.temporary("performed");
            self.sink(&arguments[0], Mode::Perform, Sink::Define(name.clone()), out)?;
            return Ok(identifier_expression(&name));
        }
        let mut values = vec![];
        for argument in arguments {
            values.push(self.value(argument, out)?);
        }
        Ok(match foreign {
            Foreign::Operator(operator) => self.operator(operator, values),
            Foreign::Call { function, integers, .. } => {
                self.imports.insert(function.package.path());
                let widened = values
                    .into_iter()
                    .enumerate()
                    .map(|(position, value)| {
                        if integers.arguments.contains(&position) {
                            GoExpression::Conversion { type_: GoType::Int, value: Box::new(value) }
                        } else {
                            value
                        }
                    })
                    .collect();
                let callee = GoExpression::Qualified {
                    package: function.package.name(),
                    name: function.name.into(),
                };
                let result = call(callee, widened);
                if integers.result { self.narrow(result, monotype) } else { result }
            }
            Foreign::Constant(function) => {
                self.imports.insert(function.package.path());
                let constant = GoExpression::Qualified {
                    package: function.package.name(),
                    name: function.name.into(),
                };
                self.narrow(constant, monotype)
            }
            Foreign::Unit => unit_value(),
            Foreign::UnsafeCoerce | Foreign::Identity => values.remove(0),
            _ => unreachable!("invariant violated: effectful foreign reached value conversion"),
        })
    }

    /// go-support represents PureScript `Int` as Go `int`; generated code uses
    /// `int32`, whose overflow wraps exactly like JavaScript's `| 0`.
    fn narrow(&mut self, value: GoExpression, monotype: MonotypeId) -> GoExpression {
        if let Monotype::Int = self.monotypes.get(monotype) {
            return GoExpression::Conversion {
                type_: GoType::Named("int32".into()),
                value: Box::new(value),
            };
        }
        value
    }

    fn operator(&mut self, operator: Operator, mut values: Vec<GoExpression>) -> GoExpression {
        let unary = |operator: &'static str, values: &mut Vec<GoExpression>| GoExpression::Unary {
            operator,
            operand: Box::new(values.remove(0)),
        };
        if operator.arity() == 1 {
            return match operator {
                Operator::IntNegate | Operator::NumberNegate => unary("-", &mut values),
                Operator::BooleanNot => unary("!", &mut values),
                Operator::ArrayLength => GoExpression::Conversion {
                    type_: GoType::Named("int32".into()),
                    value: Box::new(call(identifier_expression("len"), values)),
                },
                Operator::IntToNumber => GoExpression::Conversion {
                    type_: GoType::Float64,
                    value: Box::new(values.remove(0)),
                },
                _ => unreachable!(),
            };
        }
        let right = values.pop().expect("invariant violated: binary operator arity");
        let left = values.pop().expect("invariant violated: binary operator arity");
        if let Operator::ArrayIndex = operator {
            return GoExpression::Index { value: Box::new(left), index: Box::new(right) };
        }
        let symbol = match operator {
            Operator::IntAdd | Operator::NumberAdd | Operator::StringAppend => "+",
            Operator::IntSubtract | Operator::NumberSubtract => "-",
            Operator::IntMultiply | Operator::NumberMultiply => "*",
            Operator::NumberDivide => "/",
            Operator::BooleanAnd => "&&",
            Operator::BooleanOr => "||",
            Operator::Compare(comparison) => match comparison {
                Comparison::Equal => "==",
                Comparison::NotEqual => "!=",
                Comparison::LessThan => "<",
                Comparison::LessThanOrEqual => "<=",
                Comparison::GreaterThan => ">",
                Comparison::GreaterThanOrEqual => ">=",
            },
            _ => unreachable!(),
        };
        binary(symbol, left, right)
    }

    fn case(
        &mut self,
        expression: &Expression,
        scrutinees: &[Expression],
        alternatives: &[Alternative],
        mode: Mode,
        sink: Sink,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<()> {
        let mut paths = vec![];
        for (position, scrutinee) in scrutinees.iter().enumerate() {
            let inspected = alternatives.iter().any(|alternative| {
                !matches!(alternative.patterns[position].kind, PatternKind::Wildcard)
            });
            if !inspected {
                paths.push(unit_value());
                continue;
            }
            let value = self.value(scrutinee, out)?;
            paths.push(self.hoist(value, "scrutinee", out));
        }
        if let Some(first) = alternatives.first()
            && let Guarded::Unconditional(body) = &first.body
        {
            let (tests, bindings) = self.alternative_tests(&paths, &first.patterns)?;
            if tests.is_empty() {
                for (local, path) in &bindings {
                    let uses = local_uses(body, local.id);
                    if uses > 0 {
                        self.bind_pattern_local(local, path, uses, out)?;
                    }
                }
                return self.sink(body, mode, sink, out);
            }
        }
        if self.try_switch(expression, &paths, scrutinees, alternatives, mode, sink.clone(), out)? {
            return Ok(());
        }
        if let Sink::Return = sink {
            return self.sequential_case(&paths, alternatives, mode, out);
        }
        let sink = self.prepare_branching_sink(sink, expression, mode, out)?;
        let mut chain: Vec<(Option<GoExpression>, Vec<GoStatement>)> = vec![];
        let mut exhaustive = false;
        for alternative in alternatives {
            let (tests, bindings) = self.alternative_tests(&paths, &alternative.patterns)?;
            let branches: Vec<(Vec<&Guard>, &Expression)> = match &alternative.body {
                Guarded::Unconditional(body) => vec![(vec![], body)],
                Guarded::Guards(branches) => branches
                    .iter()
                    .map(|branch| (branch.guards.iter().collect(), &branch.body))
                    .collect(),
            };
            for (guards, body) in branches {
                let mut conditions = tests.clone();
                for (local, path) in &bindings {
                    self.locals.insert(local.id, path.clone());
                }
                for guard in guards {
                    let Guard::Boolean(condition) = guard else {
                        return self.closure_case(
                            &paths,
                            alternatives,
                            expression,
                            mode,
                            sink,
                            out,
                        );
                    };
                    let mut hoisted = vec![];
                    let condition = self.value(condition, &mut hoisted)?;
                    if !hoisted.is_empty() {
                        return self.closure_case(
                            &paths,
                            alternatives,
                            expression,
                            mode,
                            sink,
                            out,
                        );
                    }
                    if !matches!(condition, GoExpression::Boolean(true)) {
                        conditions.push(condition);
                    }
                }
                let mut block = vec![];
                for (local, path) in &bindings {
                    let uses = local_uses(body, local.id);
                    if uses > 0 {
                        self.bind_pattern_local(local, path, uses, &mut block)?;
                    }
                }
                self.sink(body, mode, sink.clone(), &mut block)?;
                let condition = conjunction(conditions);
                let unconditional = condition.is_none();
                chain.push((condition, block));
                if unconditional {
                    exhaustive = true;
                    break;
                }
            }
            if exhaustive {
                break;
            }
        }
        if !exhaustive {
            chain.push((None, vec![panic_statement("Failed pattern match")]));
        }
        let mut statements: Vec<GoStatement> = vec![];
        for (condition, block) in chain.into_iter().rev() {
            statements = match condition {
                None => block,
                Some(condition) => {
                    vec![GoStatement::If { condition, then: block, otherwise: statements }]
                }
            };
        }
        out.extend(statements);
        Ok(())
    }

    fn closure_case(
        &mut self,
        paths: &[GoExpression],
        alternatives: &[Alternative],
        expression: &Expression,
        mode: Mode,
        sink: Sink,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<()> {
        let result = match mode {
            Mode::Perform => {
                self.monotypes.effect_result(expression.monotype).unwrap_or(expression.monotype)
            }
            Mode::Value => expression.monotype,
        };
        let result_type = self.go_result(result)?;
        let saved = self.tail_loop.take();
        let mut body = vec![];
        self.sequential_case(paths, alternatives, mode, &mut body)?;
        self.tail_loop = saved;
        let closure = GoExpression::Function { parameters: vec![], result: result_type, body };
        self.deliver(call(closure, vec![]), result, sink, out)
    }

    fn sequential_case(
        &mut self,
        paths: &[GoExpression],
        alternatives: &[Alternative],
        mode: Mode,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<()> {
        for alternative in alternatives {
            let (tests, bindings) = self.alternative_tests(paths, &alternative.patterns)?;
            let mut block = vec![];
            for (local, path) in &bindings {
                let uses = guarded_local_uses(&alternative.body, local.id);
                if uses > 0 {
                    self.bind_pattern_local(local, path, uses, &mut block)?;
                }
            }
            let terminates = self.guarded_sequential(&alternative.body, mode, &mut block)?;
            match conjunction(tests) {
                None => {
                    out.extend(block);
                    if terminates {
                        return Ok(());
                    }
                }
                Some(condition) => {
                    out.push(GoStatement::If { condition, then: block, otherwise: vec![] })
                }
            }
        }
        out.push(panic_statement("Failed pattern match"));
        Ok(())
    }

    fn guarded_sequential(
        &mut self,
        guarded: &Guarded,
        mode: Mode,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<bool> {
        let branches = match guarded {
            Guarded::Unconditional(body) => {
                self.sink(body, mode, Sink::Return, out)?;
                return Ok(true);
            }
            Guarded::Guards(branches) => branches,
        };
        for branch in branches {
            if self.guard_chain(&branch.guards, vec![], vec![], &branch.body, mode, out)? {
                return Ok(true);
            }
        }
        Ok(false)
    }

    fn guard_chain(
        &mut self,
        guards: &[Guard],
        mut conditions: Vec<GoExpression>,
        mut bindings: Vec<(Local, GoExpression)>,
        body: &Expression,
        mode: Mode,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<bool> {
        let Some((guard, rest)) = guards.split_first() else {
            let mut block = vec![];
            for (local, path) in &bindings {
                let uses = local_uses(body, local.id);
                if uses > 0 {
                    self.bind_pattern_local(local, path, uses, &mut block)?;
                }
            }
            self.sink(body, mode, Sink::Return, &mut block)?;
            return Ok(match conjunction(conditions) {
                None => {
                    out.extend(block);
                    true
                }
                Some(condition) => {
                    out.push(GoStatement::If { condition, then: block, otherwise: vec![] });
                    false
                }
            });
        };
        let mut evaluation = vec![];
        let mut tests = vec![];
        let mut guard_bindings = vec![];
        match guard {
            Guard::Boolean(condition) => {
                let condition = self.value(condition, &mut evaluation)?;
                if !matches!(condition, GoExpression::Boolean(true)) {
                    tests.push(condition);
                }
            }
            Guard::Pattern { pattern, value } => {
                let value = self.value(value, &mut evaluation)?;
                let value = self.hoist(value, "guarded", &mut evaluation);
                self.pattern_tests(pattern, value, &mut tests, &mut guard_bindings)?;
                for (local, path) in &guard_bindings {
                    self.locals.insert(local.id, path.clone());
                }
            }
        }
        if evaluation.is_empty() || conditions.is_empty() {
            out.extend(evaluation);
            conditions.extend(tests);
            bindings.extend(guard_bindings);
            return self.guard_chain(rest, conditions, bindings, body, mode, out);
        }
        let mut block = evaluation;
        bindings.extend(guard_bindings);
        self.guard_chain(rest, tests, bindings, body, mode, &mut block)?;
        let condition =
            conjunction(conditions).expect("invariant violated: conditions are pending");
        out.push(GoStatement::If { condition, then: block, otherwise: vec![] });
        Ok(false)
    }

    #[allow(clippy::too_many_arguments)]
    fn try_switch(
        &mut self,
        expression: &Expression,
        paths: &[GoExpression],
        scrutinees: &[Expression],
        alternatives: &[Alternative],
        mode: Mode,
        sink: Sink,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<bool> {
        let [path] = paths else { return Ok(false) };
        let [scrutinee] = scrutinees else { return Ok(false) };
        let switchable = alternatives.len() > 1
            && alternatives.iter().enumerate().all(|(position, alternative)| {
                let Guarded::Unconditional(_) = alternative.body else { return false };
                let pattern = &alternative.patterns[0];
                match &pattern.kind {
                    PatternKind::Constructor { arguments, .. } => {
                        arguments.iter().all(Pattern::is_irrefutable)
                    }
                    PatternKind::Literal(
                        Literal::Int(_) | Literal::String(_) | Literal::Char(_),
                    ) => true,
                    PatternKind::Wildcard | PatternKind::Variable(_) => {
                        position == alternatives.len() - 1
                    }
                    _ => false,
                }
            });
        if !switchable {
            return Ok(false);
        }
        let subject = match self.monotypes.get(scrutinee.monotype).clone() {
            Monotype::Data(data) => {
                let layout = self.data_layout(&data)?;
                match layout.kind {
                    DataKind::Enumeration => path.clone(),
                    DataKind::Tagged => field(path.clone(), "Tag"),
                    DataKind::Product => return Ok(false),
                }
            }
            Monotype::Int | Monotype::String | Monotype::Char => path.clone(),
            _ => return Ok(false),
        };
        let sink = match sink {
            Sink::Return => Sink::Return,
            other => self.prepare_branching_sink(other, expression, mode, out)?,
        };
        let mut cases = vec![];
        let mut default = None;
        for alternative in alternatives {
            let Guarded::Unconditional(body) = &alternative.body else { unreachable!() };
            let pattern = &alternative.patterns[0];
            let mut tests = vec![];
            let mut bindings = vec![];
            self.pattern_tests(pattern, path.clone(), &mut tests, &mut bindings)?;
            let mut block = vec![];
            for (local, binding_path) in &bindings {
                let uses = local_uses(body, local.id);
                if uses > 0 {
                    self.bind_pattern_local(local, binding_path, uses, &mut block)?;
                }
            }
            self.sink(body, mode, sink.clone(), &mut block)?;
            let value = match &pattern.kind {
                PatternKind::Constructor { data, constructor, .. } => {
                    let layout = self.data_layout(data)?;
                    Some(identifier_expression(&layout.constructors[*constructor].tag))
                }
                PatternKind::Literal(literal) => Some(self.literal(literal, pattern.monotype)),
                _ => None,
            };
            match value {
                Some(value) => cases.push(GoCase { values: vec![value], body: block }),
                None => default = Some(block),
            }
        }
        let needs_terminator = default.is_none() && matches!(sink, Sink::Return);
        out.push(GoStatement::Switch { value: Some(subject), cases, default });
        if needs_terminator {
            out.push(panic_statement("Failed pattern match"));
        }
        Ok(true)
    }

    fn alternative_tests(
        &mut self,
        paths: &[GoExpression],
        patterns: &[Pattern],
    ) -> GoResult<(Vec<GoExpression>, Vec<(Local, GoExpression)>)> {
        let mut tests = vec![];
        let mut bindings = vec![];
        for (path, pattern) in paths.iter().zip(patterns) {
            self.pattern_tests(pattern, path.clone(), &mut tests, &mut bindings)?;
        }
        Ok((tests, bindings))
    }

    fn pattern_tests(
        &mut self,
        pattern: &Pattern,
        path: GoExpression,
        tests: &mut Vec<GoExpression>,
        bindings: &mut Vec<(Local, GoExpression)>,
    ) -> GoResult<()> {
        match &pattern.kind {
            PatternKind::Wildcard => {}
            PatternKind::Variable(local) => bindings.push((local.clone(), path)),
            PatternKind::Named { local, pattern } => {
                bindings.push((local.clone(), path.clone()));
                self.pattern_tests(pattern, path, tests, bindings)?;
            }
            PatternKind::Literal(Literal::Boolean(true)) => tests.push(path),
            PatternKind::Literal(Literal::Boolean(false)) => {
                tests.push(GoExpression::Unary { operator: "!", operand: Box::new(path) })
            }
            PatternKind::Literal(literal) => {
                let literal = self.literal(literal, pattern.monotype);
                tests.push(binary("==", path, literal));
            }
            PatternKind::Array(elements) => {
                let length = call(identifier_expression("len"), vec![path.clone()]);
                tests.push(binary("==", length, GoExpression::Integer(elements.len() as i64)));
                for (position, element) in elements.iter().enumerate() {
                    let element_path = GoExpression::Index {
                        value: Box::new(path.clone()),
                        index: Box::new(GoExpression::Integer(position as i64)),
                    };
                    self.pattern_tests(element, element_path, tests, bindings)?;
                }
            }
            PatternKind::Record(fields) => {
                for (label, field_pattern) in fields {
                    self.pattern_tests(
                        field_pattern,
                        field(path.clone(), &identifier(label)),
                        tests,
                        bindings,
                    )?;
                }
            }
            PatternKind::Constructor { data, constructor, arguments } => {
                let layout = self.data_layout(data)?;
                let constructor_layout = &layout.constructors[*constructor];
                match layout.kind {
                    DataKind::Enumeration => {
                        tests.push(binary(
                            "==",
                            path.clone(),
                            identifier_expression(&constructor_layout.tag),
                        ));
                    }
                    DataKind::Tagged => {
                        tests.push(binary(
                            "==",
                            field(path.clone(), "Tag"),
                            identifier_expression(&constructor_layout.tag),
                        ));
                    }
                    DataKind::Product => {}
                }
                for ((field_name, _), argument) in constructor_layout.fields.iter().zip(arguments) {
                    self.pattern_tests(argument, field(path.clone(), field_name), tests, bindings)?;
                }
            }
        }
        Ok(())
    }
}

const RANGE_SOURCE: &str = "func rangeInt32(start int32, end int32) []int32 {
\tstep := int32(1)
\tif start > end {
\t\tstep = -1
\t}
\telements := []int32{start}
\tfor value := start; value != end; {
\t\tvalue += step
\t\telements = append(elements, value)
\t}
\treturn elements
}
";

fn is_untyped_constant(expression: &GoExpression) -> bool {
    match expression {
        GoExpression::Integer(_) | GoExpression::Float(_) | GoExpression::Rune(_) => true,
        GoExpression::Unary { operand, .. } => is_untyped_constant(operand),
        GoExpression::Binary { left, right, .. } => {
            is_untyped_constant(left) && is_untyped_constant(right)
        }
        _ => false,
    }
}

fn is_effect_node(expression: &Expression) -> bool {
    matches!(
        expression.kind,
        ExpressionKind::EffectPure(_)
            | ExpressionKind::EffectBind { .. }
            | ExpressionKind::EffectEach { .. }
            | ExpressionKind::EffectWhen { .. }
    ) || matches!(&expression.kind, ExpressionKind::Foreign { foreign, .. } if foreign.is_effectful())
        || matches!(&expression.kind, ExpressionKind::Apply { .. })
}

fn ends_in_jump(statements: &[GoStatement]) -> bool {
    matches!(statements.last(), Some(GoStatement::Return(_) | GoStatement::Continue))
        || matches!(statements.last(), Some(GoStatement::Expression(GoExpression::Call { function, .. }))
        if matches!(function.as_ref(), GoExpression::Identifier(name) if name == "panic"))
}

fn has_tail_call(expression: &Expression, function: FunctionId, arity: usize, mode: Mode) -> bool {
    match &expression.kind {
        ExpressionKind::Apply { function: callee, arguments } => {
            matches!(callee.kind, ExpressionKind::Function(id) if id == function)
                && arguments.len() == arity
        }
        ExpressionKind::Let { body, .. } => has_tail_call(body, function, arity, mode),
        ExpressionKind::If { then, otherwise, .. } => {
            has_tail_call(then, function, arity, mode)
                || has_tail_call(otherwise, function, arity, mode)
        }
        ExpressionKind::Case { alternatives, .. } => {
            alternatives.iter().any(|alternative| match &alternative.body {
                Guarded::Unconditional(body) => has_tail_call(body, function, arity, mode),
                Guarded::Guards(branches) => {
                    branches.iter().any(|branch| has_tail_call(&branch.body, function, arity, mode))
                }
            })
        }
        ExpressionKind::EffectBind { body, .. } if mode == Mode::Perform => {
            has_tail_call(body, function, arity, mode)
        }
        _ => false,
    }
}

fn captures_parameters(
    expression: &Expression,
    parameters: &[Local],
    mode: Mode,
    monotypes: &Monotypes,
) -> bool {
    let uses_parameter = |expression: &Expression| {
        parameters.iter().any(|parameter| uses_local(expression, parameter.id))
    };
    let captures = |expression: &Expression, mode: Mode| {
        captures_parameters(expression, parameters, mode, monotypes)
    };
    if mode == Mode::Value
        && is_effect_node(expression)
        && monotypes.effect_result(expression.monotype).is_some()
    {
        return uses_parameter(expression);
    }
    match &expression.kind {
        ExpressionKind::Lambda { body, .. } => uses_parameter(body),
        ExpressionKind::EffectPure(value) if mode == Mode::Perform => captures(value, Mode::Value),
        ExpressionKind::EffectBind { action, body, .. } if mode == Mode::Perform => {
            captures(action, Mode::Perform) || captures(body, Mode::Perform)
        }
        ExpressionKind::EffectEach { .. } | ExpressionKind::EffectWhen { .. }
            if mode == Mode::Perform =>
        {
            uses_parameter(expression)
        }
        ExpressionKind::EffectPure(_)
        | ExpressionKind::EffectBind { .. }
        | ExpressionKind::EffectEach { .. }
        | ExpressionKind::EffectWhen { .. } => uses_parameter(expression),
        ExpressionKind::Let { bindings, body } => {
            bindings.iter().any(|binding| captures(&binding.value, Mode::Value))
                || captures(body, mode)
        }
        ExpressionKind::If { condition, then, otherwise } => {
            captures(condition, Mode::Value) || captures(then, mode) || captures(otherwise, mode)
        }
        ExpressionKind::Case { scrutinees, alternatives } => {
            scrutinees.iter().any(|scrutinee| captures(scrutinee, Mode::Value))
                || alternatives.iter().any(|alternative| match &alternative.body {
                    Guarded::Unconditional(body) => captures(body, mode),
                    Guarded::Guards(branches) => branches.iter().any(|branch| {
                        branch.guards.iter().any(|guard| match guard {
                            Guard::Boolean(condition) => captures(condition, Mode::Value),
                            Guard::Pattern { value, .. } => captures(value, Mode::Value),
                        }) || captures(&branch.body, mode)
                    }),
                })
        }
        _ => {
            let mut captured = false;
            crate::simplify::for_each_child(expression, &mut |child| {
                captured = captured || captures(child, Mode::Value);
            });
            captured
        }
    }
}

fn render_type(type_: &GoType) -> String {
    let declaration = GoDeclaration::Type { name: "T".into(), type_: type_.clone() };
    let file = GoFile { imports: vec![], declarations: vec![declaration] };
    let rendered = file.render();
    rendered.lines().find_map(|line| line.strip_prefix("type T ")).unwrap_or("any").to_string()
}
