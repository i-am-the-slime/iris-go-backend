use rustc_hash::{FxHashMap, FxHashSet};

use super::buffers::{byte_slice, to_string};
use super::names::{NamePart, PendingSpelling};
use super::packages::Spelling;
use super::{
    Emitter, Mode, Sink, binary, call, has_tail_call, identifier_expression, shown_boolean,
};
use crate::error::GoResult;
use crate::foreign::{Foreign, GoFunction, Operator};
use crate::go_traversal;
use crate::monomorphic::{Expression, ExpressionKind, FunctionId, Guarded, Literal};
use crate::monotype::{Monotype, MonotypeId};
use crate::syntax::{
    GoBinaryOperator, GoBuiltin, GoDeclaration, GoExpression, GoPackage, GoStatement, GoType,
};

impl<'q, Q> Emitter<'_, '_, 'q, Q>
where
    Q: checking::ExternalQueries,
{
    pub(super) fn builds_text(&mut self, expression: &Expression) -> bool {
        match &expression.kind {
            ExpressionKind::Foreign { foreign, arguments } if is_shown_array(foreign) => {
                matches!(arguments.as_slice(), [show, _] if self.writes_elements(show))
            }
            ExpressionKind::Foreign {
                foreign: Foreign::Operator(Operator::StringAppend),
                arguments,
            } if !self.owned_snocs.contains(&std::ptr::from_ref(&arguments[0])) => {
                let mut operands = vec![];
                append_operands(expression, &mut operands);
                operands.into_iter().any(|operand| self.nests_text(operand))
            }
            _ => false,
        }
    }

    pub(super) fn buffered_text(
        &mut self,
        expression: &Expression,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<GoExpression> {
        if let ExpressionKind::Foreign { foreign, arguments } = &expression.kind
            && is_shown_array(foreign)
            && let [show, array] = arguments.as_slice()
            && let ExpressionKind::Function(id) = show.kind
        {
            let shower = self.array_show(id, array.monotype)?;
            let array = self.value(array, out)?;
            return Ok(call(identifier_expression(&shower), vec![array]));
        }
        let buffer = self.temporary("text");
        let declaration = out.len();
        out.push(GoStatement::Variable { name: buffer.clone(), type_: byte_slice(), value: None });
        self.sink(expression, Mode::Value, Sink::Write(buffer.clone()), out)?;
        if let Some(first) = out.get(declaration + 1)
            && let Some(start) = starting_value(first, &buffer)
        {
            out.remove(declaration + 1);
            let names = vec![buffer.clone()];
            out[declaration] = GoStatement::Define { names, values: vec![start] };
        }
        Ok(to_string(identifier_expression(&buffer)))
    }

    pub(super) fn write_text(
        &mut self,
        expression: &Expression,
        buffer: &str,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<bool> {
        if let Some(condition) = shown_boolean(expression) {
            let condition = self.value(condition, out)?;
            let formatted = self.format_boolean(condition);
            let appended = self.text_append(buffer, formatted);
            out.push(assign(buffer, appended));
            return Ok(true);
        }
        let (foreign, arguments) = match &expression.kind {
            ExpressionKind::Literal(Literal::String(text)) => {
                if !text.is_empty() {
                    self.write_constant(buffer, text, out);
                }
                return Ok(true);
            }
            ExpressionKind::Apply { function, arguments } => {
                return self.write_call(function, arguments, buffer, out);
            }
            ExpressionKind::Foreign { foreign, arguments } => (foreign, arguments),
            _ => return Ok(false),
        };
        if let Foreign::Operator(Operator::StringAppend) = foreign
            && !self.owned_snocs.contains(&std::ptr::from_ref(&arguments[0]))
        {
            self.sink(&arguments[0], Mode::Value, Sink::Write(buffer.to_string()), out)?;
            self.sink(&arguments[1], Mode::Value, Sink::Write(buffer.to_string()), out)?;
            return Ok(true);
        }
        let Foreign::Call { function, .. } = foreign else { return Ok(false) };
        if function.package != GoPackage::Prim {
            return Ok(false);
        }
        match (function.name, arguments.as_slice()) {
            ("ShowInt", [value]) => {
                let value = self.value(value, out)?;
                let widened = GoExpression::Conversion {
                    type_: GoType::Named("int64".into()),
                    value: Box::new(value),
                };
                let append_int = self.qualified(GoPackage::Strconv, "AppendInt");
                let decimal = GoExpression::Integer(10);
                let buffer_value = identifier_expression(buffer);
                let appended = call(append_int, vec![buffer_value, widened, decimal]);
                out.push(assign(buffer, appended));
                Ok(true)
            }
            ("ShowNumber" | "ShowString" | "ShowChar", [value]) => {
                let value = self.value(value, out)?;
                let name = match function.name {
                    "ShowNumber" => "AppendShowNumber",
                    "ShowString" => "AppendShowString",
                    _ => "AppendShowChar",
                };
                let append = self.go_function(GoFunction { package: GoPackage::Prim, name });
                out.push(assign(buffer, call(append, vec![identifier_expression(buffer), value])));
                Ok(true)
            }
            ("ShowArray", [show, array]) => self.write_array(show, array, buffer, out),
            _ => Ok(false),
        }
    }

    fn write_array(
        &mut self,
        show: &Expression,
        array: &Expression,
        buffer: &str,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<bool> {
        match &show.kind {
            ExpressionKind::Lambda { parameters, body } if parameters.len() == 1 => {
                let array = self.value(array, out)?;
                let element = self.bind_local(&parameters[0]);
                let mut shown = vec![];
                self.sink(body, Mode::Value, Sink::Write(buffer.to_string()), &mut shown)?;
                self.write_elements(buffer, element, array, shown, out);
                Ok(true)
            }
            ExpressionKind::Function(id) if self.program.function(*id).parameters.len() == 1 => {
                let writer = self.array_writer(*id, array.monotype)?;
                let array = self.value(array, out)?;
                let written = call(
                    identifier_expression(&writer),
                    vec![identifier_expression(buffer), array],
                );
                out.push(assign(buffer, written));
                Ok(true)
            }
            _ => Ok(false),
        }
    }

    fn write_elements(
        &mut self,
        buffer: &str,
        element: String,
        array: GoExpression,
        shown: Vec<GoStatement>,
        out: &mut Vec<GoStatement>,
    ) {
        let index = self.temporary("index");
        let mut body = vec![GoStatement::If {
            condition: binary(
                GoBinaryOperator::GreaterThan,
                identifier_expression(&index),
                GoExpression::Integer(0),
            ),
            then: vec![self.constant_append(buffer, ",")],
            otherwise: vec![],
        }];
        body.extend(shown);
        self.write_constant(buffer, "[", out);
        out.push(GoStatement::Range { index: Some(index), element, iterable: array, body });
        self.write_constant(buffer, "]", out);
    }

    fn array_writer(&mut self, show: FunctionId, array: MonotypeId) -> GoResult<String> {
        if let Some((name, _)) = self.array_writers.get(&show) {
            return Ok(name.clone());
        }
        let name = match self.json_global("appendShow", array) {
            Ok(name) => name,
            Err(_) => {
                let function_name = self.function_names[show.0 as usize].clone();
                self.global_name(Spelling::derived("appendArray", function_name, ""))
            }
        };
        self.array_writers.insert(show, (name.clone(), array));
        self.pending_array_writers.push(show);
        Ok(name)
    }

    /// `func ArrayInt(array []int) string`, the array shown by its writer.
    fn array_show(&mut self, show: FunctionId, array: MonotypeId) -> GoResult<String> {
        if let Some(name) = self.array_shows.get(&show) {
            return Ok(name.clone());
        }
        self.array_writer(show, array)?;
        let mut full = String::new();
        let mut parts = vec![];
        let name = match self.json_name_parts(array, &mut full, &mut parts) {
            Ok(()) => {
                if let Some(NamePart::Text(first)) = parts.first_mut() {
                    *first = crate::naming::lower_first(first);
                }
                let full = crate::naming::lower_first(&full);
                self.pending_global(full, PendingSpelling::Parts(parts))
            }
            Err(_) => {
                let function_name = self.function_names[show.0 as usize].clone();
                self.global_name(Spelling::derived("showArray", function_name, ""))
            }
        };
        self.array_shows.insert(show, name.clone());
        self.pending_array_shows.push(show);
        Ok(name)
    }

    pub(super) fn array_show_declaration(&mut self, show: FunctionId) -> GoResult<GoDeclaration> {
        let name = self.array_shows[&show].clone();
        let (writer, array) = self.array_writers[&show].clone();
        self.current = Some(show);
        self.locals.clear();
        self.local_names.clear();
        self.tail_loop = None;
        let array_name = self.local_name("array".into());
        let written = call(
            identifier_expression(&writer),
            vec![GoExpression::nil(), identifier_expression(&array_name)],
        );
        let body = vec![GoStatement::Return(Some(to_string(written)))];
        let parameters = vec![(array_name, self.go_type(array)?)];
        Ok(GoDeclaration::Function { name, parameters, result: Some(GoType::String), body })
    }

    pub(super) fn array_writer_declaration(
        &mut self,
        show: FunctionId,
    ) -> GoResult<Vec<GoDeclaration>> {
        let (name, array) = self.array_writers[&show].clone();
        self.current = Some(show);
        self.locals.clear();
        self.local_names.clear();
        self.tail_loop = None;
        self.byte_buffers.clear();
        let buffer = self.local_name("buffer".into());
        let array_name = self.local_name("array".into());
        let element = self.local_name("element".into());
        let argument = identifier_expression(&element);
        let mut shown = vec![];
        if self.is_inlined_writer(show) {
            self.write_inlined(show, vec![argument], &buffer, &mut shown)?;
        } else {
            let appended = match self.writer_for(show) {
                Some(writer) => call(
                    identifier_expression(&writer),
                    vec![identifier_expression(&buffer), argument],
                ),
                None => {
                    let show_function = identifier_expression(self.function_reference(show));
                    let shown = call(show_function, vec![argument]);
                    self.buffer_append(identifier_expression(&buffer), shown)
                }
            };
            shown.push(assign(&buffer, appended));
        }
        let mut body = vec![];
        self.write_elements(&buffer, element, identifier_expression(&array_name), shown, &mut body);
        body.push(GoStatement::Return(Some(identifier_expression(&buffer))));
        let parameters = vec![(buffer, byte_slice()), (array_name, self.go_type(array)?)];
        Ok(vec![GoDeclaration::Function { name, parameters, result: Some(byte_slice()), body }])
    }

    fn write_call(
        &mut self,
        function: &Expression,
        arguments: &[Expression],
        buffer: &str,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<bool> {
        let ExpressionKind::Function(id) = function.kind else { return Ok(false) };
        if self.program.function(id).parameters.len() != arguments.len() {
            return Ok(false);
        }
        if self.is_inlined_writer(id) {
            let values = self.values(arguments, out)?;
            self.write_inlined(id, values, buffer, out)?;
            return Ok(true);
        }
        let Some(writer) = self.writer_for(id) else { return Ok(false) };
        let mut values = vec![identifier_expression(buffer)];
        values.extend(self.values(arguments, out)?);
        out.push(assign(buffer, call(identifier_expression(&writer), values)));
        Ok(true)
    }

    fn is_inlined_writer(&mut self, id: FunctionId) -> bool {
        let function = self.program.function(id);
        let is_parameter = |expression: &Expression| match expression.kind {
            ExpressionKind::Local(local) => {
                function.parameters.iter().any(|parameter| parameter.id == local)
            }
            _ => false,
        };
        let is_constant = |expression: &Expression| {
            matches!(expression.kind, ExpressionKind::Literal(Literal::String(_)))
        };
        if shown_boolean(&function.body).is_some_and(is_parameter) {
            return self.is_writable(id);
        }
        self.is_writable(id)
            && match &function.body.kind {
                ExpressionKind::Literal(Literal::String(_)) => true,
                ExpressionKind::Foreign { foreign, arguments } if is_shown_array(foreign) => {
                    matches!(
                        arguments.as_slice(),
                        [show, array] if matches!(show.kind, ExpressionKind::Function(_)) && is_parameter(array)
                    )
                }
                ExpressionKind::Foreign { foreign, arguments } => {
                    is_shown(foreign) && arguments.iter().all(is_parameter)
                }
                ExpressionKind::If { condition, then, otherwise } => {
                    is_parameter(condition) && is_constant(then) && is_constant(otherwise)
                }
                _ => false,
            }
    }

    fn write_inlined(
        &mut self,
        id: FunctionId,
        arguments: Vec<GoExpression>,
        buffer: &str,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<()> {
        let function = self.program.function(id);
        let mut arguments_by_parameter = vec![];
        for (parameter, argument) in function.parameters.iter().zip(arguments) {
            let argument = self.hoist(argument, &parameter.name, out);
            arguments_by_parameter.push((parameter.id, argument));
        }
        let mut previous = vec![];
        for (parameter, argument) in arguments_by_parameter {
            previous.push((parameter, self.locals.insert(parameter, argument)));
        }
        let written = self.sink(&function.body, Mode::Value, Sink::Write(buffer.to_string()), out);
        for (parameter, value) in previous {
            match value {
                Some(value) => self.locals.insert(parameter, value),
                None => self.locals.remove(&parameter),
            };
        }
        written
    }

    pub(super) fn text_append(&mut self, buffer: &str, value: GoExpression) -> GoExpression {
        let buffer = identifier_expression(buffer);
        let GoExpression::Call { function, mut arguments } = value else {
            return self.buffer_append(buffer, value);
        };
        let formatted = match function.name_in(GoPackage::Strconv) {
            Some("FormatInt") => Some("AppendInt"),
            Some("FormatUint") => Some("AppendUint"),
            Some("FormatBool") => Some("AppendBool"),
            _ => None,
        };
        let Some(append) = formatted else {
            return self.buffer_append(buffer, GoExpression::Call { function, arguments });
        };
        arguments.insert(0, buffer);
        call(GoExpression::qualified(GoPackage::Strconv, append), arguments)
    }

    fn write_constant(&mut self, buffer: &str, text: &str, out: &mut Vec<GoStatement>) {
        if let Some(GoStatement::Assign { targets, values }) = out.last_mut()
            && let [GoExpression::Identifier(target)] = targets.as_slice()
            && target == buffer
            && let [GoExpression::Call { function, arguments }] = values.as_mut_slice()
            && function.is_builtin(GoBuiltin::Append)
            && let [GoExpression::Identifier(appended), GoExpression::Spread(spread)] =
                arguments.as_mut_slice()
            && appended == buffer
            && let GoExpression::String(previous) = &mut **spread
        {
            previous.push_str(text);
            return;
        }
        let appended = self
            .buffer_append(identifier_expression(buffer), GoExpression::String(text.to_string()));
        out.push(assign(buffer, appended));
    }

    fn constant_append(&mut self, buffer: &str, text: &str) -> GoStatement {
        let mut statements = vec![];
        self.write_constant(buffer, text, &mut statements);
        statements.remove(0)
    }

    fn nests_text(&mut self, expression: &Expression) -> bool {
        match &expression.kind {
            ExpressionKind::Foreign { foreign, arguments } if is_shown_array(foreign) => {
                matches!(arguments.as_slice(), [show, _] if self.writes_elements(show))
            }
            // A function that returns one of its constants hands back text it never builds:
            // appending what it returns copies as much as writing it would.
            ExpressionKind::Apply { function, arguments } => match function.kind {
                ExpressionKind::Function(id) => {
                    let function = self.program.function(id);
                    function.parameters.len() == arguments.len()
                        && !only_constants(&function.body)
                        && self.is_writable(id)
                }
                _ => false,
            },
            _ => false,
        }
    }

    fn writes_elements(&self, show: &Expression) -> bool {
        match &show.kind {
            ExpressionKind::Lambda { parameters, .. } => parameters.len() == 1,
            ExpressionKind::Function(id) => self.program.function(*id).parameters.len() == 1,
            _ => false,
        }
    }

    fn writer_for(&mut self, id: FunctionId) -> Option<String> {
        if let Some(name) = self.writers.get(&id) {
            return Some(name.clone());
        }
        if !self.is_writable(id) {
            return None;
        }
        let function_name = self.function_names[id.0 as usize].clone();
        let name = self.global_name(Spelling::derived("append", function_name, ""));
        self.writers.insert(id, name.clone());
        self.pending_writers.push(id);
        Some(name)
    }

    fn is_writable(&mut self, id: FunctionId) -> bool {
        if let Some(&writable) = self.writable.get(&id) {
            return writable;
        }
        let function = self.program.function(id);
        let writable = !function.parameters.is_empty()
            && matches!(self.monotypes.get(function.result), Monotype::String)
            && !has_tail_call(&function.body, id, function.parameters.len(), Mode::Value)
            && !self.tail_group_of.contains_key(&id);
        self.writable.insert(id, false);
        let writable = writable && self.leaves_build_text(&function.body);
        self.writable.insert(id, writable);
        writable
    }

    fn leaves_build_text(&mut self, expression: &Expression) -> bool {
        match &expression.kind {
            ExpressionKind::Let { body, .. } => self.leaves_build_text(body),
            ExpressionKind::If { then, otherwise, .. } => {
                self.leaves_build_text(then) || self.leaves_build_text(otherwise)
            }
            ExpressionKind::Case { alternatives, .. } => {
                alternatives.iter().any(|alternative| match &alternative.body {
                    Guarded::Unconditional(body) => self.leaves_build_text(body),
                    Guarded::Guards(branches) => {
                        branches.iter().any(|branch| self.leaves_build_text(&branch.body))
                    }
                })
            }
            ExpressionKind::Foreign { foreign, .. } => is_shown(foreign),
            ExpressionKind::Literal(Literal::String(_)) => true,
            ExpressionKind::Apply { function, arguments } => match function.kind {
                ExpressionKind::Function(id) => {
                    self.program.function(id).parameters.len() == arguments.len()
                        && self.is_writable(id)
                }
                _ => false,
            },
            _ => false,
        }
    }

    pub(super) fn delegate_to_writers(&mut self, declarations: &mut [GoDeclaration]) {
        let mut delegated = FxHashMap::default();
        let writers = self.writers.iter().map(|(&id, name)| (id, name.clone()));
        let writers: Vec<(FunctionId, String)> = writers.collect();
        for (id, writer) in writers {
            if self.is_inlined_writer(id) || only_constants(&self.program.function(id).body) {
                continue;
            }
            delegated.insert(self.function_names[id.0 as usize].clone(), writer);
        }
        for declaration in declarations {
            let GoDeclaration::Function { name, parameters, body, .. } = declaration else {
                continue;
            };
            let Some(writer) = delegated.get(name.as_str()) else { continue };
            let mut arguments = vec![GoExpression::nil()];
            arguments
                .extend(parameters.iter().map(|(parameter, _)| identifier_expression(parameter)));
            let written = call(identifier_expression(writer), arguments);
            *body = vec![GoStatement::Return(Some(to_string(written)))];
        }
    }

    pub(super) fn writer(&mut self, id: FunctionId) -> GoResult<Vec<GoDeclaration>> {
        let name = self.writers[&id].clone();
        let function = self.program.function(id);
        self.current = Some(id);
        self.locals.clear();
        self.local_names.clear();
        self.tail_loop = None;
        self.byte_buffers.clear();
        let buffer = self.local_name("buffer".into());
        let mut parameters = vec![(buffer.clone(), byte_slice())];
        for parameter in &function.parameters {
            let parameter_name = self.bind_local(parameter);
            let parameter_type = self.go_type(parameter.monotype)?;
            parameters.push((parameter_name, parameter_type));
        }
        let mut body = vec![];
        self.sink(&function.body, Mode::Value, Sink::Write(buffer.clone()), &mut body)?;
        body.push(GoStatement::Return(Some(identifier_expression(&buffer))));
        self.attribute(function.body.position, 0, &mut body)?;
        Ok(vec![GoDeclaration::Function { name, parameters, result: Some(byte_slice()), body }])
    }
}

fn assign(buffer: &str, value: GoExpression) -> GoStatement {
    GoStatement::Assign { targets: vec![identifier_expression(buffer)], values: vec![value] }
}

fn is_shown_array(foreign: &Foreign) -> bool {
    matches!(
        foreign,
        Foreign::Call { function: GoFunction { package: GoPackage::Prim, name: "ShowArray" }, .. }
    )
}

fn only_constants(expression: &Expression) -> bool {
    match &expression.kind {
        ExpressionKind::Literal(Literal::String(_)) => true,
        ExpressionKind::Let { body, .. } => only_constants(body),
        ExpressionKind::If { then, otherwise, .. } => {
            only_constants(then) && only_constants(otherwise)
        }
        ExpressionKind::Case { alternatives, .. } => {
            alternatives.iter().all(|alternative| match &alternative.body {
                Guarded::Unconditional(body) => only_constants(body),
                Guarded::Guards(branches) => {
                    branches.iter().all(|branch| only_constants(&branch.body))
                }
            })
        }
        _ => false,
    }
}

fn starting_value(statement: &GoStatement, buffer: &str) -> Option<GoExpression> {
    let GoStatement::Assign { targets, values } = statement else { return None };
    let [GoExpression::Identifier(target)] = targets.as_slice() else { return None };
    let [GoExpression::Call { function, arguments }] = values.as_slice() else { return None };
    if target != buffer
        || !matches!(arguments.first(), Some(GoExpression::Identifier(first)) if first == buffer)
    {
        return None;
    }
    if function.is_builtin(GoBuiltin::Append) {
        let text = match arguments.as_slice() {
            [_, GoExpression::Spread(text)] => (**text).clone(),
            [_, GoExpression::Rune(byte)] => GoExpression::String(byte.to_string()),
            _ => return None,
        };
        return Some(GoExpression::Conversion { type_: byte_slice(), value: Box::new(text) });
    }
    let mut arguments = arguments.clone();
    arguments[0] = GoExpression::nil();
    Some(call((**function).clone(), arguments))
}

fn is_shown(foreign: &Foreign) -> bool {
    match foreign {
        Foreign::Operator(Operator::StringAppend) => true,
        Foreign::Call { function: GoFunction { package: GoPackage::Prim, name }, .. } => {
            matches!(*name, "ShowArray" | "ShowInt" | "ShowNumber" | "ShowString" | "ShowChar")
        }
        _ => false,
    }
}

fn append_operands<'e>(expression: &'e Expression, operands: &mut Vec<&'e Expression>) {
    match &expression.kind {
        ExpressionKind::Foreign {
            foreign: Foreign::Operator(Operator::StringAppend),
            arguments,
        } => {
            append_operands(&arguments[0], operands);
            append_operands(&arguments[1], operands);
        }
        _ => operands.push(expression),
    }
}

/// Drops the functions that no code reaches: the string wrapper of a writer whose callers all
/// append with the writer, or a helper whose every call was found to build a constant.
pub(super) fn drop_unreached_functions(declarations: &mut Vec<GoDeclaration>) {
    let functions = declarations.iter().filter_map(|declaration| match declaration {
        GoDeclaration::Function { name, .. } if name != "main" && name != "init" => {
            Some(name.clone())
        }
        _ => None,
    });
    let functions: FxHashSet<String> = functions.collect();
    let mut references: FxHashMap<String, Vec<String>> = FxHashMap::default();
    let mut reached: Vec<String> = vec![];
    for declaration in declarations.iter_mut() {
        let own = match &*declaration {
            GoDeclaration::Function { name, .. } if functions.contains(name) => Some(name.clone()),
            _ => None,
        };
        let mut called = vec![];
        match &mut *declaration {
            GoDeclaration::Source { template: text, .. } => {
                called.extend(functions.iter().filter(|name| text.contains(name.as_str())).cloned())
            }
            GoDeclaration::Written { source: text, .. } => {
                called.extend(functions.iter().filter(|name| text.contains(name.as_str())).cloned())
            }
            declaration => {
                go_traversal::each_expression_in_declaration(declaration, |expression| {
                    if let GoExpression::Identifier(name) = expression
                        && functions.contains(name)
                    {
                        called.push(name.clone());
                    }
                })
            }
        }
        match own {
            Some(name) => references.entry(name).or_default().extend(called),
            None => reached.extend(called),
        }
    }
    let mut kept: FxHashSet<String> = FxHashSet::default();
    while let Some(name) = reached.pop() {
        if kept.insert(name.clone()) {
            reached.extend(references.remove(&name).unwrap_or_default());
        }
    }
    declarations.retain(|declaration| match declaration {
        GoDeclaration::Function { name, .. } => !functions.contains(name) || kept.contains(name),
        _ => true,
    });
}
