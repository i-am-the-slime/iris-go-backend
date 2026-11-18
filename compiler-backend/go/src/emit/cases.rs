//! Pattern matching: cases compiled to `if` chains and `switch` statements.

use super::{
    DataKind, DataLayout, Emitter, Exit, GuardChain, Mode, Sink, binary, breaks_to, call,
    conjunction, ends_in_panic, field, guarded_local_uses, identifier_expression, local_uses,
    unit_value,
};
use crate::error::GoResult;
use crate::mono::{Alternative, Expression, Guard, Guarded, Literal, Local, Pattern, PatternKind};
use crate::monotype::Monotype;
use crate::syntax::{GoCase, GoDefault, GoExpression, GoStatement};

impl<Q> Emitter<'_, '_, '_, Q>
where
    Q: checking::ExternalQueries,
{
    pub(super) fn case(
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
                self.bind_pattern_locals(&bindings, |local| local_uses(body, local), out)?;
                return self.sink(body, mode, sink, out);
            }
        }
        if self.try_switch(expression, &paths, scrutinees, alternatives, mode, sink.clone(), out)? {
            return Ok(());
        }
        if let Sink::Return = sink {
            return self.sequential_case(&paths, alternatives, mode, &Exit::Return, out);
        }
        let sink = self.prepare_branching_sink(sink, expression, mode, out)?;
        let mut chain: Vec<(Option<GoExpression>, Vec<GoStatement>)> = vec![];
        let mut unconditional = false;
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
                        return self.labelled_case(&paths, alternatives, mode, sink, out);
                    };
                    let mut hoisted = vec![];
                    let condition = self.value(condition, &mut hoisted)?;
                    if !hoisted.is_empty() {
                        return self.labelled_case(&paths, alternatives, mode, sink, out);
                    }
                    if !matches!(condition, GoExpression::Boolean(true)) {
                        conditions.push(condition);
                    }
                }
                let mut block = vec![];
                self.bind_pattern_locals(&bindings, |local| local_uses(body, local), &mut block)?;
                self.sink(body, mode, sink.clone(), &mut block)?;
                let condition = conjunction(conditions);
                unconditional = condition.is_none();
                chain.push((condition, block));
                if unconditional {
                    break;
                }
            }
            if unconditional {
                break;
            }
        }
        if let Some((condition, _)) = chain.last_mut() {
            *condition = None;
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

    pub(super) fn exit_with(
        &mut self,
        body: &Expression,
        mode: Mode,
        exit: &Exit,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<()> {
        match exit {
            Exit::Return => self.sink(body, mode, Sink::Return, out),
            Exit::Break { sink, label } => {
                self.sink(body, mode, sink.clone(), out)?;
                if !ends_in_panic(out) {
                    out.push(GoStatement::BreakTo(label.clone()));
                }
                Ok(())
            }
        }
    }

    pub(super) fn labelled_case(
        &mut self,
        paths: &[GoExpression],
        alternatives: &[Alternative],
        mode: Mode,
        sink: Sink,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<()> {
        let label = self.temporary("matched");
        let exit = Exit::Break { sink, label: label.clone() };
        let saved = self.tail_loop.take();
        let mut body = vec![];
        let outcome = self.sequential_case(paths, alternatives, mode, &exit, &mut body);
        self.tail_loop = saved;
        outcome?;
        if breaks_to(&body, &label) {
            out.push(GoStatement::LabeledLoop { label, body });
        } else {
            out.extend(body);
        }
        Ok(())
    }

    pub(super) fn sequential_case(
        &mut self,
        paths: &[GoExpression],
        alternatives: &[Alternative],
        mode: Mode,
        exit: &Exit,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<()> {
        for (position, alternative) in alternatives.iter().enumerate() {
            let last = position + 1 == alternatives.len();
            let (tests, bindings) = self.alternative_tests(paths, &alternative.patterns)?;
            let mut block = vec![];
            self.bind_pattern_locals(
                &bindings,
                |local| guarded_local_uses(&alternative.body, local),
                &mut block,
            )?;
            let terminates =
                self.guarded_sequential(&alternative.body, mode, exit, last, &mut block)?;
            let condition = if last { None } else { conjunction(tests) };
            match condition {
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
        unreachable!("invariant violated: the last alternative of a total case always matches")
    }

    pub(super) fn guarded_sequential(
        &mut self,
        guarded: &Guarded,
        mode: Mode,
        exit: &Exit,
        last_alternative: bool,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<bool> {
        let branches = match guarded {
            Guarded::Unconditional(body) => {
                self.exit_with(body, mode, exit, out)?;
                return Ok(true);
            }
            Guarded::Guards(branches) => branches,
        };
        for (position, branch) in branches.iter().enumerate() {
            let tested = !(last_alternative && position + 1 == branches.len());
            let terminates = self.guard_chain(
                &branch.guards,
                vec![],
                vec![],
                &branch.body,
                GuardChain { mode, exit, tested },
                out,
            )?;
            if terminates {
                return Ok(true);
            }
        }
        Ok(false)
    }

    pub(super) fn guard_chain(
        &mut self,
        guards: &[Guard],
        mut conditions: Vec<GoExpression>,
        mut bindings: Vec<(Local, GoExpression)>,
        body: &Expression,
        chain: GuardChain<'_>,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<bool> {
        let GuardChain { mode, exit, tested } = chain;
        let Some((guard, rest)) = guards.split_first() else {
            let mut block = vec![];
            self.bind_pattern_locals(&bindings, |local| local_uses(body, local), &mut block)?;
            self.exit_with(body, mode, exit, &mut block)?;
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
        if !tested {
            tests.clear();
        }
        if evaluation.is_empty() || conditions.is_empty() {
            out.extend(evaluation);
            conditions.extend(tests);
            bindings.extend(guard_bindings);
            return self.guard_chain(rest, conditions, bindings, body, chain, out);
        }
        let mut block = evaluation;
        bindings.extend(guard_bindings);
        self.guard_chain(rest, tests, bindings, body, chain, &mut block)?;
        let condition =
            conjunction(conditions).expect("invariant violated: conditions are pending");
        out.push(GoStatement::If { condition, then: block, otherwise: vec![] });
        Ok(false)
    }

    #[allow(clippy::too_many_arguments)]
    pub(super) fn try_switch(
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
                    PatternKind::Constructor { arguments, .. }
                    | PatternKind::Closure { captures: arguments, .. } => {
                        arguments.iter().all(Pattern::is_irrefutable)
                    }
                    PatternKind::Literal(
                        Literal::Int(_) | Literal::String(_) | Literal::Utf16(_) | Literal::Char(_),
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
            Monotype::Data(_) | Monotype::Function(..) => {
                let layout = match self.monotypes.get(scrutinee.monotype).clone() {
                    Monotype::Data(data) => self.data_layout(&data)?,
                    _ if self.has_closure_set(scrutinee.monotype) => {
                        self.closure_layout(scrutinee.monotype)?
                    }
                    _ => return Ok(false),
                };
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
            self.bind_pattern_locals(&bindings, |local| local_uses(body, local), &mut block)?;
            self.sink(body, mode, sink.clone(), &mut block)?;
            let value = match &pattern.kind {
                PatternKind::Constructor { data, constructor, .. } => {
                    let layout = self.data_layout(data)?;
                    Some(identifier_expression(&layout.constructors[*constructor].tag))
                }
                PatternKind::Closure { tag, .. } => {
                    let layout = self.closure_layout(pattern.monotype)?;
                    Some(identifier_expression(&layout.constructors[*tag].tag))
                }
                PatternKind::Literal(literal) => Some(self.literal(literal, pattern.monotype)),
                _ => None,
            };
            match value {
                Some(value) => cases.push(GoCase { values: vec![value], body: block }),
                None => default = Some(GoDefault { covers: vec![], body: block }),
            }
        }
        let default = default.unwrap_or_else(|| GoDefault::covering(&mut cases));
        out.push(GoStatement::Switch { value: Some(subject), cases, default: Some(default) });
        Ok(true)
    }

    pub(super) fn alternative_tests(
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

    pub(super) fn pattern_tests(
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
                    let field_path = self.read_field(path.clone(), pattern.monotype, label);
                    self.pattern_tests(field_pattern, field_path, tests, bindings)?;
                }
            }
            PatternKind::Constructor { data, constructor, arguments } => {
                let layout = self.data_layout(data)?;
                self.constructor_tests(&layout, *constructor, arguments, path, tests, bindings)?;
            }
            PatternKind::Closure { tag, captures } => {
                let layout = self.closure_layout(pattern.monotype)?;
                self.constructor_tests(&layout, *tag, captures, path, tests, bindings)?;
            }
        }
        Ok(())
    }

    pub(super) fn constructor_tests(
        &mut self,
        layout: &DataLayout,
        constructor: usize,
        arguments: &[Pattern],
        path: GoExpression,
        tests: &mut Vec<GoExpression>,
        bindings: &mut Vec<(Local, GoExpression)>,
    ) -> GoResult<()> {
        let constructor_layout = &layout.constructors[constructor];
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
        Ok(())
    }
}
