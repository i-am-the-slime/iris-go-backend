use super::{Emitter, Mode, identifier_expression, tail_calls};
use crate::monomorphic::traversal::visit;
use crate::monomorphic::{Expression, ExpressionKind, Function, FunctionId, Literal, Program};
use crate::syntax::{GoExpression, GoStatement, GoType, StructField};

const LEAST_CARRIED_PARAMETERS: usize = 8;

pub(super) struct LoopState {
    pub name: String,
    pub positions: Vec<usize>,
    pub definition: GoStatement,
}

impl LoopState {
    pub fn place(&self, parameter: &str) -> GoExpression {
        GoExpression::Field {
            value: Box::new(identifier_expression(&self.name)),
            name: parameter.to_string(),
        }
    }
}

impl<'q, Q> Emitter<'_, '_, 'q, Q>
where
    Q: checking::ExternalQueries,
{
    pub(super) fn loop_state(
        &mut self,
        id: FunctionId,
        function: &Function,
        mode: Mode,
        parameters: &[(String, GoType)],
        excluded: &[usize],
    ) -> Option<LoopState> {
        let calls = tail_calls(&function.body, id, function.parameters.len(), mode);
        let positions = carried_positions(function, &calls, excluded);
        if positions.len() < LEAST_CARRIED_PARAMETERS {
            return None;
        }
        let initial = initial_literals(self.program, id, &calls, &positions);
        let name = self.local_name("state".into());
        let mut fields = vec![];
        let mut values = vec![];
        for (position, literal) in positions.iter().zip(initial) {
            let (parameter, type_) = &parameters[*position];
            fields.push(StructField::new(parameter.clone(), type_.clone()));
            let value = match literal {
                Some(literal) => self.literal(&literal, function.parameters[*position].monotype),
                None => identifier_expression(parameter),
            };
            values.push((Some(parameter.clone()), value));
        }
        let composite = GoExpression::Composite { type_: GoType::Struct(fields), fields: values };
        let definition = GoStatement::Define { names: vec![name.clone()], values: vec![composite] };
        let state = LoopState { name, positions, definition };
        for position in &state.positions {
            let place = state.place(&parameters[*position].0);
            self.locals.insert(function.parameters[*position].id, place);
        }
        Some(state)
    }
}

fn carried_positions(
    function: &Function,
    calls: &[&[Expression]],
    excluded: &[usize],
) -> Vec<usize> {
    let passed_along = |position: usize| {
        let parameter = function.parameters[position].id;
        let unchanged = |arguments: &[Expression]| {
            let ExpressionKind::Local(local) = arguments[position].kind else { return false };
            local == parameter
        };
        calls.iter().filter(|arguments| unchanged(arguments)).count()
    };
    (0..function.parameters.len())
        .filter(|position| !excluded.contains(position))
        .filter(|position| (1..calls.len()).contains(&passed_along(*position)))
        .collect()
}

fn initial_literals(
    program: &Program,
    id: FunctionId,
    tail_calls: &[&[Expression]],
    positions: &[usize],
) -> Vec<Option<Literal>> {
    let arity = program.function(id).parameters.len();
    let jumps = tail_calls.iter().map(|arguments| arguments.as_ptr());
    let jumps: Vec<*const Expression> = jumps.collect();
    let mut references = 0;
    let mut entries: Vec<Vec<Option<Literal>>> = vec![];
    for function in &program.functions {
        visit(&function.body, &mut |expression| match &expression.kind {
            ExpressionKind::Function(callee) if *callee == id => references += 1,
            ExpressionKind::Apply { function, arguments }
                if matches!(function.kind, ExpressionKind::Function(callee) if callee == id)
                    && arguments.len() == arity
                    && !jumps.contains(&arguments.as_ptr()) =>
            {
                let literal = |position: &usize| match &arguments[*position].kind {
                    ExpressionKind::Literal(literal) => Some(literal.clone()),
                    _ => None,
                };
                entries.push(positions.iter().map(literal).collect());
            }
            _ => {}
        });
    }
    let unknown = vec![None; positions.len()];
    if id == program.entry || entries.is_empty() || references != entries.len() + jumps.len() {
        return unknown;
    }
    let shared = |index: usize| {
        let first = entries[0][index].clone()?;
        entries.iter().all(|entry| entry[index].as_ref() == Some(&first)).then_some(first)
    };
    (0..positions.len()).map(shared).collect()
}
