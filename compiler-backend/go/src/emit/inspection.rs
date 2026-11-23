use super::reuse::{Cells, first_unused_local};
use super::uses_local;
use crate::foreign::{Foreign, Operator};
use crate::monomorphic::traversal::{for_each_child, for_each_child_mut, visit};
use crate::monomorphic::{
    Binding, Expression, ExpressionKind, FunctionId, Local, LocalId, Program,
};

pub(super) fn inspecting_functions(program: &Program) -> Vec<bool> {
    let count = program.functions.len();
    let mut inspecting = vec![true; count];
    let mut referrers: Vec<Vec<FunctionId>> = vec![vec![]; count];
    let mut demoted = vec![];
    for (index, function) in program.functions.iter().enumerate() {
        let id = FunctionId(index as u32);
        let mut keeps = false;
        visit(&function.body, &mut |expression| match &expression.kind {
            ExpressionKind::Function(referenced) => referrers[referenced.0 as usize].push(id),
            ExpressionKind::Foreign { foreign, .. } => keeps |= may_keep(foreign),
            ExpressionKind::Apply { function, .. } => {
                keeps |= !matches!(function.kind, ExpressionKind::Function(_));
            }
            ExpressionKind::Closure { .. } => keeps = true,
            _ => {}
        });
        if keeps {
            inspecting[index] = false;
            demoted.push(id);
        }
    }
    while let Some(id) = demoted.pop() {
        for &referrer in &referrers[id.0 as usize] {
            if inspecting[referrer.0 as usize] {
                inspecting[referrer.0 as usize] = false;
                demoted.push(referrer);
            }
        }
    }
    inspecting
}

fn may_keep(foreign: &Foreign) -> bool {
    matches!(
        foreign,
        Foreign::Project { .. }
            | Foreign::UnsafeCoerce
            | Foreign::UnsafePerformEffect
            | Foreign::Identity
    )
}

pub(super) fn inspects(
    inspecting: &[bool],
    cells: &mut impl Cells,
    call: &Expression,
    argument: &Expression,
) -> bool {
    if !matches!(argument.kind, ExpressionKind::Local(_)) {
        return false;
    }
    let Some(cell) = cells.cell(argument.monotype) else { return false };
    let reads = match &call.kind {
        ExpressionKind::Apply { function, .. } => {
            matches!(function.kind, ExpressionKind::Function(id) if inspecting[id.0 as usize])
        }
        ExpressionKind::Foreign { foreign, arguments } => {
            !may_keep(foreign)
                && arguments.iter().all(|other| {
                    std::ptr::eq(other, argument) || !cells.holds(other.monotype, &cell)
                })
        }
        _ => false,
    };
    reads && !cells.holds(call.monotype, &cell)
}

pub(super) fn sequence_inspections(
    program: &Program,
    inspecting: &[bool],
    cells: &mut impl Cells,
) -> Program {
    let mut sequencer = Sequencer { inspecting, cells, next_local: first_unused_local(program) };
    let mut functions = program.functions.clone();
    for function in &mut functions {
        sequencer.expression(&mut function.body);
    }
    Program { functions, entry: program.entry }
}

struct Sequencer<'a, C> {
    inspecting: &'a [bool],
    cells: &'a mut C,
    next_local: u32,
}

impl<C: Cells> Sequencer<'_, C> {
    fn expression(&mut self, expression: &mut Expression) {
        for_each_child_mut(expression, &mut |child| self.expression(child));
        let Some(arguments) = strict_arguments(expression) else { return };
        let Some(last) = self.last_inspection(&arguments) else { return };
        let mut bindings = vec![];
        let arguments = strict_arguments_mut(expression)
            .expect("invariant violated: strict arguments vanished while sequencing them");
        for argument in arguments.into_iter().take(last + 1) {
            if is_trivial(argument) {
                continue;
            }
            let id = LocalId(self.next_local);
            self.next_local += 1;
            let monotype = argument.monotype;
            let reference = Expression::new(ExpressionKind::Local(id), monotype);
            let value = std::mem::replace(argument, reference);
            let local = Local { id, name: "argument".into(), monotype };
            bindings.push(Binding { local, value });
        }
        if bindings.is_empty() {
            return;
        }
        let monotype = expression.monotype;
        let call = std::mem::replace(expression, Expression::new(ExpressionKind::Unit, monotype));
        let body = Box::new(call);
        *expression = Expression::new(ExpressionKind::Let { bindings, body }, monotype);
    }

    fn last_inspection(&mut self, arguments: &[&Expression]) -> Option<usize> {
        let mut last = None;
        for (position, argument) in arguments.iter().enumerate() {
            let later = &arguments[position + 1..];
            for local in self.inspected_locals(argument) {
                if later.iter().any(|other| uses_local(other, local))
                    && self.only_inspects(argument, local)
                {
                    last = Some(position);
                }
            }
        }
        last
    }

    fn inspected_locals(&mut self, expression: &Expression) -> Vec<LocalId> {
        let mut locals = vec![];
        visit(expression, &mut |call| {
            let arguments = match &call.kind {
                ExpressionKind::Apply { arguments, .. }
                | ExpressionKind::Foreign { arguments, .. } => arguments,
                _ => return,
            };
            for argument in arguments {
                if let ExpressionKind::Local(local) = argument.kind
                    && !locals.contains(&local)
                    && inspects(self.inspecting, self.cells, call, argument)
                {
                    locals.push(local);
                }
            }
        });
        locals
    }

    fn only_inspects(&mut self, expression: &Expression, local: LocalId) -> bool {
        match &expression.kind {
            ExpressionKind::Local(id) => *id != local,
            ExpressionKind::Lambda { .. }
            | ExpressionKind::Closure { .. }
            | ExpressionKind::EffectPure(_)
            | ExpressionKind::EffectBind { .. }
            | ExpressionKind::EffectEach { .. } => !uses_local(expression, local),
            ExpressionKind::Apply { function, arguments } => {
                self.only_inspects(function, local)
                    && self.only_inspects_arguments(expression, arguments, local)
            }
            ExpressionKind::Foreign { arguments, .. } => {
                self.only_inspects_arguments(expression, arguments, local)
            }
            _ => {
                let mut only = true;
                for_each_child(expression, &mut |child| {
                    only = only && self.only_inspects(child, local);
                });
                only
            }
        }
    }

    fn only_inspects_arguments(
        &mut self,
        call: &Expression,
        arguments: &[Expression],
        local: LocalId,
    ) -> bool {
        arguments.iter().all(|argument| match argument.kind {
            ExpressionKind::Local(id) if id == local => {
                inspects(self.inspecting, self.cells, call, argument)
            }
            _ => self.only_inspects(argument, local),
        })
    }
}

fn strict_arguments(expression: &Expression) -> Option<Vec<&Expression>> {
    match &expression.kind {
        ExpressionKind::Apply { function, arguments } if is_trivial(function) => {
            Some(arguments.iter().collect())
        }
        ExpressionKind::Construct { arguments, .. } | ExpressionKind::Array(arguments) => {
            Some(arguments.iter().collect())
        }
        ExpressionKind::Foreign { foreign, arguments } if is_strict(foreign) => {
            Some(arguments.iter().collect())
        }
        ExpressionKind::Record(fields) => Some(fields.iter().map(|(_, value)| value).collect()),
        _ => None,
    }
}

fn strict_arguments_mut(expression: &mut Expression) -> Option<Vec<&mut Expression>> {
    match &mut expression.kind {
        ExpressionKind::Apply { function, arguments } if is_trivial(function) => {
            Some(arguments.iter_mut().collect())
        }
        ExpressionKind::Construct { arguments, .. } | ExpressionKind::Array(arguments) => {
            Some(arguments.iter_mut().collect())
        }
        ExpressionKind::Foreign { foreign, arguments } if is_strict(foreign) => {
            Some(arguments.iter_mut().collect())
        }
        ExpressionKind::Record(fields) => Some(fields.iter_mut().map(|(_, value)| value).collect()),
        _ => None,
    }
}

fn is_strict(foreign: &Foreign) -> bool {
    match foreign {
        Foreign::Operator(operator) => {
            !matches!(operator, Operator::BooleanAnd | Operator::BooleanOr)
        }
        Foreign::Int64 { .. } => true,
        Foreign::Call { boundary, .. } => {
            boundary.lazy.is_empty() && !boundary.thunk && boundary.iteration.is_none()
        }
        _ => false,
    }
}

fn is_trivial(expression: &Expression) -> bool {
    matches!(
        expression.kind,
        ExpressionKind::Local(_)
            | ExpressionKind::Function(_)
            | ExpressionKind::Literal(_)
            | ExpressionKind::Unit
    )
}
