use smol_str::SmolStr;

use super::reuse::{Cells, first_unused_local};
use crate::foreign::{Boundary, Foreign, Iteration};
use crate::monomorphic::traversal::{for_each_child_mut, visit};
use crate::monomorphic::{Binding, Expression, ExpressionKind, Local, LocalId, Program};
use crate::monotype::MonotypeId;

pub(super) fn hoist_field_reads(program: &Program, cells: &mut impl Cells) -> Program {
    let mut hoister = Hoister { cells, next_local: first_unused_local(program) };
    let mut functions = program.functions.clone();
    for function in &mut functions {
        hoister.expression(&mut function.body);
    }
    Program { functions, entry: program.entry }
}

struct Hoister<'a, C> {
    cells: &'a mut C,
    next_local: u32,
}

impl<C: Cells> Hoister<'_, C> {
    fn expression(&mut self, expression: &mut Expression) {
        for_each_child_mut(expression, &mut |child| self.expression(child));
        let ExpressionKind::Foreign {
            foreign:
                Foreign::Call {
                    boundary:
                        Boundary {
                            iteration:
                                Some(iteration @ (Iteration::FoldLeft | Iteration::FoldRight)),
                            ..
                        },
                    ..
                },
            arguments,
        } = &mut expression.kind
        else {
            return;
        };
        let accumulator = match iteration {
            Iteration::FoldLeft => 0,
            _ => 1,
        };
        if let [callback, _, _] = arguments.as_mut_slice() {
            self.callback(callback, accumulator, &mut vec![]);
        }
    }

    fn callback(
        &mut self,
        callback: &mut Expression,
        accumulator: usize,
        parameters: &mut Vec<Local>,
    ) {
        let ExpressionKind::Lambda { parameters: more, body } = &mut callback.kind else { return };
        parameters.extend(more.iter().cloned());
        if parameters.len() < 2 {
            self.callback(body, accumulator, parameters);
            return;
        }
        if parameters.len() != 2 || !self.cells.is_record(parameters[accumulator].monotype) {
            return;
        }
        self.hoist(body, parameters[accumulator].id);
    }

    fn hoist(&mut self, body: &mut Expression, record: LocalId) {
        let mut labels: Vec<(SmolStr, MonotypeId, usize)> = vec![];
        visit(body, &mut |expression| {
            let ExpressionKind::Access { record: accessed, label } = &expression.kind else {
                return;
            };
            if !matches!(accessed.kind, ExpressionKind::Local(id) if id == record) {
                return;
            }
            match labels.iter_mut().find(|(seen, _, _)| seen == label) {
                Some((_, _, count)) => *count += 1,
                None => labels.push((label.clone(), expression.monotype, 1)),
            }
        });
        let mut bindings = vec![];
        for (label, monotype, count) in labels {
            if count < 2 || self.cells.cell(monotype).is_none() {
                continue;
            }
            let mut read = None;
            let next_local = &mut self.next_local;
            let mut fresh = || {
                let id = LocalId(*next_local);
                *next_local += 1;
                id
            };
            replace_reads(body, record, &label, &mut fresh, &mut read);
            if let Some((local, value)) = read {
                bindings.push(Binding { local, value });
            }
        }
        if bindings.is_empty() {
            return;
        }
        let monotype = body.monotype;
        let inner = std::mem::replace(body, Expression::new(ExpressionKind::Unit, monotype));
        *body = Expression::new(ExpressionKind::Let { bindings, body: Box::new(inner) }, monotype);
    }
}

fn replace_reads(
    expression: &mut Expression,
    record: LocalId,
    label: &SmolStr,
    fresh: &mut impl FnMut() -> LocalId,
    read: &mut Option<(Local, Expression)>,
) {
    let is_read = matches!(
        &expression.kind,
        ExpressionKind::Access { record: accessed, label: accessed_label }
            if accessed_label == label
                && matches!(accessed.kind, ExpressionKind::Local(id) if id == record)
    );
    if is_read {
        let monotype = expression.monotype;
        let (local, _) = read.get_or_insert_with(|| {
            let local = Local { id: fresh(), name: label.clone(), monotype };
            (local, expression.clone())
        });
        *expression = Expression::new(ExpressionKind::Local(local.id), monotype);
        return;
    }
    for_each_child_mut(expression, &mut |child| replace_reads(child, record, label, fresh, read));
}
