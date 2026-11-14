use smol_str::SmolStr;

use crate::foreign::Foreign;
use crate::mono::{Expression, ExpressionKind, FunctionId, Guard, Guarded, LocalId, RecordUpdate};
use crate::simplify::for_each_child;

#[derive(Clone, Copy)]
pub(super) struct Carried<'a> {
    pub accumulator: LocalId,
    pub field: Option<&'a SmolStr>,
}

pub(super) fn owned_snocs<'e>(
    carried: Carried<'_>,
    step: &'e Expression,
) -> Option<Vec<&'e Expression>> {
    if reads(carried, step) > 1 {
        return None;
    }
    let mut owned = vec![];
    results(carried, step, &mut owned)?;
    Some(owned)
}

#[derive(Clone, Copy)]
pub(super) struct TailCall {
    pub function: FunctionId,
    pub arity: usize,
    pub position: usize,
}

pub(super) fn owned_loop_snocs<'e>(
    carried: Carried<'_>,
    body: &'e Expression,
    tail_call: TailCall,
) -> Option<Vec<&'e Expression>> {
    if reads(carried, body) > 1 {
        return None;
    }
    let mut owned = vec![];
    loop_results(carried, body, tail_call, &mut owned)?;
    Some(owned)
}

const SHARED: usize = 2;

fn loop_results<'e>(
    carried: Carried<'_>,
    expression: &'e Expression,
    tail_call: TailCall,
    owned: &mut Vec<&'e Expression>,
) -> Option<()> {
    match &expression.kind {
        ExpressionKind::Let { body, .. } => loop_results(carried, body, tail_call, owned),
        ExpressionKind::If { then, otherwise, .. } => {
            loop_results(carried, then, tail_call, owned)?;
            loop_results(carried, otherwise, tail_call, owned)
        }
        ExpressionKind::Case { alternatives, .. } => {
            for alternative in alternatives {
                match &alternative.body {
                    Guarded::Unconditional(body) => loop_results(carried, body, tail_call, owned)?,
                    Guarded::Guards(branches) => {
                        for branch in branches {
                            loop_results(carried, &branch.body, tail_call, owned)?;
                        }
                    }
                }
            }
            Some(())
        }
        ExpressionKind::Apply { function, arguments }
            if matches!(function.kind, ExpressionKind::Function(id) if id == tail_call.function)
                && arguments.len() == tail_call.arity =>
        {
            results(carried, &arguments[tail_call.position], owned)
        }
        _ => Some(()),
    }
}

fn is_accumulator(carried: Carried<'_>, expression: &Expression) -> bool {
    matches!(expression.kind, ExpressionKind::Local(id) if id == carried.accumulator)
}

fn is_carried(carried: Carried<'_>, expression: &Expression) -> bool {
    match (&expression.kind, carried.field) {
        (ExpressionKind::Local(id), None) => *id == carried.accumulator,
        (ExpressionKind::Access { record, label }, Some(field)) => {
            label == field && is_accumulator(carried, record)
        }
        _ => false,
    }
}

fn snoc_of_carried<'e>(carried: Carried<'_>, expression: &'e Expression) -> Option<&'e Expression> {
    match &expression.kind {
        ExpressionKind::Foreign { foreign: Foreign::Snoc, arguments }
            if is_carried(carried, &arguments[0]) =>
        {
            Some(&arguments[0])
        }
        _ => None,
    }
}

fn results<'e>(
    carried: Carried<'_>,
    expression: &'e Expression,
    owned: &mut Vec<&'e Expression>,
) -> Option<()> {
    match &expression.kind {
        ExpressionKind::Let { body, .. } => results(carried, body, owned),
        ExpressionKind::If { then, otherwise, .. } => {
            results(carried, then, owned)?;
            results(carried, otherwise, owned)
        }
        ExpressionKind::Case { alternatives, .. } => {
            for alternative in alternatives {
                match &alternative.body {
                    Guarded::Unconditional(body) => results(carried, body, owned)?,
                    Guarded::Guards(branches) => {
                        for branch in branches {
                            results(carried, &branch.body, owned)?;
                        }
                    }
                }
            }
            Some(())
        }
        ExpressionKind::Fail(_) => Some(()),
        _ if carried.field.is_none() => carried_value(carried, expression, owned),
        ExpressionKind::Local(id) if *id == carried.accumulator => Some(()),
        ExpressionKind::Record(fields) => {
            let field = carried.field?;
            let (_, value) = fields.iter().find(|(label, _)| label == field)?;
            carried_value(carried, value, owned)
        }
        ExpressionKind::Update { record, updates } if is_accumulator(carried, record) => {
            let field = carried.field?;
            let updated = updates.iter().find_map(|update| match update {
                RecordUpdate::Leaf { label, value } if label == field => Some(value),
                _ => None,
            });
            match updated {
                Some(value) => carried_value(carried, value, owned),
                None => Some(()),
            }
        }
        _ => None,
    }
}

fn carried_value<'e>(
    carried: Carried<'_>,
    value: &'e Expression,
    owned: &mut Vec<&'e Expression>,
) -> Option<()> {
    if is_carried(carried, value) || matches!(value.kind, ExpressionKind::Array(_)) {
        return Some(());
    }
    owned.push(snoc_of_carried(carried, value)?);
    Some(())
}

fn reads(carried: Carried<'_>, expression: &Expression) -> usize {
    match &expression.kind {
        _ if is_carried(carried, expression) => 1,
        ExpressionKind::Local(id) if *id == carried.accumulator => 1,
        ExpressionKind::Access { record, .. } if is_accumulator(carried, record) => 0,
        ExpressionKind::Update { record, updates }
            if is_accumulator(carried, record) && overwrites(carried, updates) =>
        {
            updates.iter().map(|update| update_reads(carried, update)).sum()
        }
        ExpressionKind::Lambda { body, .. } => {
            if reads(carried, body) > 0 {
                SHARED
            } else {
                0
            }
        }
        ExpressionKind::Closure { .. }
        | ExpressionKind::EffectPure(_)
        | ExpressionKind::EffectBind { .. }
        | ExpressionKind::EffectEach { .. }
        | ExpressionKind::EffectWhen { .. } => {
            let mut total = 0;
            for_each_child(expression, &mut |child| total += reads(carried, child));
            if total > 0 { SHARED } else { 0 }
        }
        ExpressionKind::If { condition, then, otherwise } => {
            reads(carried, condition) + reads(carried, then).max(reads(carried, otherwise))
        }
        ExpressionKind::Case { scrutinees, alternatives } => {
            let scrutinised: usize =
                scrutinees.iter().map(|scrutinee| reads(carried, scrutinee)).sum();
            let branches = alternatives
                .iter()
                .map(|alternative| guarded_reads(carried, &alternative.body))
                .max()
                .unwrap_or(0);
            scrutinised + branches
        }
        _ => {
            let mut total = 0;
            for_each_child(expression, &mut |child| total += reads(carried, child));
            total
        }
    }
}

fn overwrites(carried: Carried<'_>, updates: &[RecordUpdate]) -> bool {
    let Some(field) = carried.field else { return false };
    updates
        .iter()
        .any(|update| matches!(update, RecordUpdate::Leaf { label, .. } if label == field))
}

fn update_reads(carried: Carried<'_>, update: &RecordUpdate) -> usize {
    match update {
        RecordUpdate::Leaf { value, .. } => reads(carried, value),
        RecordUpdate::Branch { updates, .. } => {
            updates.iter().map(|update| update_reads(carried, update)).sum()
        }
    }
}

fn guarded_reads(carried: Carried<'_>, guarded: &Guarded) -> usize {
    match guarded {
        Guarded::Unconditional(body) => reads(carried, body),
        Guarded::Guards(branches) => {
            let mut tested = 0;
            let mut most = 0;
            for branch in branches {
                for guard in &branch.guards {
                    tested += match guard {
                        Guard::Boolean(condition) => reads(carried, condition),
                        Guard::Pattern { value, .. } => reads(carried, value),
                    };
                }
                most = most.max(tested + reads(carried, &branch.body));
            }
            most.max(tested)
        }
    }
}
