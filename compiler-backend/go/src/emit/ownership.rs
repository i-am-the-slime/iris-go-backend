use smol_str::SmolStr;

use crate::foreign::{self, Foreign, Operator};
use crate::mono::{
    Expression, ExpressionKind, FunctionId, Guard, Guarded, LocalId, PatternKind, RecordUpdate,
};
use crate::simplify::for_each_child;

/// Where an accumulator keeps the array, or the string, that a loop appends to.
#[derive(Clone)]
pub(super) enum Place {
    /// The accumulator itself.
    Whole,
    /// A field of the accumulator record, by its label and its Go field.
    Field(SmolStr, String),
    /// The field at `index` of the accumulator's constructor `constructor`, read through the
    /// locals that a `case` on the accumulator binds to it. `go_field` is its Go field.
    Constructor { constructor: usize, index: usize, go_field: String },
}

#[derive(Clone, Copy)]
pub(super) struct Carried<'a> {
    pub accumulator: LocalId,
    pub place: &'a Place,
    /// The locals that patterns bind to the carried constructor field.
    aliases: &'a [LocalId],
}

impl<'a> Carried<'a> {
    pub(super) fn new(accumulator: LocalId, place: &'a Place) -> Carried<'a> {
        Carried { accumulator, place, aliases: &[] }
    }
}

/// The appends in `step` that may extend the carried value in place, when the step reads it
/// only to append to it or to return it unchanged.
pub(super) fn owned_snocs<'e>(
    carried: Carried<'_>,
    step: &'e Expression,
) -> Option<Vec<&'e Expression>> {
    let aliases = aliases(carried, step)?;
    let carried = Carried { aliases: &aliases, ..carried };
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
    let aliases = aliases(carried, body)?;
    let carried = Carried { aliases: &aliases, ..carried };
    if reads(carried, body) > 1 {
        return None;
    }
    let mut owned = vec![];
    loop_results(carried, body, tail_call, &mut owned)?;
    Some(owned)
}

/// The locals bound to the carried constructor field by patterns on the accumulator; none when
/// a pattern binds the accumulator as a whole, which would read it once more.
fn aliases(carried: Carried<'_>, expression: &Expression) -> Option<Vec<LocalId>> {
    let Place::Constructor { constructor, index, .. } = *carried.place else {
        return Some(vec![]);
    };
    let mut aliases = vec![];
    let mut whole = false;
    crate::simplify::visit(expression, &mut |expression| {
        let ExpressionKind::Case { scrutinees, alternatives } = &expression.kind else { return };
        for (position, scrutinee) in scrutinees.iter().enumerate() {
            if !is_accumulator(carried, scrutinee) {
                continue;
            }
            for alternative in alternatives {
                match &alternative.patterns[position].kind {
                    PatternKind::Constructor { constructor: matched, arguments, .. }
                        if *matched == constructor =>
                    {
                        match &arguments[index].kind {
                            PatternKind::Variable(local) => aliases.push(local.id),
                            PatternKind::Wildcard => {}
                            _ => whole = true,
                        }
                    }
                    PatternKind::Constructor { .. } | PatternKind::Wildcard => {}
                    _ => whole = true,
                }
            }
        }
    });
    (!whole).then_some(aliases)
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
    match (&expression.kind, carried.place) {
        (ExpressionKind::Local(id), Place::Whole) => *id == carried.accumulator,
        (ExpressionKind::Access { record, label }, Place::Field(field, _)) => {
            label == field && is_accumulator(carried, record)
        }
        (ExpressionKind::Local(id), Place::Constructor { .. }) => carried.aliases.contains(id),
        _ => false,
    }
}

/// `snoc carried x`, `carried <> [x, …]` or, for a string, `carried <> s`: the carried value,
/// which an owned append extends in place.
fn snoc_of_carried<'e>(carried: Carried<'_>, expression: &'e Expression) -> Option<&'e Expression> {
    let ExpressionKind::Foreign { foreign, arguments } = &expression.kind else { return None };
    let appends = match foreign {
        Foreign::Snoc | Foreign::Operator(Operator::StringAppend) => true,
        _ => {
            foreign.calls(foreign::ARRAY_APPEND)
                && matches!(arguments[1].kind, ExpressionKind::Array(_))
        }
    };
    (appends && is_carried(carried, &arguments[0])).then_some(&arguments[0])
}

fn owned_appends_of<'e>(
    carried: Carried<'_>,
    expression: &'e Expression,
    owned: &mut Vec<&'e Expression>,
) -> Option<()> {
    if let Some(snoc) = snoc_of_carried(carried, expression) {
        owned.push(snoc);
        return Some(());
    }
    let ExpressionKind::Foreign { foreign: Foreign::Operator(Operator::StringAppend), arguments } =
        &expression.kind
    else {
        return None;
    };
    owned_appends_of(carried, &arguments[0], owned)?;
    owned.push(&arguments[0]);
    Some(())
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
        _ if matches!(carried.place, Place::Whole) => carried_value(carried, expression, owned),
        ExpressionKind::Local(id) if *id == carried.accumulator => Some(()),
        ExpressionKind::Construct { constructor, arguments, .. } => match *carried.place {
            Place::Constructor { constructor: carrying, index, .. } if *constructor == carrying => {
                carried_value(carried, &arguments[index], owned)
            }
            Place::Constructor { .. } => Some(()),
            _ => None,
        },
        ExpressionKind::Record(fields) => {
            let Place::Field(field, _) = carried.place else { return None };
            let (_, value) = fields.iter().find(|(label, _)| label == field)?;
            carried_value(carried, value, owned)
        }
        ExpressionKind::Update { record, updates } if is_accumulator(carried, record) => {
            let Place::Field(field, _) = carried.place else { return None };
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
    owned_appends_of(carried, value, owned)
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
        | ExpressionKind::EffectEach { .. } => {
            let mut total = 0;
            for_each_child(expression, &mut |child| total += reads(carried, child));
            if total > 0 { SHARED } else { 0 }
        }
        ExpressionKind::If { condition, then, otherwise } => {
            reads(carried, condition) + reads(carried, then).max(reads(carried, otherwise))
        }
        ExpressionKind::Case { scrutinees, alternatives } => {
            // Matching a constructor on the accumulator reads the carried field only through
            // the aliases the patterns bind.
            let destructured = |scrutinee: &Expression| {
                matches!(carried.place, Place::Constructor { .. })
                    && is_accumulator(carried, scrutinee)
            };
            let scrutinised: usize = scrutinees
                .iter()
                .filter(|scrutinee| !destructured(scrutinee))
                .map(|scrutinee| reads(carried, scrutinee))
                .sum();
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
    let Place::Field(field, _) = carried.place else { return false };
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
