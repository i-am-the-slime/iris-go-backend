use super::{Simplifier, substitute_in_place};
use crate::monomorphic::traversal::for_each_alternative_child;
use crate::monomorphic::{
    Alternative, Binding, Expression, ExpressionKind, Guard, Guarded, GuardedBranch, Literal,
    Local, LocalId, Pattern, PatternKind,
};
use crate::monotype::{MonotypeId, Monotypes};
use crate::naming::is_vague;
use crate::purity::{can_fail, is_trivial, size};
use smol_str::SmolStr;

impl Simplifier<'_> {
    pub(super) fn eliminate_columns(
        &mut self,
        mut scrutinees: Vec<Expression>,
        mut alternatives: Vec<Alternative>,
    ) -> (Vec<Binding>, Vec<Expression>, Vec<Alternative>) {
        let mut bindings = vec![];
        self.split_known_constructions(&mut scrutinees, &mut alternatives, &mut bindings);
        for column in (0..scrutinees.len()).rev() {
            let Some(outcomes) = column_outcomes(&scrutinees[column], &alternatives, column) else {
                continue;
            };
            let scrutinee = scrutinees.remove(column);
            let name = alternatives
                .iter()
                .find_map(|alternative| match &alternative.patterns[column].kind {
                    PatternKind::Variable(local) | PatternKind::Named { local, .. }
                        if !is_vague(&local.name) =>
                    {
                        Some(local.name.clone())
                    }
                    _ => None,
                })
                .unwrap_or_else(|| "scrutinee".into());
            let template = Local { id: LocalId(0), name, monotype: scrutinee.monotype };
            let whole = self.fresh(&template);
            let fields: Vec<Local> = match &scrutinee.kind {
                ExpressionKind::Construct { arguments, .. } => {
                    let fields = arguments.iter().map(|argument| {
                        let template = Local {
                            id: LocalId(0),
                            name: "field".into(),
                            monotype: argument.monotype,
                        };
                        self.fresh(&template)
                    });
                    fields.collect()
                }
                _ => vec![],
            };
            let mut kept = Vec::with_capacity(alternatives.len());
            for (mut alternative, outcome) in alternatives.into_iter().zip(outcomes) {
                let pattern = alternative.patterns.remove(column);
                if let ColumnOutcome::Matches = outcome {
                    for (local, field) in pattern_variables(&pattern) {
                        let value = match field {
                            Some(FieldPath { position, labels }) => labels.into_iter().fold(
                                fields[position].expression(),
                                |record, (label, monotype)| {
                                    let record = Box::new(record);
                                    let kind = ExpressionKind::Access { record, label };
                                    Expression::new(kind, monotype)
                                },
                            ),
                            None => match &scrutinee.kind {
                                ExpressionKind::Construct { data, constructor, .. }
                                    if !fields.is_empty() =>
                                {
                                    let kind = ExpressionKind::Construct {
                                        data: data.clone(),
                                        constructor: *constructor,
                                        arguments: fields.iter().map(Local::expression).collect(),
                                    };
                                    Expression::new(kind, scrutinee.monotype)
                                }
                                _ => whole.expression(),
                            },
                        };
                        substitute_guarded(&mut alternative.body, local, &value, self.monotypes);
                    }
                    kept.push(alternative);
                }
            }
            alternatives = kept;
            match scrutinee.kind {
                ExpressionKind::Construct { arguments, .. } if !fields.is_empty() => {
                    for (local, value) in fields.into_iter().zip(arguments) {
                        bindings.push(Binding { local, value });
                    }
                }
                _ => bindings.push(Binding { local: whole, value: scrutinee }),
            }
        }
        (bindings, scrutinees, alternatives)
    }

    /// A column whose scrutinee is a constructor the code builds, matched by patterns that look
    /// into its fields, `Deep _ Flat` against `Deep x rest`, becomes a column for each field: the
    /// alternatives for other constructors are dropped, and one that binds the whole value gets it
    /// rebuilt from the fields.
    fn split_known_constructions(
        &mut self,
        scrutinees: &mut Vec<Expression>,
        alternatives: &mut Vec<Alternative>,
        bindings: &mut Vec<Binding>,
    ) {
        let mut column = 0;
        while column < scrutinees.len() {
            if !splits(&scrutinees[column], alternatives, column) {
                column += 1;
                continue;
            }
            let scrutinee = scrutinees.remove(column);
            let monotype = scrutinee.monotype;
            let ExpressionKind::Construct { data, constructor, arguments } = scrutinee.kind else {
                unreachable!("invariant violated: only a construction is split")
            };
            let fields = arguments.into_iter().map(|argument| {
                if is_trivial(&argument) {
                    return argument;
                }
                let monotype = argument.monotype;
                let template = Local { id: LocalId(0), name: "field".into(), monotype };
                let field = self.fresh(&template);
                let expression = field.expression();
                bindings.push(Binding { local: field, value: argument });
                expression
            });
            let fields: Vec<Expression> = fields.collect();
            let monotypes: Vec<MonotypeId> = fields.iter().map(|field| field.monotype).collect();
            let kind = ExpressionKind::Construct { data, constructor, arguments: fields.clone() };
            let rebuilt = Expression::new(kind, monotype);
            let mut kept = Vec::with_capacity(alternatives.len());
            for mut alternative in std::mem::take(alternatives) {
                let pattern = alternative.patterns.remove(column);
                let mut whole = vec![];
                let Some(parts) = field_patterns(pattern, constructor, &monotypes, &mut whole)
                else {
                    continue;
                };
                for local in whole {
                    substitute_guarded(&mut alternative.body, local, &rebuilt, self.monotypes);
                }
                alternative.patterns.splice(column..column, parts);
                kept.push(alternative);
            }
            *alternatives = kept;
            scrutinees.splice(column..column, fields);
        }
    }
}

pub(super) fn reachable(alternatives: Vec<Alternative>) -> Vec<Alternative> {
    let mut kept: Vec<Alternative> = Vec::with_capacity(alternatives.len());
    for alternative in alternatives {
        let shadowed = kept.iter().any(|earlier| {
            matches!(earlier.body, Guarded::Unconditional(_))
                && earlier
                    .patterns
                    .iter()
                    .zip(&alternative.patterns)
                    .all(|(earlier, later)| subsumes(earlier, later))
        });
        if !shadowed {
            kept.push(alternative);
        }
    }
    kept
}

/// Guards whose conditions folded to literals decided: a `true` condition
/// always holds, a branch with a `false` one is never taken, and the branches
/// after one that always holds are never reached. Guards that cannot fail
/// may be skipped; a branch whose guards might fail first is kept.
pub(super) fn decided_guards(branches: Vec<GuardedBranch>) -> Guarded {
    let mut kept: Vec<GuardedBranch> = Vec::with_capacity(branches.len());
    let mut dropped = None;
    let always_false = |guard: &Guard| literal_guard(guard) == Some(false);
    for mut branch in branches {
        let never_taken = branch.guards.iter().position(always_false);
        if let Some(position) = never_taken
            && branch.guards[..position].iter().all(|guard| !can_fail(guard_value(guard)))
        {
            dropped = Some(branch);
            continue;
        }
        branch.guards.retain(|guard| literal_guard(guard) != Some(true));
        let always_taken = branch.guards.is_empty();
        kept.push(branch);
        if always_taken {
            break;
        }
    }
    match kept.as_slice() {
        [only] if only.guards.is_empty() => {
            Guarded::Unconditional(kept.pop().expect("one branch").body)
        }
        // An alternative keeps a branch, so that it still reads as one that never matches.
        [] => Guarded::Guards(dropped.into_iter().collect()),
        _ => Guarded::Guards(kept),
    }
}

fn literal_guard(guard: &Guard) -> Option<bool> {
    match guard {
        Guard::Boolean(Expression {
            kind: ExpressionKind::Literal(Literal::Boolean(value)),
            ..
        }) => Some(*value),
        _ => None,
    }
}

fn guard_value(guard: &Guard) -> &Expression {
    match guard {
        Guard::Boolean(value) | Guard::Pattern { value, .. } => value,
    }
}

fn irrefutable(pattern: &Pattern) -> bool {
    match &pattern.kind {
        PatternKind::Wildcard | PatternKind::Variable(_) => true,
        PatternKind::Named { pattern, .. } => irrefutable(pattern),
        PatternKind::Record(fields) => fields.iter().all(|(_, field)| irrefutable(field)),
        _ => false,
    }
}

fn subsumes(earlier: &Pattern, later: &Pattern) -> bool {
    let each = |earlier: &[Pattern], later: &[Pattern]| {
        earlier.len() == later.len()
            && earlier.iter().zip(later).all(|(earlier, later)| subsumes(earlier, later))
    };
    match (&earlier.kind, &later.kind) {
        _ if irrefutable(earlier) => true,
        (PatternKind::Named { pattern, .. }, _) => subsumes(pattern, later),
        (_, PatternKind::Named { pattern, .. }) => subsumes(earlier, pattern),
        (PatternKind::Literal(earlier), PatternKind::Literal(later)) => {
            literals_equal(earlier, later) == Some(true)
        }
        (PatternKind::Array(earlier), PatternKind::Array(later)) => each(earlier, later),
        (PatternKind::Record(earlier), PatternKind::Record(later)) => {
            earlier.iter().all(|(label, field)| {
                later.iter().any(|(other, pattern)| other == label && subsumes(field, pattern))
            })
        }
        (
            PatternKind::Constructor { constructor: earlier, arguments: x, .. },
            PatternKind::Constructor { constructor: later, arguments: y, .. },
        )
        | (
            PatternKind::Closure { tag: earlier, captures: x },
            PatternKind::Closure { tag: later, captures: y },
        ) => earlier == later && each(x, y),
        _ => false,
    }
}

pub(super) enum ColumnOutcome {
    Matches,
    Fails,
}

pub(super) fn column_outcomes(
    scrutinee: &Expression,
    alternatives: &[Alternative],
    column: usize,
) -> Option<Vec<ColumnOutcome>> {
    let mut outcomes = Vec::with_capacity(alternatives.len());
    for alternative in alternatives {
        outcomes.push(pattern_outcome(&alternative.patterns[column], scrutinee)?);
    }
    Some(outcomes)
}

/// Whether a pattern matches a value the code spells out: an as-pattern as its inner pattern does.
fn pattern_outcome(pattern: &Pattern, scrutinee: &Expression) -> Option<ColumnOutcome> {
    Some(match (&pattern.kind, &scrutinee.kind) {
        (PatternKind::Wildcard | PatternKind::Variable(_), _) => ColumnOutcome::Matches,
        (PatternKind::Named { pattern, .. }, _) => pattern_outcome(pattern, scrutinee)?,
        (
            PatternKind::Constructor { constructor, arguments: patterns, .. },
            ExpressionKind::Construct { constructor: known, arguments: values, .. },
        ) => {
            if constructor != known {
                ColumnOutcome::Fails
            } else {
                let binds_or_matches = |pattern: &Pattern, value: &Expression| match pattern.kind {
                    _ if irrefutable(pattern) => Some(true),
                    _ => known_match(pattern, value),
                };
                all_of(patterns.iter().zip(values).map(|(p, v)| binds_or_matches(p, v)))?
            }
        }
        (PatternKind::Literal(pattern), ExpressionKind::Literal(known)) => {
            match literals_equal(pattern, known)? {
                true => ColumnOutcome::Matches,
                false => ColumnOutcome::Fails,
            }
        }
        _ => return None,
    })
}

/// Whether a pattern that binds nothing matches a value the code spells out, when the value
/// settles it.
fn known_match(pattern: &Pattern, value: &Expression) -> Option<bool> {
    match (&pattern.kind, &value.kind) {
        (PatternKind::Wildcard, _) => Some(true),
        (PatternKind::Literal(pattern), ExpressionKind::Literal(known)) => {
            literals_equal(pattern, known)
        }
        (
            PatternKind::Constructor { constructor, arguments: patterns, .. },
            ExpressionKind::Construct { constructor: known, arguments: values, .. },
        ) => {
            if constructor != known {
                return Some(false);
            }
            let outcomes = patterns.iter().zip(values).map(|(p, v)| known_match(p, v));
            match all_of(outcomes) {
                Some(ColumnOutcome::Matches) => Some(true),
                Some(ColumnOutcome::Fails) => Some(false),
                None => None,
            }
        }
        _ => None,
    }
}

/// The outcome of matching every one of the parts: a part known to fail decides it even when
/// another is unknown.
fn all_of(parts: impl Iterator<Item = Option<bool>>) -> Option<ColumnOutcome> {
    let mut unknown = false;
    for part in parts {
        match part {
            Some(false) => return Some(ColumnOutcome::Fails),
            Some(true) => {}
            None => unknown = true,
        }
    }
    (!unknown).then_some(ColumnOutcome::Matches)
}

fn literals_equal(left: &Literal, right: &Literal) -> Option<bool> {
    match (left, right) {
        (Literal::Int(left), Literal::Int(right)) => Some(left == right),
        (Literal::String(left), Literal::String(right)) => Some(left == right),
        (Literal::Utf16(left), Literal::Utf16(right)) => Some(left == right),
        (Literal::String(_), Literal::Utf16(_)) | (Literal::Utf16(_), Literal::String(_)) => {
            Some(false)
        }
        (Literal::Char(left), Literal::Char(right)) => Some(left == right),
        (Literal::Boolean(left), Literal::Boolean(right)) => Some(left == right),
        _ => None,
    }
}

/// A field of a matched constructor, and the record labels read on the way into it.
struct FieldPath {
    position: usize,
    labels: Vec<(SmolStr, MonotypeId)>,
}

fn pattern_variables(pattern: &Pattern) -> Vec<(LocalId, Option<FieldPath>)> {
    match &pattern.kind {
        PatternKind::Variable(local) => vec![(local.id, None)],
        PatternKind::Named { local, pattern } => {
            let mut variables = vec![(local.id, None)];
            variables.extend(pattern_variables(pattern));
            variables
        }
        PatternKind::Constructor { arguments, .. } => {
            let mut variables = vec![];
            for (position, argument) in arguments.iter().enumerate() {
                field_variables(argument, position, &mut vec![], &mut variables);
            }
            variables
        }
        _ => vec![],
    }
}

fn field_variables(
    pattern: &Pattern,
    position: usize,
    labels: &mut Vec<(SmolStr, MonotypeId)>,
    variables: &mut Vec<(LocalId, Option<FieldPath>)>,
) {
    match &pattern.kind {
        PatternKind::Variable(local) => {
            variables.push((local.id, Some(FieldPath { position, labels: labels.clone() })))
        }
        PatternKind::Named { local, pattern } => {
            variables.push((local.id, Some(FieldPath { position, labels: labels.clone() })));
            field_variables(pattern, position, labels, variables);
        }
        PatternKind::Record(fields) => {
            for (label, field) in fields {
                labels.push((label.clone(), field.monotype));
                field_variables(field, position, labels, variables);
                labels.pop();
            }
        }
        _ => {}
    }
}

fn substitute_guarded(
    guarded: &mut Guarded,
    local: LocalId,
    value: &Expression,
    monotypes: &Monotypes,
) {
    match guarded {
        Guarded::Unconditional(body) => substitute_in_place(body, local, value, monotypes),
        Guarded::Guards(branches) => {
            for branch in branches {
                for guard in &mut branch.guards {
                    substitute_in_place(guard.value_mut(), local, value, monotypes);
                }
                substitute_in_place(&mut branch.body, local, value, monotypes);
            }
        }
    }
}

/// A case whose first alternative only names its scrutinees is a let.
pub(super) fn binds_only(alternatives: &[Alternative]) -> bool {
    let Some(first) = alternatives.first() else { return false };
    matches!(first.body, Guarded::Unconditional(_))
        && first
            .patterns
            .iter()
            .all(|pattern| matches!(pattern.kind, PatternKind::Variable(_) | PatternKind::Wildcard))
}

pub(super) fn alternatives_size(alternatives: &[Alternative]) -> usize {
    let mut total = 0;
    for_each_alternative_child(alternatives, &mut |child| total += size(child));
    total
}

/// Whether a column's scrutinee builds a constructor with fields that some pattern looks into
/// further than the constructor, so that only splitting it into its fields resolves the match.
fn splits(scrutinee: &Expression, alternatives: &[Alternative], column: usize) -> bool {
    let ExpressionKind::Construct { arguments, .. } = &scrutinee.kind else { return false };
    fn splittable(pattern: &Pattern) -> bool {
        match &pattern.kind {
            PatternKind::Wildcard | PatternKind::Variable(_) | PatternKind::Constructor { .. } => {
                true
            }
            PatternKind::Named { pattern, .. } => splittable(pattern),
            _ => false,
        }
    }
    !arguments.is_empty()
        && column_outcomes(scrutinee, alternatives, column).is_none()
        && alternatives.iter().all(|alternative| splittable(&alternative.patterns[column]))
}

/// The patterns a split column's fields meet, or `None` when the pattern is for another
/// constructor; the locals that bind the whole value are added to `whole`.
fn field_patterns(
    pattern: Pattern,
    constructor: usize,
    monotypes: &[MonotypeId],
    whole: &mut Vec<LocalId>,
) -> Option<Vec<Pattern>> {
    let wildcard = |&monotype: &MonotypeId| Pattern { kind: PatternKind::Wildcard, monotype };
    let wildcards = || monotypes.iter().map(wildcard);
    match pattern.kind {
        PatternKind::Wildcard => Some(wildcards().collect()),
        PatternKind::Variable(local) => {
            whole.push(local.id);
            Some(wildcards().collect())
        }
        PatternKind::Named { local, pattern } => {
            whole.push(local.id);
            field_patterns(*pattern, constructor, monotypes, whole)
        }
        PatternKind::Constructor { constructor: matched, arguments, .. } => {
            (matched == constructor).then_some(arguments)
        }
        _ => unreachable!("invariant violated: only a splittable pattern is split"),
    }
}
