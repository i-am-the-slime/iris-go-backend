use super::{Simplifier, substitute_in_place};
use crate::mono::walk::for_each_alternative_child;
use crate::mono::{
    Alternative, Binding, Expression, ExpressionKind, Guarded, Literal, Local, LocalId, Pattern,
    PatternKind,
};
use crate::monotype::Monotypes;
use crate::purity::size;

impl Simplifier<'_> {
    pub(super) fn eliminate_columns(
        &mut self,
        mut scrutinees: Vec<Expression>,
        mut alternatives: Vec<Alternative>,
    ) -> (Vec<Binding>, Vec<Expression>, Vec<Alternative>) {
        let mut bindings = vec![];
        for column in (0..scrutinees.len()).rev() {
            let Some(outcomes) = column_outcomes(&scrutinees[column], &alternatives, column) else {
                continue;
            };
            let scrutinee = scrutinees.remove(column);
            let template =
                Local { id: LocalId(0), name: "scrutinee".into(), monotype: scrutinee.monotype };
            let whole = self.fresh(&template);
            let fields: Vec<Local> = match &scrutinee.kind {
                ExpressionKind::Construct { arguments, .. } => arguments
                    .iter()
                    .map(|argument| {
                        let template = Local {
                            id: LocalId(0),
                            name: "field".into(),
                            monotype: argument.monotype,
                        };
                        self.fresh(&template)
                    })
                    .collect(),
                _ => vec![],
            };
            let mut kept = Vec::with_capacity(alternatives.len());
            for (mut alternative, outcome) in alternatives.into_iter().zip(outcomes) {
                let pattern = alternative.patterns.remove(column);
                if let ColumnOutcome::Matches = outcome {
                    for (local, field) in pattern_variables(&pattern) {
                        let value = match field {
                            Some(position) => fields[position].expression(),
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
        let pattern = &alternative.patterns[column];
        let outcome = match (&pattern.kind, &scrutinee.kind) {
            (PatternKind::Wildcard | PatternKind::Variable(_), _) => ColumnOutcome::Matches,
            (
                PatternKind::Constructor { constructor, arguments, .. },
                ExpressionKind::Construct { constructor: known, .. },
            ) => {
                if constructor != known {
                    ColumnOutcome::Fails
                } else if arguments.iter().all(|argument| {
                    matches!(argument.kind, PatternKind::Wildcard | PatternKind::Variable(_))
                }) {
                    ColumnOutcome::Matches
                } else {
                    return None;
                }
            }
            (PatternKind::Literal(pattern), ExpressionKind::Literal(known)) => {
                match literals_equal(pattern, known)? {
                    true => ColumnOutcome::Matches,
                    false => ColumnOutcome::Fails,
                }
            }
            _ => return None,
        };
        outcomes.push(outcome);
    }
    Some(outcomes)
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

fn pattern_variables(pattern: &Pattern) -> Vec<(LocalId, Option<usize>)> {
    match &pattern.kind {
        PatternKind::Variable(local) => vec![(local.id, None)],
        PatternKind::Constructor { arguments, .. } => arguments
            .iter()
            .enumerate()
            .filter_map(|(position, argument)| match &argument.kind {
                PatternKind::Variable(local) => Some((local.id, Some(position))),
                _ => None,
            })
            .collect(),
        _ => vec![],
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
