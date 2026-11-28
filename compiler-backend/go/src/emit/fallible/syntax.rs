use rustc_hash::{FxHashMap, FxHashSet};

use super::Conversion;
use crate::go_traversal::Walk;
use crate::syntax::{GoExpression, GoStatement, Name};

/// `EFromResults(value, err)` of two locals, with the `Either` type it builds.
pub(super) fn joined_results(value: &GoExpression) -> Option<(String, String, String)> {
    let GoExpression::Call { function, arguments } = value.unattributed() else { return None };
    let GoExpression::Identifier(converter) = function.unattributed() else { return None };
    let shape = converter.strip_prefix('\u{0}')?.strip_suffix(Conversion::FromResults.suffix())?;
    let [value, failure] = arguments.as_slice() else { return None };
    let (GoExpression::Identifier(value), GoExpression::Identifier(failure)) =
        (value.unattributed(), failure.unattributed())
    else {
        return None;
    };
    Some((shape.to_string(), value.clone(), failure.clone()))
}

/// Whether control cannot fall out of the end of the statements.
pub(super) fn terminates(statements: &[GoStatement]) -> bool {
    match statements.iter().rev().find(|statement| !matches!(statement, GoStatement::Line(_))) {
        Some(
            GoStatement::Return(_)
            | GoStatement::Continue
            | GoStatement::Break
            | GoStatement::BreakTo(_),
        ) => true,
        Some(statement) if statement.is_panic() => true,
        Some(GoStatement::If { then, otherwise, .. }) => terminates(then) && terminates(otherwise),
        Some(GoStatement::Switch { cases, default: Some(default), .. }) => {
            cases.iter().all(|case| terminates(&case.body)) && terminates(&default.body)
        }
        _ => false,
    }
}

/// Visits every block of the statements, function literals' bodies included, outer ones first.
pub(super) fn every_block(
    body: &mut Vec<GoStatement>,
    visit: &mut impl FnMut(&mut Vec<GoStatement>),
) {
    struct Blocks<'v, F>(&'v mut F);
    impl<F: FnMut(&mut Vec<GoStatement>)> Walk for Blocks<'_, F> {
        fn block(&mut self, body: &mut Vec<GoStatement>) {
            (self.0)(body);
            body.iter_mut().for_each(|statement| self.statement(statement));
        }
    }
    Blocks(visit).block(body);
}

/// How often each of the names is read, not counting assignments to it.
pub(super) fn reads(
    body: &mut [GoStatement],
    names: &FxHashSet<String>,
) -> FxHashMap<String, usize> {
    let mut reads = FxHashMap::default();
    crate::syntax::statements_names(body, &mut |name| {
        if let Name::Reference(name) = name
            && names.contains(name.as_str())
        {
            *reads.entry(name.clone()).or_default() += 1;
        }
    });
    reads
}

/// A value whose evaluation does nothing: a name, a literal, or a struct of those.
pub(super) fn is_plain(value: &GoExpression) -> bool {
    match value.unattributed() {
        GoExpression::Identifier(_)
        | GoExpression::Qualified { .. }
        | GoExpression::Integer(_)
        | GoExpression::Float(_)
        | GoExpression::String(_)
        | GoExpression::Boolean(_)
        | GoExpression::Rune(_)
        | GoExpression::Function { .. } => true,
        GoExpression::Composite { fields, .. } => fields.iter().all(|(_, field)| is_plain(field)),
        _ => false,
    }
}
