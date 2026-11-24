use super::Simplifier;
use crate::foreign::{Boundary, Foreign, GoFunction, Iteration, Operator};
use crate::monomorphic::{Alternative, Expression, ExpressionKind, Guarded, LocalId, PatternKind};
use crate::monotype::{DataType, Monotype, MonotypeId};

struct Branches {
    data: DataType,
    just: usize,
    nothing: usize,
}

impl Simplifier<'_> {
    /// `case findIndex p xs of Just i -> Just (unsafeIndex xs i); _ -> Nothing`, the arrays
    /// library's `find`, as one search that yields the element it stops at. Read by index, `xs`
    /// is needed twice and is built as an array; searched for its element, it is read once, so
    /// a pipeline that makes it runs in the search's loop.
    pub(super) fn found_element(
        &mut self,
        scrutinees: &[Expression],
        alternatives: &[Alternative],
        monotype: MonotypeId,
    ) -> Option<Expression> {
        let [scrutinee] = scrutinees else { return None };
        let ExpressionKind::Foreign { foreign, arguments } = &scrutinee.kind else { return None };
        let Foreign::Call { function, arity, boundary } = foreign else { return None };
        if boundary.iteration != Some(Iteration::FindIndex) {
            return None;
        }
        let [_, _, predicate, array] = arguments.as_slice() else { return None };
        let ExpressionKind::Local(array_local) = array.kind else { return None };
        let Monotype::Array(element) = *self.monotypes.get(array.monotype) else { return None };
        let Branches { data, just, nothing } = indexing_branches(alternatives, array_local)?;
        let found = self.named_local("found", element);
        let present = ExpressionKind::Construct {
            data: data.clone(),
            constructor: just,
            arguments: vec![found.expression()],
        };
        let present = Expression::new(present, monotype);
        let present_type = self.monotypes.function(element, monotype);
        let present = ExpressionKind::Lambda { parameters: vec![found], body: Box::new(present) };
        let present = Expression::new(present, present_type);
        let absent = ExpressionKind::Construct { data, constructor: nothing, arguments: vec![] };
        let absent = Expression::new(absent, monotype);
        let find = Foreign::Call {
            function: GoFunction { package: function.package, name: "Find" },
            arity: *arity,
            boundary: Boundary { iteration: Some(Iteration::Find), ..*boundary },
        };
        let find = ExpressionKind::Foreign {
            foreign: find.interned(),
            arguments: vec![present, absent, predicate.clone(), array.clone()],
        };
        Some(Expression::new(find, monotype))
    }
}

/// The constructors of a case that answers `Just (unsafeIndex array i)` for the position `i`
/// it finds and `Nothing` otherwise.
fn indexing_branches(alternatives: &[Alternative], array: LocalId) -> Option<Branches> {
    let [first, second] = alternatives else { return None };
    let (found, missing) = match &first.patterns[..] {
        [pattern] if matches!(&pattern.kind, PatternKind::Constructor { arguments, .. } if arguments.len() == 1) => {
            (first, second)
        }
        _ => (second, first),
    };
    let [found_pattern] = &found.patterns[..] else { return None };
    let [missing_pattern] = &missing.patterns[..] else { return None };
    let PatternKind::Constructor { arguments, .. } = &found_pattern.kind else { return None };
    let [position] = &arguments[..] else { return None };
    let PatternKind::Variable(position) = &position.kind else { return None };
    let missing_matches = match &missing_pattern.kind {
        PatternKind::Wildcard => std::ptr::eq(missing, second),
        PatternKind::Constructor { arguments, .. } => arguments.is_empty(),
        _ => false,
    };
    if !missing_matches {
        return None;
    }
    let Guarded::Unconditional(found_body) = &found.body else { return None };
    let Guarded::Unconditional(missing_body) = &missing.body else { return None };
    let ExpressionKind::Construct { data, constructor: just, arguments } = &found_body.kind else {
        return None;
    };
    let [indexed] = &arguments[..] else { return None };
    let ExpressionKind::Foreign { foreign: Foreign::Operator(Operator::ArrayIndex), arguments } =
        &indexed.kind
    else {
        return None;
    };
    let [indexed_array, indexed_position] = &arguments[..] else { return None };
    let reads_found = matches!(indexed_array.kind, ExpressionKind::Local(id) if id == array)
        && matches!(indexed_position.kind, ExpressionKind::Local(id) if id == position.id);
    if !reads_found {
        return None;
    }
    let ExpressionKind::Construct { data: missing_data, constructor: nothing, arguments } =
        &missing_body.kind
    else {
        return None;
    };
    let same_data = missing_data.file_id == data.file_id && missing_data.item == data.item;
    if !same_data || nothing == just || !arguments.is_empty() {
        return None;
    }
    Some(Branches { data: data.clone(), just: *just, nothing: *nothing })
}
