use rustc_hash::{FxHashMap, FxHashSet};

use crate::foreign::{Foreign, Operator};
use crate::mono::walk::{for_each_child, visit};
use crate::mono::{Binding, Expression, ExpressionKind, Function, FunctionId, Local, LocalId};
use crate::monotype::{Monotype, Monotypes};

// Whether the expression runs an action in pure code anywhere inside it:
// unsafePerformEffect, or runST.
pub(crate) fn runs_any_effect(expression: &Expression) -> bool {
    let mut runs = false;
    visit(expression, &mut |node| {
        runs |= matches!(
            node.kind,
            ExpressionKind::Foreign {
                foreign: Foreign::RunEffect | Foreign::UnsafePerformEffect,
                ..
            }
        );
    });
    runs
}

/// Whether evaluating the expression runs an action in pure code, in it or in a function it
/// calls. A recursive function runs one when any of its calls does, so each function is looked
/// into once.
pub(crate) fn runs_effect(known: &impl KnownFunctions, expression: &Expression) -> bool {
    EffectSearch { known, entered: FxHashSet::default() }.runs(expression, false)
}

/// Whether applying the function the expression evaluates to runs an action in pure code.
pub(crate) fn runs_effect_when_applied(
    known: &impl KnownFunctions,
    expression: &Expression,
) -> bool {
    EffectSearch { known, entered: FxHashSet::default() }.applying_runs(expression, false)
}

struct EffectSearch<'k, K> {
    known: &'k K,
    /// The functions whose bodies this search has entered, and whether it entered them running:
    /// entering one again finds nothing the first entry would not.
    entered: FxHashSet<(FunctionId, bool)>,
}

impl<K: KnownFunctions> EffectSearch<'_, K> {
    fn runs(&mut self, expression: &Expression, running: bool) -> bool {
        match &expression.kind {
            ExpressionKind::Foreign { foreign: Foreign::UnsafePerformEffect, .. } => true,
            ExpressionKind::Foreign { foreign: Foreign::RunEffect, arguments } => {
                arguments.iter().any(|argument| self.runs(argument, true))
            }
            ExpressionKind::Lambda { .. } => false,
            ExpressionKind::EffectBind { action: built, .. }
            | ExpressionKind::EffectEach { array: built, .. }
                if !running =>
            {
                self.runs(built, running)
            }
            ExpressionKind::Apply { function, arguments } => {
                let callee_runs = match &function.kind {
                    ExpressionKind::Lambda { body, .. } => self.runs(body, running),
                    ExpressionKind::Function(id) => self.called_runs(*id, running),
                    ExpressionKind::Local(id) => self.known.runs_effect_when_applied(*id),
                    _ => self.runs(function, running),
                };
                callee_runs || arguments.iter().any(|argument| self.passed_runs(argument, running))
            }
            ExpressionKind::Foreign { arguments, .. } => {
                arguments.iter().any(|argument| self.passed_runs(argument, running))
            }
            _ => {
                let mut runs = false;
                for_each_child(expression, &mut |child| runs = runs || self.runs(child, running));
                runs
            }
        }
    }

    /// A function passed to another may be applied there.
    fn passed_runs(&mut self, argument: &Expression, running: bool) -> bool {
        self.runs(argument, running) || self.applying_runs(argument, running)
    }

    fn applying_runs(&mut self, function: &Expression, running: bool) -> bool {
        match &function.kind {
            ExpressionKind::Lambda { body, .. } => self.runs(body, running),
            ExpressionKind::Function(id) => self.called_runs(*id, running),
            ExpressionKind::Local(id) => self.known.runs_effect_when_applied(*id),
            _ => false,
        }
    }

    fn called_runs(&mut self, id: FunctionId, running: bool) -> bool {
        let known = self.known;
        let Some(callee) = known.known(id) else { return false };
        self.entered.insert((id, running)) && self.runs(&callee.body, running)
    }
}

/// Whether evaluating the expression may reach a failure: a pattern match
/// failure, a crash or a thrown exception. An argument that a foreign function
/// ignores is never evaluated.
pub(crate) fn can_fail(expression: &Expression) -> bool {
    match &expression.kind {
        ExpressionKind::Fail(_)
        | ExpressionKind::Foreign { foreign: Foreign::Crash | Foreign::Throw, .. } => true,
        ExpressionKind::Foreign { foreign, arguments } => {
            let ignored = foreign.ignored_arguments();
            arguments
                .iter()
                .enumerate()
                .any(|(position, argument)| !ignored.contains(&position) && can_fail(argument))
        }
        _ => {
            let mut fails = false;
            for_each_child(expression, &mut |child| fails = fails || can_fail(child));
            fails
        }
    }
}

/// Whether evaluating the expression costs no more than a few instructions,
/// allocates nothing and cannot fail.
pub(crate) fn is_cheap(expression: &Expression) -> bool {
    match &expression.kind {
        ExpressionKind::Literal(_)
        | ExpressionKind::Unit
        | ExpressionKind::Local(_)
        | ExpressionKind::Function(_) => true,
        ExpressionKind::Foreign { foreign: Foreign::Operator(operator), arguments }
            if *operator != Operator::ArrayIndex && *operator != Operator::StringAppend =>
        {
            arguments.iter().all(is_cheap)
        }
        ExpressionKind::Foreign { foreign: Foreign::Int64 { .. }, arguments } => {
            arguments.iter().all(is_cheap)
        }
        ExpressionKind::Access { record, .. } => is_cheap(record),
        _ => false,
    }
}

/// Whether evaluating the expression can be skipped without a trace: it is
/// pure, cannot fail, and calls nothing that could.
pub(crate) fn is_discardable(expression: &Expression) -> bool {
    match &expression.kind {
        ExpressionKind::Literal(_)
        | ExpressionKind::Unit
        | ExpressionKind::Local(_)
        | ExpressionKind::Function(_)
        | ExpressionKind::Lambda { .. } => true,
        ExpressionKind::Foreign { foreign: Foreign::Operator(operator), arguments }
            if *operator != Operator::ArrayIndex =>
        {
            arguments.iter().all(is_discardable)
        }
        ExpressionKind::Foreign { foreign: Foreign::Int64 { .. }, arguments } => {
            arguments.iter().all(is_discardable)
        }
        ExpressionKind::Construct { arguments, .. } | ExpressionKind::Array(arguments) => {
            arguments.iter().all(is_discardable)
        }
        ExpressionKind::Foreign { arguments, .. } => arguments.is_empty(),
        ExpressionKind::Record(fields) => fields.iter().all(|(_, value)| is_discardable(value)),
        ExpressionKind::Access { record: value, .. } | ExpressionKind::Coerce(value) => {
            is_discardable(value)
        }
        _ => false,
    }
}

/// Whether evaluating the expression later, or not at all, leaves the program as it was: it
/// performs no effect, cannot fail and reuses no cell in place. A pure argument a foreign uses on
/// one path only can then be built on that path.
pub(crate) fn is_deferrable(expression: &Expression) -> bool {
    let mut deferrable = true;
    visit(expression, &mut |node| {
        deferrable &= match &node.kind {
            ExpressionKind::Foreign { foreign, .. } => {
                !matches!(
                    foreign,
                    Foreign::Throw
                        | Foreign::Crash
                        | Foreign::RunEffect
                        | Foreign::UnsafePerformEffect
                        | Foreign::LazyForce
                ) && !foreign.is_effectful()
            }
            ExpressionKind::Reuse { .. }
            | ExpressionKind::Update { .. }
            | ExpressionKind::EffectPure(_)
            | ExpressionKind::EffectBind { .. }
            | ExpressionKind::EffectEach { .. }
            | ExpressionKind::Fail(_) => false,
            _ => true,
        }
    });
    deferrable
}

pub(crate) trait KnownFunctions {
    fn known(&self, id: FunctionId) -> Option<&Function>;
    fn is_recursive(&self, id: FunctionId) -> bool;

    fn runs_effect_when_applied(&self, _local: LocalId) -> bool {
        false
    }
}

pub(crate) fn does_no_work(known: &impl KnownFunctions, expression: &Expression) -> bool {
    match &expression.kind {
        ExpressionKind::Fail(_) | ExpressionKind::Lambda { .. } => true,
        ExpressionKind::Coerce(value)
        | ExpressionKind::Access { record: value, .. }
        | ExpressionKind::EffectPure(value)
        | ExpressionKind::EffectBind { action: value, .. }
        | ExpressionKind::EffectEach { array: value, .. } => does_no_work(known, value),
        ExpressionKind::Construct { arguments, .. } | ExpressionKind::Array(arguments) => {
            arguments.iter().all(|argument| does_no_work(known, argument))
        }
        ExpressionKind::Record(fields) => {
            fields.iter().all(|(_, value)| does_no_work(known, value))
        }
        ExpressionKind::Foreign { foreign, arguments } => {
            let builds_value = foreign.is_effectful() || matches!(foreign, Foreign::Identity);
            (builds_value || arguments.is_empty())
                && arguments.iter().all(|argument| does_no_work(known, argument))
        }
        ExpressionKind::Apply { function, arguments } => {
            let builds_value = match &function.kind {
                ExpressionKind::Function(id) => known.known(*id).is_some_and(|callee| {
                    callee.parameters.len() > arguments.len()
                        || (!known.is_recursive(*id) && does_no_work(known, &callee.body))
                }),
                ExpressionKind::Lambda { parameters, body } => {
                    parameters.len() > arguments.len() || does_no_work(known, body)
                }
                _ => false,
            };
            builds_value && arguments.iter().all(|argument| does_no_work(known, argument))
        }
        _ => is_trivial(expression),
    }
}

pub(crate) fn is_trivial(expression: &Expression) -> bool {
    match &expression.kind {
        ExpressionKind::Literal(_) | ExpressionKind::Unit | ExpressionKind::Local(_) => true,
        ExpressionKind::Function(_) => true,
        ExpressionKind::Foreign { arguments, .. } => arguments.is_empty(),
        ExpressionKind::Construct { arguments, .. } => arguments.is_empty(),
        ExpressionKind::Lambda { parameters, body } => is_foreign_wrapper(parameters, body),
        _ => false,
    }
}

pub(crate) fn is_foreign_wrapper(parameters: &[Local], body: &Expression) -> bool {
    let ExpressionKind::Foreign { arguments, .. } = &body.kind else { return false };
    arguments.len() == parameters.len()
        && arguments.iter().zip(parameters).all(|(argument, parameter)| {
            matches!(argument.kind, ExpressionKind::Local(id) if id == parameter.id)
        })
}

pub(crate) fn size(expression: &Expression) -> usize {
    let mut total = 0;
    visit(expression, &mut |_| total += 1);
    total
}

/// Whether the expression has at most `limit` nodes, read no further.
pub(crate) fn is_within_size(expression: &Expression, limit: usize) -> bool {
    fn counted(expression: &Expression, remaining: &mut usize) -> bool {
        if *remaining == 0 {
            return false;
        }
        *remaining -= 1;
        let mut within = true;
        for_each_child(expression, &mut |child| within = within && counted(child, remaining));
        within
    }
    counted(expression, &mut { limit })
}

/// Whether the lambda reads or writes a reference cell of its surroundings.
pub(crate) fn captures_reference(lambda: &Expression, monotypes: &Monotypes) -> bool {
    captures_free(lambda, monotypes, |monotype| matches!(monotype, Monotype::Reference(_)))
}

/// Whether the lambda refers to a local of its surroundings whose type is one `kind` accepts.
pub(crate) fn captures_free(
    lambda: &Expression,
    monotypes: &Monotypes,
    kind: impl Fn(&Monotype) -> bool,
) -> bool {
    let is_cell = |node: &Expression| {
        matches!(node.kind, ExpressionKind::Local(_)) && kind(monotypes.get(node.monotype))
    };
    let mut cells = vec![];
    visit(lambda, &mut |node| {
        if let ExpressionKind::Local(id) = node.kind
            && is_cell(node)
        {
            cells.push(id);
        }
    });
    if cells.is_empty() {
        return false;
    }
    let mut bound = FxHashMap::default();
    crate::lift::collect_binders(lambda, &mut bound);
    cells.iter().any(|id| !bound.contains_key(id))
}

#[derive(Default)]
pub(crate) struct Occurrences {
    pub(crate) total: usize,
    pub(crate) under_lambda: usize,
    /// Occurrences as the function of an application.
    pub(crate) applied: usize,
    limit: usize,
}

/// Whether the local occurs in the expression, and only as the function of calls that give it at
/// least `arity` arguments.
pub(crate) fn only_called(expression: &Expression, local: LocalId, arity: usize) -> bool {
    fn called(expression: &Expression, local: LocalId, arity: usize, seen: &mut bool) -> bool {
        match &expression.kind {
            ExpressionKind::Local(id) => *id != local,
            ExpressionKind::Apply { function, arguments } if matches!(function.kind, ExpressionKind::Local(id) if id == local) =>
            {
                *seen = true;
                arguments.len() >= arity
                    && arguments.iter().all(|argument| called(argument, local, arity, seen))
            }
            _ => {
                let mut all = true;
                for_each_child(expression, &mut |child| {
                    all = all && called(child, local, arity, seen)
                });
                all
            }
        }
    }
    let mut seen = false;
    called(expression, local, arity, &mut seen) && seen
}

/// Whether the expression refers to a local one of the bindings binds.
pub(crate) fn mentions_any(expression: &Expression, bindings: &[Binding]) -> bool {
    let mut mentioned = false;
    visit(expression, &mut |node| {
        if let ExpressionKind::Local(id) = node.kind {
            mentioned |= bindings.iter().any(|binding| binding.local.id == id);
        }
    });
    mentioned
}

/// No, one and several occurrences.
pub(crate) fn occurrences(expression: &Expression, local: LocalId) -> Occurrences {
    occurrences_up_to(expression, local, 2)
}

/// The occurrences up to `limit`, past which counting stops: telling more
/// apart means reading all of the expression.
pub(crate) fn occurrences_up_to(
    expression: &Expression,
    local: LocalId,
    limit: usize,
) -> Occurrences {
    let mut result = Occurrences { limit, ..Occurrences::default() };
    count(expression, local, false, &mut result);
    result
}

fn count(expression: &Expression, local: LocalId, under_lambda: bool, result: &mut Occurrences) {
    // Callers tell no, one and several occurrences apart, and where a single
    // one is; past the limit there is nothing more to learn.
    if result.total >= result.limit {
        return;
    }
    match &expression.kind {
        ExpressionKind::Local(id) if *id == local => {
            result.total += 1;
            if under_lambda {
                result.under_lambda += 1;
            }
        }
        ExpressionKind::Apply { function, arguments } if matches!(function.kind, ExpressionKind::Local(id) if id == local) =>
        {
            result.applied += 1;
            count(function, local, under_lambda, result);
            arguments.iter().for_each(|argument| count(argument, local, under_lambda, result));
        }
        ExpressionKind::Lambda { body, .. } => count(body, local, true, result),
        ExpressionKind::EffectEach { array, body, .. } => {
            count(array, local, under_lambda, result);
            count(body, local, true, result);
        }
        _ => for_each_child(expression, &mut |child| count(child, local, under_lambda, result)),
    }
}
