//! A pure call made twice with the same arguments is made once.
//!
//! `sizeOf entry = lstat (pathOf entry) <#> either (const Nothing) (regularFileOf (pathOf entry))`
//! and a guard `String.trim name == ""` followed by `{ name: String.trim name }` call the same
//! function on the same locals twice. Where the first call is made whatever happens, before an
//! effect is bound or a condition chooses, and another one follows, the value is bound once ahead
//! of both and both read it. Locals never change, so the arguments mean the same at every call.

use std::hash::{Hash, Hasher};

use rustc_hash::{FxHashMap, FxHashSet, FxHasher};
use smol_str::SmolStr;

use super::Simplifier;
use crate::foreign::{Foreign, Operator};
use crate::monomorphic::traversal::{for_each_binder_mut, for_each_child, for_each_child_mut};
use crate::monomorphic::{Binding, Expression, ExpressionKind, FunctionSpelling, LocalId};
use crate::monotype::Monotype;
use crate::naming::lower_first;

impl Simplifier<'_> {
    pub(super) fn share_repeated_calls(&mut self, body: &mut Expression) {
        // Most functions make no call twice, which one count of the calls rules out.
        let mut counts = FxHashMap::default();
        count_calls(body, &mut counts);
        let repeated = counts.into_iter().filter(|&(_, count)| count > 1).map(|(key, _)| key);
        let repeated: FxHashSet<u64> = repeated.collect();
        if repeated.is_empty() {
            return;
        }
        let mut names = FxHashMap::default();
        record_local_names(body, &mut names);
        self.share_calls(body, &names, &repeated);
    }

    fn share_calls(
        &mut self,
        expression: &mut Expression,
        names: &FxHashMap<LocalId, SmolStr>,
        repeated: &FxHashSet<u64>,
    ) {
        for_each_child_mut(expression, &mut |child| self.share_calls(child, names, repeated));
        while let Some(call) = self.repeated_call(expression, repeated) {
            let name = self.call_name(&call, names);
            let local = self.named_local(&name, call.monotype);
            replace_calls(expression, &call, local.id);
            let monotype = expression.monotype;
            let placeholder = Expression::new(ExpressionKind::Unit, monotype);
            let body = std::mem::replace(expression, placeholder);
            let bindings = vec![Binding { local, value: call }];
            let kind = ExpressionKind::Let { bindings, body: Box::new(body) };
            *expression = Expression::new(kind, monotype);
        }
    }

    /// A call that the expression makes first whatever happens, and again later.
    fn repeated_call(
        &self,
        expression: &Expression,
        repeated: &FxHashSet<u64>,
    ) -> Option<Expression> {
        let (first, later): (&Expression, Vec<&Expression>) = match &expression.kind {
            ExpressionKind::EffectBind { action, body, .. } => (action, vec![body]),
            ExpressionKind::If { condition, then, otherwise } => (condition, vec![then, otherwise]),
            _ => return None,
        };
        let mut made = vec![];
        self.calls_made_first(first, &mut made);
        made.into_iter()
            .filter(|call| call_key(call).is_some_and(|key| repeated.contains(&key)))
            .find(|call| later.iter().any(|later| mentions_call(later, call)))
            .cloned()
    }

    /// The pure calls of locals and constants that evaluating the expression makes whatever
    /// happens: outside branches, lambdas, the rest of a bind, and the right of `&&` and `||`.
    fn calls_made_first<'e>(&self, expression: &'e Expression, made: &mut Vec<&'e Expression>) {
        if self.is_pure_call(expression) {
            made.push(expression);
        }
        match &expression.kind {
            ExpressionKind::If { condition, .. } => self.calls_made_first(condition, made),
            ExpressionKind::Case { scrutinees, .. } => {
                scrutinees.iter().for_each(|scrutinee| self.calls_made_first(scrutinee, made))
            }
            ExpressionKind::EffectBind { action, .. } => self.calls_made_first(action, made),
            ExpressionKind::EffectEach { array, .. } => self.calls_made_first(array, made),
            ExpressionKind::Lambda { .. } => {}
            ExpressionKind::Foreign {
                foreign: Foreign::Operator(Operator::BooleanAnd | Operator::BooleanOr),
                arguments,
            } => {
                if let Some(first) = arguments.first() {
                    self.calls_made_first(first, made);
                }
            }
            _ => for_each_child(expression, &mut |child| self.calls_made_first(child, made)),
        }
    }

    /// A saturated call of a pure function on locals and constants whose result is data.
    fn is_pure_call(&self, expression: &Expression) -> bool {
        let data = matches!(
            self.monotypes.get(expression.monotype),
            Monotype::Int
                | Monotype::Number
                | Monotype::Boolean
                | Monotype::Char
                | Monotype::String
                | Monotype::Array(_)
                | Monotype::Record(_)
                | Monotype::Data(_)
                | Monotype::Recursive(_)
                | Monotype::ConsList(_)
        );
        if !data {
            return false;
        }
        match &expression.kind {
            ExpressionKind::Apply { function, arguments } => {
                let saturated = match function.kind {
                    ExpressionKind::Function(id) => self.functions[id.0 as usize]
                        .as_ref()
                        .is_some_and(|callee| callee.parameters.len() == arguments.len()),
                    ExpressionKind::Local(local) => {
                        !self.unsafely_effectful_locals.contains(&local)
                    }
                    _ => false,
                };
                saturated && arguments.iter().all(is_plain_argument)
            }
            ExpressionKind::Foreign { foreign, arguments } => {
                let pure = match foreign {
                    Foreign::Call { arity, .. } => *arity == arguments.len(),
                    Foreign::Project { arity, effectful, .. } => {
                        !effectful && *arity == arguments.len()
                    }
                    _ => false,
                };
                // A foreign building an array, `replicate`'s, is one that loops fuse into what they
                // do with it, which binding it would stop.
                let scalar = matches!(
                    self.monotypes.get(expression.monotype),
                    Monotype::Int
                        | Monotype::Number
                        | Monotype::Boolean
                        | Monotype::Char
                        | Monotype::String
                );
                let reads_local = arguments
                    .iter()
                    .any(|argument| matches!(argument.kind, ExpressionKind::Local(_)));
                pure && scalar && reads_local && arguments.iter().all(is_plain_argument)
            }
            _ => false,
        }
    }

    /// The name of the value a call computes: a function's own name, the name a local function
    /// was written with, or a foreign's last word, `trim` for `StringTrim`.
    fn call_name(&self, call: &Expression, names: &FxHashMap<LocalId, SmolStr>) -> SmolStr {
        let name: Option<SmolStr> = match &call.kind {
            ExpressionKind::Apply { function, .. } => match &function.kind {
                ExpressionKind::Function(id) => {
                    self.functions[id.0 as usize].as_ref().map(|callee| {
                        match self.monotypes.function_spellings.get(&callee.name) {
                            Some(FunctionSpelling::Lifted { local, .. }) => local.clone(),
                            _ => callee.name.clone(),
                        }
                    })
                }
                ExpressionKind::Local(local) => names.get(local).cloned(),
                _ => None,
            },
            ExpressionKind::Foreign { foreign: Foreign::Call { function, .. }, .. } => {
                let name = function.name;
                let last = name.rfind(|character: char| character.is_ascii_uppercase());
                let word = &name[last.unwrap_or(0)..];
                // `ShowInt`'s last word names the type it reads, not what it computes.
                let names_a_type = ["Int", "Number", "String", "Char", "Boolean", "Array"];
                (!names_a_type.contains(&word)).then(|| SmolStr::from(word))
            }
            _ => None,
        };
        // What `pathOf` computes is a path.
        let name = name.map(|name| match name.strip_suffix("Of") {
            Some(stripped) if stripped.len() > 2 => SmolStr::from(stripped),
            _ => name,
        });
        match name {
            Some(name) if !name.is_empty() => SmolStr::from(lower_first(&name)),
            _ => SmolStr::new_static("value"),
        }
    }
}

/// A hash of what a call calls and passes, the same for calls [`same_call`] finds the same.
fn call_key(expression: &Expression) -> Option<u64> {
    let mut hasher = FxHasher::default();
    let arguments = match &expression.kind {
        ExpressionKind::Apply { function, arguments } => {
            function.kind.hash(&mut hasher);
            arguments
        }
        ExpressionKind::Foreign { foreign, arguments } => {
            foreign.hash(&mut hasher);
            arguments
        }
        _ => return None,
    };
    if !arguments.iter().all(is_plain_argument) {
        return None;
    }
    arguments.iter().for_each(|argument| argument.kind.hash(&mut hasher));
    Some(hasher.finish())
}

fn count_calls(expression: &Expression, counts: &mut FxHashMap<u64, usize>) {
    if let Some(key) = call_key(expression) {
        *counts.entry(key).or_default() += 1;
    }
    for_each_child(expression, &mut |child| count_calls(child, counts));
}

fn record_local_names(expression: &mut Expression, names: &mut FxHashMap<LocalId, SmolStr>) {
    for_each_binder_mut(expression, &mut |local| {
        names.insert(local.id, local.name.clone());
    });
    for_each_child_mut(expression, &mut |child| record_local_names(child, names));
}

fn is_plain_argument(argument: &Expression) -> bool {
    matches!(
        argument.kind,
        ExpressionKind::Local(_)
            | ExpressionKind::Literal(_)
            | ExpressionKind::Unit
            | ExpressionKind::Function(_)
    )
}

fn same_call(left: &Expression, right: &Expression) -> bool {
    let same_arguments = |left: &[Expression], right: &[Expression]| {
        left.len() == right.len()
            && left.iter().zip(right).all(|(left, right)| left.kind == right.kind)
    };
    match (&left.kind, &right.kind) {
        (
            ExpressionKind::Apply { function, arguments },
            ExpressionKind::Apply { function: other, arguments: others },
        ) => function.kind == other.kind && same_arguments(arguments, others),
        (
            ExpressionKind::Foreign { foreign, arguments },
            ExpressionKind::Foreign { foreign: other, arguments: others },
        ) => foreign == other && same_arguments(arguments, others),
        _ => false,
    }
}

fn mentions_call(expression: &Expression, call: &Expression) -> bool {
    if same_call(expression, call) {
        return true;
    }
    let mut found = false;
    for_each_child(expression, &mut |child| found |= mentions_call(child, call));
    found
}

fn replace_calls(expression: &mut Expression, call: &Expression, local: LocalId) {
    if same_call(expression, call) {
        expression.kind = ExpressionKind::Local(local);
        return;
    }
    for_each_child_mut(expression, &mut |child| replace_calls(child, call, local));
}
