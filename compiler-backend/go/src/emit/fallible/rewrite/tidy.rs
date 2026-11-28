use rustc_hash::{FxHashMap, FxHashSet};

use super::Rewrite;
use crate::emit::fallible::syntax::{every_block, is_plain, reads, terminates};
use crate::emit::fallible::{failure_test_of, is_no_failure, tested_failure};
use crate::emit::identifier_expression;
use crate::go_traversal::{self, Walk};
use crate::syntax::{GoExpression, GoStatement, Name};

impl Rewrite<'_> {
    /// Settles the split locals' declarations once the body is rewritten: a failure branch that
    /// ends ends the `if`, the value takes the name of the local it was copied into, and what
    /// nothing reads is `_`.
    pub(super) fn tidy(&self, body: &mut Vec<GoStatement>) {
        if self.splits.is_empty() {
            return;
        }
        let pairs: FxHashMap<String, String> = self
            .splits
            .values()
            .map(|split| (split.failure.clone(), split.value.clone()))
            .collect();
        every_block(body, &mut |block| pass_split_once(block, &pairs));
        every_block(body, &mut |block| return_early(block, &self.failure_names));
        let values = self.splits.values().map(|split| split.value.clone());
        let values: FxHashSet<String> = values.collect();
        let adopted = adopt_copies(body, &values);
        let adopted_name = |value: String| adopted.get(&value).cloned().unwrap_or(value);
        let mut split_names: FxHashSet<String> = values.into_iter().map(adopted_name).collect();
        split_names.extend(self.failure_names.iter().cloned());
        forward_moves(body, &split_names);
        split_names.extend(call_results(body));
        loop {
            let read = reads(body, &split_names);
            let before = body.clone();
            drop_unread(body, &split_names, &read);
            if *body == before {
                break;
            }
        }
        reuse_failure_names(body, &self.reusable_failures);
        declare_each_once(body, &split_names);
        every_block(body, &mut |block| {
            for statement in block.iter_mut() {
                if let GoStatement::If { condition, then, otherwise } = statement
                    && then.iter().all(|statement| matches!(statement, GoStatement::Line(_)))
                    && let Some((failure, failed)) = tested_failure(condition, &self.failure_names)
                        .map(|(failure, failed)| (failure.to_string(), failed))
                {
                    *condition = failure_test_of(&failure, !failed);
                    *then = std::mem::take(otherwise);
                }
            }
        });
    }
}

/// `if err.Failed { return j(…, zero, err) } else { return j(…, value, F{}) }` as `return j(…,
/// value, err)`: a split parameter's value is not read where there is a failure. The two calls
/// differ only there.
fn pass_split_once(block: &mut [GoStatement], pairs: &FxHashMap<String, String>) {
    for statement in block.iter_mut() {
        let GoStatement::If { condition, then, otherwise } = &*statement else { continue };
        let failures: FxHashSet<String> = pairs.keys().cloned().collect();
        let Some((failure, true)) = tested_failure(condition, &failures) else { continue };
        let value = &pairs[failure];
        let (Some(failed), Some(succeeded)) = (only_call(then), only_call(otherwise)) else {
            continue;
        };
        let Some(merged) = merged_call(failed, succeeded, failure, value) else { continue };
        *statement = merged;
    }
}

/// The one statement of a branch, when it returns or runs a call.
fn only_call(statements: &[GoStatement]) -> Option<&GoStatement> {
    let mut rest = statements.iter().filter(|statement| !matches!(statement, GoStatement::Line(_)));
    let (Some(statement), None) = (rest.next(), rest.next()) else { return None };
    let call = match statement {
        GoStatement::Return(Some(value)) | GoStatement::Expression(value) => value,
        _ => return None,
    };
    matches!(call.unattributed(), GoExpression::Call { .. }).then_some(statement)
}

fn merged_call(
    failed: &GoStatement,
    succeeded: &GoStatement,
    failure: &str,
    value: &str,
) -> Option<GoStatement> {
    let arguments = |statement: &GoStatement| match statement {
        GoStatement::Return(Some(call)) | GoStatement::Expression(call) => {
            match call.unattributed() {
                GoExpression::Call { function, arguments } => {
                    Some((function.clone(), arguments.clone()))
                }
                _ => None,
            }
        }
        _ => None,
    };
    let (failed_function, failed_arguments) = arguments(failed)?;
    let (function, mut merged) = arguments(succeeded)?;
    if failed_function.unattributed() != function.unattributed()
        || failed_arguments.len() != merged.len()
        || std::mem::discriminant(failed) != std::mem::discriminant(succeeded)
    {
        return None;
    }
    let is = |argument: &GoExpression, name: &str| matches!(argument.unattributed(), GoExpression::Identifier(found) if found == name);
    let mut index = 0;
    let mut passed = false;
    while index < merged.len() {
        if failed_arguments[index].unattributed() == merged[index].unattributed() {
            index += 1;
            continue;
        }
        let pair = index + 1 < merged.len()
            && is_plain(&failed_arguments[index])
            && is(&merged[index], value)
            && is(&failed_arguments[index + 1], failure)
            && is_no_failure(&merged[index + 1]);
        if !pair || passed {
            return None;
        }
        merged[index + 1] = identifier_expression(failure);
        passed = true;
        index += 2;
    }
    if !passed {
        return None;
    }
    let call = GoExpression::Call { function, arguments: merged };
    Some(match succeeded {
        GoStatement::Return(_) => GoStatement::Return(Some(call)),
        _ => GoStatement::Expression(call),
    })
}
/// The locals `a, err := f()` binds, whose reads dropping an unread split local can remove.
fn call_results(body: &mut Vec<GoStatement>) -> FxHashSet<String> {
    let mut results = FxHashSet::default();
    every_block(body, &mut |block| {
        for statement in block.iter() {
            if let GoStatement::Define { names, values } = statement
                && names.len() > 1
                && values.len() == 1
            {
                results.extend(names.iter().filter(|name| *name != "_").cloned());
            }
        }
    });
    results
}

/// `a, b := f(); c, d = a, b` as `c, d = f()`, when nothing else reads `a` and `b`.
fn forward_moves(body: &mut Vec<GoStatement>, names: &FxHashSet<String>) {
    let mut uses: FxHashMap<String, usize> = FxHashMap::default();
    crate::syntax::statements_names(body, &mut |name| {
        if let Name::Reference(name) | Name::Written(name) = name {
            *uses.entry(name.clone()).or_default() += 1;
        }
    });
    every_block(body, &mut |block| {
        let mut index = 0;
        while index < block.len() {
            let is_statement = |&at: &usize| !matches!(block[at], GoStatement::Line(_));
            let next = (index + 1..block.len()).find(is_statement);
            if let Some(next) = next
                && let GoStatement::Define { names: defined, values: called } = &block[index]
                && let [call] = called.as_slice()
                && defined.len() > 1
                && defined.iter().all(|name| names.contains(name) && uses.get(name) == Some(&1))
                && let GoStatement::Assign { targets, values } = &block[next]
                && values.len() == defined.len()
                && values.iter().zip(defined).all(|(value, name)| {
                    matches!(value, GoExpression::Identifier(found) if found == name)
                })
            {
                let moved = GoStatement::Assign { targets: targets.clone(), values: vec![call.clone()] };
                block[index] = moved;
                block.remove(next);
            }
            index += 1;
        }
    });
}

/// `if err != nil { return … } else { rest }` as `if err != nil { return … }` followed by the
/// rest, when the rest's locals clash with nothing around the `if`.
fn return_early(block: &mut Vec<GoStatement>, failures: &FxHashSet<String>) {
    let mut index = 0;
    while index < block.len() {
        let GoStatement::If { condition, then, otherwise } = &block[index] else {
            index += 1;
            continue;
        };
        let tests_failure = matches!(tested_failure(condition, failures), Some((_, true)));
        if !tests_failure || otherwise.is_empty() || !terminates(then) {
            index += 1;
            continue;
        }
        let bound = top_level_binders(otherwise);
        let bound: Vec<String> = bound.into_iter().collect();
        if mentions(&block[..index], &bound) || mentions(&block[index + 1..], &bound) {
            index += 1;
            continue;
        }
        let GoStatement::If { otherwise, .. } = &mut block[index] else { unreachable!() };
        let rest = std::mem::take(otherwise);
        block.splice(index + 1..index + 1, rest);
        index += 1;
    }
}

fn top_level_binders(statements: &[GoStatement]) -> FxHashSet<String> {
    let mut bound = FxHashSet::default();
    for statement in statements {
        match statement {
            GoStatement::Define { names, .. } => bound.extend(names.iter().cloned()),
            GoStatement::Variable { name, .. } => {
                bound.insert(name.clone());
            }
            _ => {}
        }
    }
    bound.remove("_");
    bound
}

/// Names a split value after the local it is copied into, `b` in `value, err := f(); b :=
/// value`, when that copy is all that reads it.
fn adopt_copies(
    body: &mut Vec<GoStatement>,
    values: &FxHashSet<String>,
) -> FxHashMap<String, String> {
    let mut binders: FxHashMap<String, usize> = FxHashMap::default();
    let mut uses: FxHashMap<String, usize> = FxHashMap::default();
    let mut written: FxHashSet<String> = FxHashSet::default();
    crate::syntax::statements_names(body, &mut |name| match name {
        Name::Binder(name) => *binders.entry(name.clone()).or_default() += 1,
        Name::Reference(name) => *uses.entry(name.clone()).or_default() += 1,
        Name::Written(name) => {
            *uses.entry(name.clone()).or_default() += 1;
            written.insert(name.clone());
        }
    });
    let mut renamed: FxHashMap<String, String> = FxHashMap::default();
    every_block(body, &mut |block| {
        block.retain(|statement| {
            if let GoStatement::Define { names, values: copied } = statement
                && let [copy] = names.as_slice()
                && let [GoExpression::Identifier(value)] = copied.as_slice()
                && values.contains(value)
                && uses.get(value) == Some(&1)
                && binders.get(copy) == Some(&1)
                && binders.get(value) == Some(&1)
                && !written.contains(copy)
                && !written.contains(value)
                && !renamed.contains_key(value)
            {
                renamed.insert(value.clone(), copy.clone());
                return false;
            }
            true
        });
    });
    if !renamed.is_empty() {
        crate::syntax::statements_names(body, &mut |name| {
            let (Name::Reference(name) | Name::Written(name) | Name::Binder(name)) = name;
            if let Some(copy) = renamed.get(name.as_str()) {
                *name = copy.clone();
            }
        });
    }
    renamed
}

/// Writes `_` for the split locals nothing reads, and leaves out their declarations.
fn drop_unread(
    body: &mut Vec<GoStatement>,
    names: &FxHashSet<String>,
    reads: &FxHashMap<String, usize>,
) {
    let unread = |name: &str| names.contains(name) && !reads.contains_key(name);
    every_block(body, &mut |block| {
        block.retain(|statement| !matches!(statement, GoStatement::Variable { name, value: None, .. } if unread(name)));
        let mut kept = Vec::with_capacity(block.len());
        for mut statement in std::mem::take(block) {
            if let GoStatement::Variable { name, value: Some(value), .. } = &statement
                && unread(name)
            {
                if !is_plain(value) {
                    kept.push(GoStatement::Assign {
                        targets: vec![identifier_expression("_")],
                        values: vec![value.clone()],
                    });
                }
                continue;
            }
            let ignored = match &mut statement {
                GoStatement::Define { names, values } => {
                    for name in names.iter_mut() {
                        if unread(name) {
                            *name = "_".into();
                        }
                    }
                    names.iter().all(|name| name == "_") && values.len() == 1
                }
                GoStatement::Assign { targets, values } => {
                    for target in targets.iter_mut() {
                        if let GoExpression::Identifier(name) = target
                            && unread(name)
                        {
                            *name = "_".into();
                        }
                    }
                    let ignored = |target: &GoExpression| matches!(target, GoExpression::Identifier(name) if name == "_");
                    if values.len() == targets.len() && values.len() > 1 {
                        let pairs: Vec<(GoExpression, GoExpression)> = std::mem::take(targets)
                            .into_iter()
                            .zip(std::mem::take(values))
                            .filter(|(target, value)| !(ignored(target) && is_plain(value)))
                            .collect();
                        (*targets, *values) = pairs.into_iter().unzip();
                        if targets.is_empty() {
                            continue;
                        }
                    }
                    targets.iter().all(ignored) && values.len() == 1
                }
                _ => false,
            };
            let (
                true,
                GoStatement::Define { mut values, .. } | GoStatement::Assign { mut values, .. },
            ) = (ignored, statement.clone())
            else {
                kept.push(statement);
                continue;
            };
            let value = values.pop().expect("invariant violated: one value");
            match value.unattributed() {
                GoExpression::Call { .. } => kept.push(GoStatement::Expression(value)),
                _ if is_plain(&value) => {}
                _ => kept.push(GoStatement::Assign {
                    targets: vec![identifier_expression("_")],
                    values: vec![value],
                }),
            }
        }
        *block = kept;
    });
}

/// Names a failure local after an earlier one of its type in the same block that nothing reads
/// from there on, as Go code reuses `err`.
fn reuse_failure_names(body: &mut Vec<GoStatement>, reusable: &FxHashMap<String, String>) {
    let captured = captured(body);
    let mut renamed: FxHashMap<String, String> = FxHashMap::default();
    every_block(body, &mut |block| {
        let mut current: FxHashMap<&String, Vec<String>> = FxHashMap::default();
        for index in 0..block.len() {
            let GoStatement::Define { names, .. } = &block[index] else { continue };
            for name in names.clone() {
                let Some(kind) = reusable.get(&name) else { continue };
                if captured.contains(&name) {
                    continue;
                }
                match current.get_mut(kind) {
                    Some(group) if !mentions(&block[index + 1..], group) => {
                        renamed.insert(name.clone(), group[0].clone());
                        group.push(name);
                    }
                    _ => {
                        current.insert(kind, vec![name]);
                    }
                }
            }
        }
    });
    if renamed.is_empty() {
        return;
    }
    crate::syntax::statements_names(body, &mut |name| {
        let (Name::Reference(name) | Name::Written(name) | Name::Binder(name)) = name;
        if let Some(earlier) = renamed.get(name.as_str()) {
            *name = earlier.clone();
        }
    });
}

/// Whether the statements mention one of the names.
fn mentions(statements: &[GoStatement], wanted: &[String]) -> bool {
    let mut statements = statements.to_vec();
    let mut found = false;
    crate::syntax::statements_names(&mut statements, &mut |name| {
        let (Name::Reference(name) | Name::Written(name) | Name::Binder(name)) = name;
        found |= wanted.contains(name);
    });
    found
}

/// `_, err = f()` where `err` is already declared in the block, since `:=` declares something.
fn declare_each_once(body: &mut Vec<GoStatement>, names: &FxHashSet<String>) {
    every_block(body, &mut |block| {
        let mut declared: FxHashSet<String> = FxHashSet::default();
        for statement in block.iter_mut() {
            match statement {
                GoStatement::Define { names: defined, values } => {
                    let new = defined.iter().any(|name| name != "_" && !declared.contains(name));
                    if !new && defined.iter().any(|name| names.contains(name)) {
                        *statement = GoStatement::Assign {
                            targets: defined
                                .iter()
                                .map(|name| identifier_expression(name))
                                .collect(),
                            values: std::mem::take(values),
                        };
                        continue;
                    }
                    declared.extend(defined.iter().filter(|name| *name != "_").cloned());
                }
                GoStatement::Variable { name, .. } => {
                    declared.insert(name.clone());
                }
                _ => {}
            }
        }
    });
}

/// The locals of a function body that function literals in it refer to but do not bind.
fn captured(body: &mut [GoStatement]) -> FxHashSet<String> {
    struct Literals(FxHashSet<String>);
    impl Walk for Literals {
        fn expression(&mut self, value: &mut GoExpression) {
            if let GoExpression::Function { parameters, body, .. } = value {
                let bound = parameters.iter().map(|(parameter, _)| parameter.clone());
                let mut bound: FxHashSet<String> = bound.collect();
                let mut referred = FxHashSet::default();
                crate::syntax::statements_names(body, &mut |name| match name {
                    Name::Binder(name) => {
                        bound.insert(name.clone());
                    }
                    Name::Reference(name) | Name::Written(name) => {
                        referred.insert(name.clone());
                    }
                });
                self.0.extend(referred.into_iter().filter(|name| !bound.contains(name)));
            }
            go_traversal::expression(self, value);
        }
    }
    let mut literals = Literals(FxHashSet::default());
    body.iter_mut().for_each(|statement| literals.statement(statement));
    literals.0
}
