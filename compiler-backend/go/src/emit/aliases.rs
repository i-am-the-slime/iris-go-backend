use rustc_hash::FxHashSet;

use crate::go_traversal::{self, Walk};
use crate::syntax::{GoDeclaration, GoExpression, GoStatement, GoType};

pub(super) fn substitute_aliases(declarations: &mut [GoDeclaration]) {
    for declaration in declarations {
        let guarded = Guarded::of(declaration);
        go_traversal::each_block_in_declaration(declaration, |block| {
            let mut position = 0;
            while position < block.len() {
                if !substitute_at(block, position, &guarded) {
                    position += 1;
                }
            }
            drop_self_assignments(block);
            assign_directly(block);
            name_values_after_their_aliases(block);
            return_directly(block);
        });
    }
}

/// `alias := value` for `original := value` followed by `alias := original`, where nothing else
/// mentions `original` and nothing writes `alias`: an erased newtype's wrapper leaves such an
/// alias behind, and the value reads better under the name the PureScript gave it.
fn name_values_after_their_aliases(block: &mut Vec<GoStatement>) {
    let mut position = 0;
    while position < block.len() {
        let renamed = defined_alias(&block[position]).and_then(|(alias, original)| {
            let definition = (0..position).rev().find(|&earlier| {
                matches!(&block[earlier], GoStatement::Define { names, .. }
                    if names.len() == 1 && names[0] == original)
            })?;
            let (before, after) = block.split_at_mut(position);
            let between = &mut before[definition + 1..];
            let quiet = between
                .iter_mut()
                .all(|statement| !mentions(statement, &original) && !mentions(statement, &alias))
                && after[1..]
                    .iter_mut()
                    .all(|statement| !mentions(statement, &original) && !writes(statement, &alias));
            quiet.then_some((definition, alias))
        });
        match renamed {
            Some((definition, alias)) => {
                let GoStatement::Define { names, .. } = &mut block[definition] else {
                    unreachable!()
                };
                names[0] = alias;
                block.remove(position);
            }
            None => position += 1,
        }
    }
}

fn substitute_at(block: &mut Vec<GoStatement>, position: usize, guarded: &Guarded) -> bool {
    let Some((alias, original)) = defined_alias(&block[position]) else { return false };
    if guarded.written_in_literal(&alias) || !guarded.is_local(&original) {
        return false;
    }
    let rest = &mut block[position + 1..];
    let Some(last) = last_read(rest, &alias) else { return false };
    if guarded.written_in_literal(&original) && rest[..=last].iter_mut().any(calls) {
        return false;
    }
    if rest.iter_mut().any(|statement| writes(statement, &alias)) {
        return false;
    }
    if read_before_written(&mut rest[..=last], &alias, &original, false).is_none() {
        return false;
    }
    for statement in rest {
        go_traversal::each_expression_in_statement(statement, |expression| {
            if is_named(expression, &alias) {
                *expression = GoExpression::Identifier(original.clone());
            }
        });
    }
    block.remove(position);
    true
}

fn defined_alias(statement: &GoStatement) -> Option<(String, String)> {
    let GoStatement::Define { names, values } = statement else { return None };
    let [alias] = names.as_slice() else { return None };
    let [GoExpression::Identifier(original)] = values.as_slice() else { return None };
    (alias != original && original != "nil").then(|| (alias.clone(), original.clone()))
}

fn last_read(rest: &mut [GoStatement], alias: &str) -> Option<usize> {
    let mut last = None;
    for (offset, statement) in rest.iter_mut().enumerate() {
        match reads(statement, alias) {
            Read::Never => {}
            Read::Plainly => last = Some(offset),
            Read::InLiteral => return None,
        }
    }
    last
}

fn read_before_written(
    block: &mut [GoStatement],
    alias: &str,
    original: &str,
    mut written: bool,
) -> Option<bool> {
    for statement in block {
        let read = !matches!(reads(statement, alias), Read::Never);
        if read && written {
            return None;
        }
        written = match statement {
            GoStatement::If { then, otherwise, .. } => {
                let after_then = read_before_written(then, alias, original, written)?;
                let after_otherwise = read_before_written(otherwise, alias, original, written)?;
                after_then || after_otherwise
            }
            GoStatement::IfAssert { then, .. } => {
                read_before_written(then, alias, original, written)?
            }
            GoStatement::Switch { cases, default, .. } => {
                let mut after = written;
                for body in cases.iter_mut().map(|case| &mut case.body) {
                    after |= read_before_written(body, alias, original, written)?;
                }
                if let Some(default) = default {
                    after |= read_before_written(&mut default.body, alias, original, written)?;
                }
                after
            }
            GoStatement::Range { body, .. }
            | GoStatement::Counting { body, .. }
            | GoStatement::CountingDown { body, .. }
            | GoStatement::Loop(body)
            | GoStatement::LabeledLoop { body, .. } => {
                let writes_in_body = body.iter_mut().any(|statement| writes(statement, original));
                let reads_in_body = body
                    .iter_mut()
                    .any(|statement| !matches!(reads(statement, alias), Read::Never));
                if writes_in_body && reads_in_body {
                    return None;
                }
                written || writes_in_body
            }
            statement => written || writes(statement, original),
        };
    }
    Some(written)
}

enum Read {
    Never,
    Plainly,
    InLiteral,
}

fn reads(statement: &mut GoStatement, name: &str) -> Read {
    let mut reads = Reads { name, count: 0, in_literal: false, read_in_literal: false };
    reads.statement(statement);
    match (reads.count, reads.read_in_literal) {
        (_, true) => Read::InLiteral,
        (0, false) => Read::Never,
        _ => Read::Plainly,
    }
}

struct Reads<'a> {
    name: &'a str,
    count: usize,
    in_literal: bool,
    read_in_literal: bool,
}

impl Walk for Reads<'_> {
    fn expression(&mut self, value: &mut GoExpression) {
        match value {
            GoExpression::Identifier(name) if name == self.name => {
                self.count += 1;
                self.read_in_literal |= self.in_literal;
            }
            GoExpression::Function { .. } => {
                let enclosing = std::mem::replace(&mut self.in_literal, true);
                go_traversal::expression(self, value);
                self.in_literal = enclosing;
            }
            _ => go_traversal::expression(self, value),
        }
    }
}

pub(super) fn calls(statement: &mut GoStatement) -> bool {
    let mut found = false;
    go_traversal::each_expression_in_statement(statement, |expression| {
        found |= matches!(expression, GoExpression::Call { .. });
    });
    found
}

pub(super) fn mentions(statement: &mut GoStatement, name: &str) -> bool {
    !matches!(reads(statement, name), Read::Never) || writes(statement, name)
}

pub(super) fn writes(statement: &mut GoStatement, name: &str) -> bool {
    let mut writes = Writes { name, written: false };
    writes.statement(statement);
    writes.written
}

struct Writes<'a> {
    name: &'a str,
    written: bool,
}

impl Walk for Writes<'_> {
    fn statement(&mut self, statement: &mut GoStatement) {
        let bound: Vec<&str> = match statement {
            GoStatement::Assign { targets, .. } => {
                targets.iter().filter_map(|target| target_root(target)).collect()
            }
            GoStatement::Define { names, .. } => names.iter().map(String::as_str).collect(),
            GoStatement::Variable { name, .. } | GoStatement::IfAssert { name, .. } => vec![name],
            GoStatement::Range { element, index, .. } => {
                index.iter().map(String::as_str).chain([element.as_str()]).collect()
            }
            GoStatement::Counting { variable, .. } | GoStatement::CountingDown { variable, .. } => {
                vec![variable.as_str()]
            }
            _ => vec![],
        };
        if bound.contains(&self.name) {
            self.written = true;
        }
        go_traversal::statement(self, statement);
    }

    fn expression(&mut self, value: &mut GoExpression) {
        if let GoExpression::Address(inner) = value
            && is_named(inner, self.name)
        {
            self.written = true;
        }
        if let GoExpression::Call { function, arguments } = value
            && matches!(&**function, GoExpression::Identifier(builtin) if builtin == "delete" || builtin == "clear")
            && arguments.first().is_some_and(|changed| is_named(changed, self.name))
        {
            self.written = true;
        }
        go_traversal::expression(self, value);
    }
}

pub(super) fn target_root(target: &GoExpression) -> Option<&str> {
    match target {
        GoExpression::Identifier(name) => Some(name),
        GoExpression::Field { value, .. } | GoExpression::Index { value, .. } => target_root(value),
        _ => None,
    }
}

pub(super) struct Guarded {
    read: FxHashSet<String>,
    written: FxHashSet<String>,
    bound: FxHashSet<String>,
}

impl Guarded {
    pub(super) fn of(declaration: &mut GoDeclaration) -> Self {
        let guarded = Guarded { read: default(), written: default(), bound: default() };
        let mut literals = Literals { guarded };
        go_traversal::declaration(&mut literals, declaration);
        let mut bound = Bound { names: default() };
        if let GoDeclaration::Function { parameters, .. } = declaration {
            bound.names.extend(parameters.iter().map(|(name, _)| name.clone()));
        }
        go_traversal::declaration(&mut bound, declaration);
        literals.guarded.bound = bound.names;
        literals.guarded
    }

    pub(super) fn is_local(&self, name: &str) -> bool {
        self.bound.contains(name)
    }

    pub(super) fn written_in_literal(&self, name: &str) -> bool {
        self.written.contains(name)
    }

    pub(super) fn mentioned_in_literal(&self, name: &str) -> bool {
        self.read.contains(name) || self.written.contains(name)
    }
}

fn default<T: Default>() -> T {
    T::default()
}

struct Bound {
    names: FxHashSet<String>,
}

impl Walk for Bound {
    fn statement(&mut self, statement: &mut GoStatement) {
        match statement {
            GoStatement::Define { names, .. } => self.names.extend(names.iter().cloned()),
            GoStatement::Variable { name, .. } | GoStatement::IfAssert { name, .. } => {
                self.names.insert(name.clone());
            }
            GoStatement::Range { element, index, .. } => {
                self.names.extend(index.iter().chain([&*element]).cloned());
            }
            GoStatement::Counting { variable, .. } | GoStatement::CountingDown { variable, .. } => {
                self.names.insert(variable.clone());
            }
            _ => {}
        }
        go_traversal::statement(self, statement);
    }

    fn expression(&mut self, value: &mut GoExpression) {
        if let GoExpression::Function { parameters, .. } = value {
            self.names.extend(parameters.iter().map(|(name, _)| name.clone()));
        }
        go_traversal::expression(self, value);
    }
}

struct Literals {
    guarded: Guarded,
}

impl Walk for Literals {
    fn expression(&mut self, value: &mut GoExpression) {
        match value {
            GoExpression::Function { parameters, body, .. } => {
                let (read, written) = Free::of(parameters, body, &mut self.guarded);
                self.guarded.read.extend(read);
                self.guarded.written.extend(written);
            }
            GoExpression::Address(inner) => {
                if let Some(root) = target_root(inner) {
                    self.guarded.written.insert(root.to_string());
                }
                go_traversal::expression(self, value);
            }
            _ => go_traversal::expression(self, value),
        }
    }
}

struct Free<'g> {
    read: FxHashSet<String>,
    written: FxHashSet<String>,
    bound: FxHashSet<String>,
    guarded: &'g mut Guarded,
}

impl<'g> Free<'g> {
    fn of(
        parameters: &[(String, GoType)],
        body: &mut Vec<GoStatement>,
        guarded: &'g mut Guarded,
    ) -> (FxHashSet<String>, FxHashSet<String>) {
        let bound = parameters.iter().map(|(name, _)| name.clone()).collect();
        let mut free = Free { read: default(), written: default(), bound, guarded };
        free.block(body);
        let Free { mut read, mut written, bound, .. } = free;
        read.retain(|name| !bound.contains(name));
        written.retain(|name| !bound.contains(name));
        (read, written)
    }
}

impl Walk for Free<'_> {
    fn statement(&mut self, statement: &mut GoStatement) {
        match statement {
            GoStatement::Assign { targets, values } => {
                for target in targets.iter_mut() {
                    if let Some(root) = target_root(target) {
                        self.written.insert(root.to_string());
                    }
                    self.expression(target);
                }
                values.iter_mut().for_each(|value| self.expression(value));
                return;
            }
            GoStatement::Define { names, .. } => self.bound.extend(names.iter().cloned()),
            GoStatement::Variable { name, .. } | GoStatement::IfAssert { name, .. } => {
                self.bound.insert(name.clone());
            }
            GoStatement::Range { element, index, .. } => {
                self.bound.extend(index.iter().chain([&*element]).cloned());
            }
            GoStatement::Counting { variable, .. } | GoStatement::CountingDown { variable, .. } => {
                self.bound.insert(variable.clone());
            }
            _ => {}
        }
        go_traversal::statement(self, statement);
    }

    fn expression(&mut self, value: &mut GoExpression) {
        match value {
            GoExpression::Identifier(name) => {
                self.read.insert(name.clone());
            }
            GoExpression::Function { parameters, body, .. } => {
                let (read, written) = Free::of(parameters, body, self.guarded);
                self.guarded.read.extend(read.iter().cloned());
                self.guarded.written.extend(written.iter().cloned());
                self.read.extend(read);
                self.written.extend(written);
            }
            GoExpression::Address(inner) => {
                if let Some(root) = target_root(inner) {
                    self.written.insert(root.to_string());
                }
                go_traversal::expression(self, value);
            }
            _ => go_traversal::expression(self, value),
        }
    }
}

/// `variable = value` for `staged := value` directly followed by `variable = staged`, where
/// nothing else reads `staged`: `total = total + i`, which prints as `total += i`.
fn assign_directly(block: &mut Vec<GoStatement>) {
    let mut position = 0;
    while position < block.len() {
        let Some(next) =
            (position + 1..block.len()).find(|&next| !matches!(block[next], GoStatement::Line(_)))
        else {
            break;
        };
        let staged = match (&block[position], &block[next]) {
            (
                GoStatement::Define { names, values: defined },
                GoStatement::Assign { targets, values },
            ) => match (names.as_slice(), defined.as_slice(), targets.as_slice(), &values[..]) {
                (
                    [staged],
                    [_],
                    [GoExpression::Identifier(variable)],
                    [GoExpression::Identifier(read)],
                ) if read == staged && variable != staged => Some(staged.clone()),
                _ => None,
            },
            _ => None,
        };
        let Some(staged) = staged else {
            position += 1;
            continue;
        };
        let read_later = block[next + 1..]
            .iter_mut()
            .any(|statement| !matches!(reads(statement, &staged), Read::Never));
        if read_later {
            position += 1;
            continue;
        }
        let GoStatement::Define { values, .. } = block.remove(position) else { unreachable!() };
        let GoStatement::Assign { values: assigned, .. } = &mut block[next - 1] else {
            unreachable!()
        };
        *assigned = values;
    }
}

fn drop_self_assignments(block: &mut Vec<GoStatement>) {
    for statement in block.iter_mut() {
        if let GoStatement::Assign { targets, values } = statement
            && targets.len() == values.len()
        {
            let kept: Vec<bool> = targets
                .iter()
                .zip(values.iter())
                .map(|(target, value)| !is_same_local(target, value))
                .collect();
            let mut keep = kept.iter().copied();
            targets.retain(|_| keep.next().unwrap_or(true));
            let mut keep = kept.into_iter();
            values.retain(|_| keep.next().unwrap_or(true));
        }
    }
    block.retain(
        |statement| !matches!(statement, GoStatement::Assign { targets, .. } if targets.is_empty()),
    );
    for statement in block {
        if let GoStatement::If { condition, then, otherwise } = statement {
            drop_self_assignments(then);
            drop_self_assignments(otherwise);
            if then.is_empty() && !otherwise.is_empty() {
                *condition = super::conditions::negated(condition);
                std::mem::swap(then, otherwise);
            }
        }
    }
}

fn is_same_local(target: &GoExpression, value: &GoExpression) -> bool {
    match (target, value) {
        (GoExpression::Identifier(target), GoExpression::Identifier(value)) => target == value,
        _ => false,
    }
}

pub(super) fn is_named(value: &GoExpression, name: &str) -> bool {
    matches!(value, GoExpression::Identifier(identifier) if identifier == name)
}

/// `return value` for `staged := value` directly followed by `return staged`.
fn return_directly(block: &mut Vec<GoStatement>) {
    let Some(last) = block.len().checked_sub(1) else { return };
    let Some(defined) = (0..last).rev().find(|&at| !matches!(block[at], GoStatement::Line(_)))
    else {
        return;
    };
    let staged = matches!(
        (&block[defined], &block[last]),
        (
            GoStatement::Define { names, values },
            GoStatement::Return(Some(GoExpression::Identifier(returned))),
        ) if names.len() == 1 && values.len() == 1 && &names[0] == returned
    );
    if !staged || defined + 1 != last {
        return;
    }
    let GoStatement::Define { mut values, .. } = block.remove(defined) else { unreachable!() };
    block[defined] = GoStatement::Return(values.pop());
}
