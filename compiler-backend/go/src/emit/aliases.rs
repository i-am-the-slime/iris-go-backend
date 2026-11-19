use crate::syntax::{GoDeclaration, GoExpression, GoStatement};
use crate::walk::{self, Walk};

pub(super) fn substitute_aliases(declarations: &mut [GoDeclaration]) {
    for declaration in declarations {
        walk::each_block_in_declaration(declaration, |block| {
            let mut position = 0;
            while position < block.len() {
                if !substitute_at(block, position) {
                    position += 1;
                }
            }
        });
    }
}

fn substitute_at(block: &mut Vec<GoStatement>, position: usize) -> bool {
    let Some((alias, original)) = defined_alias(&block[position]) else { return false };
    let rest = &mut block[position + 1..];
    let mut total = 0;
    let mut use_at = None;
    for (offset, statement) in rest.iter_mut().enumerate() {
        let count = reads(statement, &alias);
        if count > 0 && use_at.is_none() {
            use_at = Some(offset);
        }
        total += count;
    }
    let Some(use_at) = use_at.filter(|_| total == 1) else { return false };
    if !head_reads_once(&mut rest[use_at], &alias) {
        return false;
    }
    if rest[..use_at].iter_mut().any(|statement| writes(statement, &original)) {
        return false;
    }
    walk::each_expression_in_statement(&mut rest[use_at], |expression| {
        if is_named(expression, &alias) {
            *expression = GoExpression::Identifier(original.clone());
        }
    });
    block.remove(position);
    true
}

fn defined_alias(statement: &GoStatement) -> Option<(String, String)> {
    let GoStatement::Define { names, values } = statement else { return None };
    let [alias] = names.as_slice() else { return None };
    let [GoExpression::Identifier(original)] = values.as_slice() else { return None };
    (alias != original && original != "nil").then(|| (alias.clone(), original.clone()))
}

fn heads(statement: &mut GoStatement) -> Option<Vec<&mut GoExpression>> {
    Some(match statement {
        GoStatement::Define { values, .. } | GoStatement::Assign { values, .. } => {
            values.iter_mut().collect()
        }
        GoStatement::Variable { value: Some(value), .. }
        | GoStatement::Expression(value)
        | GoStatement::Defer(value)
        | GoStatement::Return(Some(value))
        | GoStatement::If { condition: value, .. }
        | GoStatement::Switch { value: Some(value), .. }
        | GoStatement::IfAssert { value, .. }
        | GoStatement::Range { iterable: value, .. } => vec![value],
        _ => return None,
    })
}

fn head_reads_once(statement: &mut GoStatement, alias: &str) -> bool {
    let Some(heads) = heads(statement) else { return false };
    let mut reads = Reads { name: alias, count: 0, in_literal: false };
    for head in heads {
        reads.expression(head);
    }
    reads.count == 1
}

fn reads(statement: &mut GoStatement, name: &str) -> usize {
    let mut reads = Reads { name, count: 0, in_literal: false };
    reads.statement(statement);
    reads.count
}

struct Reads<'a> {
    name: &'a str,
    count: usize,
    in_literal: bool,
}

impl Walk for Reads<'_> {
    fn statement(&mut self, statement: &mut GoStatement) {
        if let GoStatement::Assign { targets, .. } = statement
            && targets.iter().any(|target| is_named(target, self.name))
        {
            self.count += 2;
        }
        walk::statement(self, statement);
    }

    fn expression(&mut self, value: &mut GoExpression) {
        match value {
            GoExpression::Identifier(name) if name == self.name => {
                self.count += if self.in_literal { 2 } else { 1 };
            }
            GoExpression::Address(inner) if is_named(inner, self.name) => self.count += 2,
            GoExpression::Function { .. } => {
                let enclosing = std::mem::replace(&mut self.in_literal, true);
                walk::expression(self, value);
                self.in_literal = enclosing;
            }
            _ => walk::expression(self, value),
        }
    }
}

fn writes(statement: &mut GoStatement, name: &str) -> bool {
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
            GoStatement::Assign { targets, .. } => targets
                .iter()
                .filter_map(|target| match target {
                    GoExpression::Identifier(name) => Some(name.as_str()),
                    _ => None,
                })
                .collect(),
            GoStatement::Define { names, .. } => names.iter().map(String::as_str).collect(),
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
        walk::statement(self, statement);
    }

    fn expression(&mut self, value: &mut GoExpression) {
        if let GoExpression::Address(inner) = value
            && is_named(inner, self.name)
        {
            self.written = true;
        }
        walk::expression(self, value);
    }
}

pub(super) fn is_named(value: &GoExpression, name: &str) -> bool {
    matches!(value, GoExpression::Identifier(identifier) if identifier == name)
}
