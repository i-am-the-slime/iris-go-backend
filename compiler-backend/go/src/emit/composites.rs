use rustc_hash::{FxHashMap, FxHashSet};

use super::aliases::{Guarded, calls, is_named, target_root, writes};
use crate::syntax::{GoDeclaration, GoExpression, GoStatement};
use crate::walk::{self, Walk};

pub(super) fn take_composites_apart(declarations: &mut [GoDeclaration]) {
    for declaration in declarations {
        let guarded = Guarded::of(declaration);
        let mentions = mentions_in(declaration);
        walk::each_block_in_declaration(declaration, |block| {
            let mut position = 0;
            while position < block.len() {
                if !take_apart_at(block, position, &guarded, &mentions) {
                    position += 1;
                }
            }
        });
    }
}

fn take_apart_at(
    block: &mut Vec<GoStatement>,
    position: usize,
    guarded: &Guarded,
    mentions: &FxHashMap<String, usize>,
) -> bool {
    let Some((name, fields)) = defined_composite(&block[position]) else { return false };
    if guarded.written_in_literal(&name) || !fields.iter().all(|(_, part)| local(part, guarded)) {
        return false;
    }
    let rest = &mut block[position + 1..];
    let Some(read) = fields_read(rest, &name, &fields) else { return false };
    let stays_used = |(field, value): &(String, GoExpression)| match value {
        GoExpression::Identifier(local) => {
            read.contains(field) || mentions.get(local).is_some_and(|count| *count > 1)
        }
        _ => true,
    };
    if !fields.iter().all(stays_used) {
        return false;
    }
    if fields.iter().any(|(_, value)| guards(value, guarded)) && rest.iter_mut().any(calls) {
        return false;
    }
    if fields.iter().any(|(_, value)| rest.iter_mut().any(|statement| rebinds(statement, value))) {
        return false;
    }
    for statement in rest {
        walk::each_expression_in_statement(statement, |expression| {
            if let Some(field) = read_field(expression, &name) {
                let (_, value) = fields.iter().find(|(name, _)| name == field).expect("read field");
                *expression = value.clone();
            }
        });
    }
    block.remove(position);
    true
}

fn defined_composite(statement: &GoStatement) -> Option<(String, Vec<(String, GoExpression)>)> {
    let GoStatement::Define { names, values } = statement else { return None };
    let ([name], [GoExpression::Composite { fields, .. }]) = (names.as_slice(), values.as_slice())
    else {
        return None;
    };
    let mut named = vec![];
    for (field, value) in fields {
        let field = field.as_ref()?;
        if !is_plain(value) {
            return None;
        }
        named.push((field.clone(), value.clone()));
    }
    Some((name.clone(), named))
}

fn is_plain(value: &GoExpression) -> bool {
    matches!(value, GoExpression::Identifier(name) if name != "nil")
}

fn local(value: &GoExpression, guarded: &Guarded) -> bool {
    matches!(value, GoExpression::Identifier(name) if guarded.is_local(name))
}

fn guards(value: &GoExpression, guarded: &Guarded) -> bool {
    matches!(value, GoExpression::Identifier(name) if guarded.written_in_literal(name))
}

fn rebinds(statement: &mut GoStatement, value: &GoExpression) -> bool {
    match value {
        GoExpression::Identifier(name) => writes(statement, name),
        _ => false,
    }
}

fn read_field<'e>(expression: &'e GoExpression, composite: &str) -> Option<&'e str> {
    match expression {
        GoExpression::Field { value, name } if is_named(value, composite) => Some(name),
        _ => None,
    }
}

fn fields_read(
    rest: &mut [GoStatement],
    name: &str,
    fields: &[(String, GoExpression)],
) -> Option<FxHashSet<String>> {
    let mut uses = Uses { name, fields, reads: FxHashSet::default(), other: false };
    for statement in rest {
        uses.statement(statement);
    }
    (!uses.other && !uses.reads.is_empty()).then_some(uses.reads)
}

fn mentions_in(declaration: &mut GoDeclaration) -> FxHashMap<String, usize> {
    let mut counts = FxHashMap::default();
    walk::each_expression_in_declaration(declaration, |expression| {
        if let GoExpression::Identifier(name) = expression {
            *counts.entry(name.clone()).or_insert(0) += 1;
        }
    });
    counts
}

struct Uses<'a> {
    name: &'a str,
    fields: &'a [(String, GoExpression)],
    reads: FxHashSet<String>,
    other: bool,
}

impl Walk for Uses<'_> {
    fn statement(&mut self, statement: &mut GoStatement) {
        if let GoStatement::Assign { targets, .. } = statement
            && targets.iter().any(|target| target_root(target) == Some(self.name))
        {
            self.other = true;
        }
        if let GoStatement::Define { names, .. } = statement
            && names.iter().any(|defined| defined == self.name)
        {
            self.other = true;
        }
        walk::statement(self, statement);
    }

    fn expression(&mut self, value: &mut GoExpression) {
        match read_field(value, self.name) {
            Some(field) if self.fields.iter().any(|(name, _)| name == field) => {
                self.reads.insert(field.to_string());
            }
            Some(_) => self.other = true,
            None if is_named(value, self.name) => self.other = true,
            None => walk::expression(self, value),
        }
    }
}
