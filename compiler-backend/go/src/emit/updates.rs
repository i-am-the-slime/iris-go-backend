use super::aliases::{Guarded, is_named, mentions};
use crate::go_traversal::{self, Walk};
use crate::syntax::{GoDeclaration, GoExpression, GoStatement};

pub(super) fn update_in_place(declarations: &mut [GoDeclaration]) {
    for declaration in declarations {
        let guarded = Guarded::of(declaration);
        go_traversal::each_block_in_declaration(declaration, |block| {
            let mut position = 0;
            while position < block.len() {
                if !update_at(block, position, &guarded) && !take_over_at(block, position, &guarded)
                {
                    position += 1;
                }
            }
        });
    }
}

fn update_at(block: &mut Vec<GoStatement>, position: usize, guarded: &Guarded) -> bool {
    let Some((copy, source)) = defined_copy(&block[position]) else { return false };
    if guarded.mentioned_in_literal(&copy) || guarded.mentioned_in_literal(&source) {
        return false;
    }
    if !guarded.is_local(&source) {
        return false;
    }
    let mut written: Vec<String> = vec![];
    let mut end = position + 1;
    while let Some((field, value)) =
        block.get(end).and_then(|statement| assigned_field(statement, &copy))
    {
        let reads = SourceReads::of(value, &source);
        if reads.copy || reads.whole || reads.fields.iter().any(|read| written.contains(read)) {
            return false;
        }
        written.push(field.to_string());
        end += 1;
    }
    let closes = |statement: &GoStatement| assigns_back(statement, &source, &copy);
    if written.is_empty() || !block.get(end).is_some_and(closes) {
        return false;
    }
    if block[end + 1..].iter_mut().any(|statement| mentions(statement, &copy)) {
        return false;
    }
    block.remove(end);
    block.remove(position);
    for statement in &mut block[position..end - 1] {
        retarget(statement, &source);
    }
    true
}

/// `copy := source`, where `source` is a local of the same block that is not
/// read again but by the copy's field updates, each before its field is
/// written, makes `source` itself the copy: updates of the copy write into the
/// local nobody reads again.
fn take_over_at(block: &mut Vec<GoStatement>, position: usize, guarded: &Guarded) -> bool {
    let Some((copy, source)) = defined_copy(&block[position]) else { return false };
    if guarded.mentioned_in_literal(&copy) || guarded.mentioned_in_literal(&source) {
        return false;
    }
    let defines_source = |statement: &GoStatement| match statement {
        GoStatement::Define { names, .. } => names.contains(&source),
        GoStatement::Variable { name, .. } => *name == source,
        _ => false,
    };
    if !block[..position].iter().any(defines_source) {
        return false;
    }
    let mut written: Vec<String> = vec![];
    let mut end = position + 1;
    while let Some((field, value)) =
        block.get(end).and_then(|statement| assigned_field(statement, &copy))
    {
        let reads = SourceReads::of(value, &source);
        if reads.whole || reads.fields.iter().any(|read| written.contains(read)) {
            return false;
        }
        written.push(field.to_string());
        end += 1;
    }
    if block[end..].iter_mut().any(|statement| mentions(statement, &source)) {
        return false;
    }
    block.remove(position);
    for statement in &mut block[position..] {
        go_traversal::each_expression_in_statement(statement, |expression| {
            if is_named(expression, &copy) {
                *expression = GoExpression::Identifier(source.clone());
            }
        });
    }
    true
}

fn defined_copy(statement: &GoStatement) -> Option<(String, String)> {
    let GoStatement::Define { names, values } = statement else { return None };
    let ([copy], [GoExpression::Identifier(source)]) = (names.as_slice(), values.as_slice()) else {
        return None;
    };
    (copy != source && source != "nil").then(|| (copy.clone(), source.clone()))
}

fn assigned_field<'s>(
    statement: &'s GoStatement,
    copy: &str,
) -> Option<(&'s str, &'s GoExpression)> {
    let GoStatement::Assign { targets, values } = statement else { return None };
    let ([GoExpression::Field { value, name }], [assigned]) =
        (targets.as_slice(), values.as_slice())
    else {
        return None;
    };
    is_named(value, copy).then_some((name.as_str(), assigned))
}

fn assigns_back(statement: &GoStatement, source: &str, copy: &str) -> bool {
    let GoStatement::Assign { targets, values } = statement else { return false };
    let ([target], [value]) = (targets.as_slice(), values.as_slice()) else { return false };
    is_named(target, source) && is_named(value, copy)
}

fn retarget(statement: &mut GoStatement, source: &str) {
    let GoStatement::Assign { targets, .. } = statement else { unreachable!("a field update") };
    let [GoExpression::Field { value, .. }] = targets.as_mut_slice() else {
        unreachable!("invariant violated: an update assigns one field")
    };
    **value = GoExpression::Identifier(source.to_string());
}

struct SourceReads<'a> {
    source: &'a str,
    copy: bool,
    whole: bool,
    fields: Vec<String>,
}

impl<'a> SourceReads<'a> {
    fn of(value: &GoExpression, source: &'a str) -> Self {
        let mut reads = SourceReads { source, copy: false, whole: false, fields: vec![] };
        let mut value = value.clone();
        reads.expression(&mut value);
        reads
    }
}

impl Walk for SourceReads<'_> {
    fn expression(&mut self, value: &mut GoExpression) {
        match value {
            GoExpression::Field { value: inner, name } if is_named(inner, self.source) => {
                self.fields.push(name.clone());
            }
            GoExpression::Identifier(name) if name == self.source => self.whole = true,
            _ => go_traversal::expression(self, value),
        }
    }
}
