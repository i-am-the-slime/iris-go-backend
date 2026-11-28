//! One hash for a Go map's membership test and the read of the entry it found.
//!
//! `Map.insertWith f k v m` of a Go map tests for the key and reads the old value where it is
//! there, hashing the key twice before the write:
//!
//! ```go
//! _, found := counts[key]
//! var result int
//! if found { result = counts[key] + 1 } else { result = 1 }
//! counts[key] = result
//! ```
//!
//! The test keeps the value it found, `old, found := counts[key]`, and the branch reads `old`.
//! Nothing between the test and the read may change the map or the key.

use rustc_hash::FxHashSet;

use super::aliases::writes;
use crate::go_traversal::{self, Walk, each_block_in_declaration};
use crate::syntax::{GoDeclaration, GoExpression, GoStatement};

pub(super) fn probe_once(declarations: &mut [GoDeclaration], taken: &dyn Fn(&str) -> bool) {
    for declaration in declarations {
        let mut names = declaration.declared_names().names;
        each_block_in_declaration(declaration, |block| {
            for position in 0..block.len() {
                probe_once_at(block, position, &mut names, taken);
            }
        });
    }
}

/// `_, found := table[key]` of a variable table and a variable or constant key.
struct Test {
    entry: GoExpression,
    table: String,
    key: Option<String>,
    found: String,
}

fn probe_once_at(
    block: &mut [GoStatement],
    position: usize,
    names: &mut FxHashSet<String>,
    taken: &dyn Fn(&str) -> bool,
) {
    let Some(test) = test(&block[position]) else { return };
    let Some(branch) = branch_after(block, position, &test) else { return };
    let GoStatement::If { then, .. } = &mut block[branch] else {
        unreachable!("invariant violated: the branch is an if")
    };
    let old = fresh_name("old", names, taken);
    let mut replaced = false;
    for statement in then.iter_mut() {
        if changes(statement, &test) {
            break;
        }
        let entry = &test.entry;
        let mut substitution = Substitution { entry, value: &old, replaced: &mut replaced };
        substitution.statement(statement);
    }
    if !replaced {
        names.remove(&old);
        return;
    }
    let GoStatement::Define { names: defined, .. } = &mut block[position] else {
        unreachable!("invariant violated: the test is a definition")
    };
    defined[0] = old;
}

fn test(statement: &GoStatement) -> Option<Test> {
    let GoStatement::Define { names, values } = statement else { return None };
    let names_and_values = (names.as_slice(), values.as_slice());
    let ([ignored, found], [entry @ GoExpression::Index { value, index }]) = names_and_values
    else {
        return None;
    };
    let GoExpression::Identifier(table) = value.as_ref() else { return None };
    let key = match index.as_ref() {
        GoExpression::Identifier(key) => Some(key.clone()),
        GoExpression::Integer(_)
        | GoExpression::String(_)
        | GoExpression::Rune(_)
        | GoExpression::Boolean(_) => None,
        _ => return None,
    };
    (ignored == "_" && found != "_").then(|| Test {
        entry: entry.clone(),
        table: table.clone(),
        key,
        found: found.clone(),
    })
}

/// The position of the `if found` after the test, when the statements up to it leave the map,
/// the key and the answer alone.
fn branch_after(block: &mut [GoStatement], position: usize, test: &Test) -> Option<usize> {
    for (index, statement) in block.iter_mut().enumerate().skip(position + 1) {
        if let GoStatement::If { condition: GoExpression::Identifier(tested), .. } = &*statement
            && *tested == test.found
        {
            return Some(index);
        }
        if changes(statement, test) || writes(statement, &test.found) {
            return None;
        }
    }
    None
}

fn changes(statement: &mut GoStatement, test: &Test) -> bool {
    writes(statement, &test.table)
        || test.key.as_ref().is_some_and(|key| writes(statement, key))
        || builds_function(statement)
}

fn builds_function(statement: &mut GoStatement) -> bool {
    let mut builds = false;
    go_traversal::each_expression_in_statement(statement, |expression| {
        builds |= matches!(expression, GoExpression::Function { .. });
    });
    builds
}

fn fresh_name(base: &str, names: &mut FxHashSet<String>, taken: &dyn Fn(&str) -> bool) -> String {
    let mut candidate = base.to_string();
    let mut suffix = 2;
    while names.contains(&candidate) || taken(&candidate) {
        candidate = format!("{base}{suffix}");
        suffix += 1;
    }
    names.insert(candidate.clone());
    candidate
}

/// Reads of the entry become reads of the value the test found.
struct Substitution<'a> {
    entry: &'a GoExpression,
    value: &'a str,
    replaced: &'a mut bool,
}

impl Walk for Substitution<'_> {
    fn statement(&mut self, statement: &mut GoStatement) {
        if let GoStatement::Assign { targets, values } = statement {
            // A write of the entry is no read of it.
            values.iter_mut().for_each(|value| self.expression(value));
            for target in targets.iter_mut() {
                if target != self.entry {
                    self.expression(target);
                }
            }
            return;
        }
        go_traversal::statement(self, statement);
    }

    fn expression(&mut self, value: &mut GoExpression) {
        if value == self.entry {
            *value = GoExpression::Identifier(self.value.to_string());
            *self.replaced = true;
            return;
        }
        go_traversal::expression(self, value);
    }
}
