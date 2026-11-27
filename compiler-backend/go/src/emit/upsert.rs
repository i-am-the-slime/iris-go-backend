//! One hash for an object's lookup and write of one key.
//!
//! `Object.fromFoldableWith`, and every tally that looks a key up in an `STObject` and pokes the
//! combined value back under it, hashes the key twice:
//!
//! ```go
//! value, found := object.LookupST(word, counts)
//! var count int
//! if found { count = value + 1 } else { count = 1 }
//! object.Poke(word, count, counts)
//! ```
//!
//! The lookup becomes `Slot`, the key's position, which the found branch reads and the write
//! assigns, so that only a key the object does not hold yet is hashed again:
//!
//! ```go
//! slot, found := object.Slot(counts, word)
//! var count int
//! if found { count = counts.Vals[slot] + 1 } else { count = 1 }
//! if found { counts.Vals[slot] = count } else { object.Poke(word, count, counts) }
//! ```
//!
//! Nothing between the two may mention the object or the key, the value may be read only where
//! it was found, and it may not be read after the write. A poked table is never one that `Lend`
//! made, so writing its `Vals` is what `Poke` does with a key it holds.

use rustc_hash::FxHashSet;

use crate::go_traversal::{self, Walk, each_block_in_declaration};
use crate::syntax::{GoDeclaration, GoExpression, GoStatement};

use super::aliases::{mentions, writes};

pub(super) fn look_up_and_write_once(
    declarations: &mut [GoDeclaration],
    taken: &dyn Fn(&str) -> bool,
) {
    for declaration in declarations {
        let mut names = declaration.declared_names().names;
        each_block_in_declaration(declaration, |block| {
            for position in 0..block.len() {
                write_once_at(block, position, &mut names, taken);
            }
        });
    }
}

/// A lookup of a key in an object, by the names of its two answers.
struct Lookup {
    package: String,
    key: String,
    object: String,
    value: String,
    found: String,
}

fn write_once_at(
    block: &mut [GoStatement],
    position: usize,
    names: &mut FxHashSet<String>,
    taken: &dyn Fn(&str) -> bool,
) {
    let Some(lookup) = lookup(&block[position]) else { return };
    let Some(write) = poke_after(block, position, &lookup) else { return };
    let slot = fresh_name("slot", names, taken);
    let found_value = vals_at(&lookup.object, &slot);
    for statement in &mut block[position + 1..write] {
        read_where_found(statement, &lookup, &found_value);
    }
    let GoStatement::Expression(GoExpression::Call { arguments, .. }) = &block[write] else {
        unreachable!("invariant violated: the write is a call of Poke")
    };
    let written = arguments[1].clone();
    let poke = block[write].clone();
    block[write] = GoStatement::If {
        condition: GoExpression::Identifier(lookup.found.clone()),
        then: vec![GoStatement::Assign { targets: vec![found_value], values: vec![written] }],
        otherwise: vec![poke],
    };
    block[position] = GoStatement::Define {
        names: vec![slot, lookup.found.clone()],
        values: vec![GoExpression::Call {
            function: Box::new(GoExpression::Qualified {
                package: lookup.package,
                name: "Slot".into(),
            }),
            arguments: vec![
                GoExpression::Identifier(lookup.object),
                GoExpression::Identifier(lookup.key),
            ],
        }],
    };
}

/// `value, found := object.LookupST(key, object)`, or `PeekImpl`, of two variables.
fn lookup(statement: &GoStatement) -> Option<Lookup> {
    let GoStatement::Define { names, values } = statement else { return None };
    let ([value, found], [GoExpression::Call { function, arguments }]) =
        (names.as_slice(), values.as_slice())
    else {
        return None;
    };
    let GoExpression::Qualified { package, name } = function.as_ref() else { return None };
    let [GoExpression::Identifier(key), GoExpression::Identifier(object)] = arguments.as_slice()
    else {
        return None;
    };
    let looks_up = matches!(name.as_str(), "LookupST" | "PeekImpl");
    let named = |name: &str| name != "_" && name != key && name != object;
    (looks_up && named(found) && value != found && value != key && value != object).then(|| {
        Lookup {
            package: package.clone(),
            key: key.clone(),
            object: object.clone(),
            value: value.clone(),
            found: found.clone(),
        }
    })
}

/// The position of the `Poke` of a variable under the looked up key, when the statements up to
/// it leave the object, the key and the answers alone and read the value only where it was found,
/// and nothing after reads the value.
fn poke_after(block: &mut [GoStatement], position: usize, lookup: &Lookup) -> Option<usize> {
    let write = (position + 1..block.len()).find(|&index| pokes(&block[index], lookup))?;
    let untouched = block[position + 1..write].iter_mut().all(|statement| {
        !mentions(statement, &lookup.object)
            && !mentions(statement, &lookup.key)
            && !writes(statement, &lookup.found)
            && !writes(statement, &lookup.value)
            && value_read_only_where_found(statement, lookup)
            && !builds_function(statement)
    });
    let read_after = block[write..].iter_mut().any(|statement| mentions(statement, &lookup.value));
    (untouched && !read_after).then_some(write)
}

fn pokes(statement: &GoStatement, lookup: &Lookup) -> bool {
    let GoStatement::Expression(GoExpression::Call { function, arguments }) = statement else {
        return false;
    };
    let GoExpression::Qualified { package, name } = function.as_ref() else { return false };
    let [
        GoExpression::Identifier(key),
        GoExpression::Identifier(written),
        GoExpression::Identifier(object),
    ] = arguments.as_slice()
    else {
        return false;
    };
    *package == lookup.package
        && name == "Poke"
        && *key == lookup.key
        && *object == lookup.object
        && *written != lookup.value
}

/// Whether the statement reads the value only in the branches of `if found`.
fn value_read_only_where_found(statement: &mut GoStatement, lookup: &Lookup) -> bool {
    match statement {
        GoStatement::If { condition: GoExpression::Identifier(tested), otherwise, .. }
            if *tested == lookup.found =>
        {
            !otherwise.iter_mut().any(|statement| mentions(statement, &lookup.value))
        }
        _ => !mentions(statement, &lookup.value),
    }
}

/// Whether the statement makes a function literal, which could read the value after the write.
fn builds_function(statement: &mut GoStatement) -> bool {
    let mut builds = false;
    go_traversal::each_expression_in_statement(statement, |expression| {
        builds |= matches!(expression, GoExpression::Function { .. });
    });
    builds
}

/// Reads the value from the object's `Vals` in the branches of `if found`.
fn read_where_found(statement: &mut GoStatement, lookup: &Lookup, found_value: &GoExpression) {
    if let GoStatement::If { condition: GoExpression::Identifier(tested), then, .. } = statement
        && *tested == lookup.found
    {
        let mut substitution = Substitution { name: &lookup.value, value: found_value };
        then.iter_mut().for_each(|statement| substitution.statement(statement));
    }
}

struct Substitution<'a> {
    name: &'a str,
    value: &'a GoExpression,
}

impl Walk for Substitution<'_> {
    fn expression(&mut self, value: &mut GoExpression) {
        match value {
            GoExpression::Identifier(name) if name == self.name => *value = self.value.clone(),
            _ => go_traversal::expression(self, value),
        }
    }
}

/// `object.Vals[slot]`.
fn vals_at(object: &str, slot: &str) -> GoExpression {
    GoExpression::Index {
        value: Box::new(GoExpression::Field {
            value: Box::new(GoExpression::Identifier(object.into())),
            name: "Vals".into(),
        }),
        index: Box::new(GoExpression::Identifier(slot.into())),
    }
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
