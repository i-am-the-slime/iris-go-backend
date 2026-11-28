//! An object made empty and then filled by a loop over an array is made for as many entries.
//!
//! `Object.fromFoldable` and an `STObject` filled by `for_` start from `object.New[V]()` and poke
//! one entry per element: `m := object.New[int](); for _, word := range words { object.Poke(word,
//! 1, m) }`. The table's keys, values and index then grow as it fills, copying each several
//! times. Made with room for an entry per element,
//!
//! ```go
//! m := object.NewWithCapacity[int](len(words))
//! ```
//!
//! it never grows. It is the empty table still: no entries, no array-index keys, and an index
//! that every operation of the runtime keeps up to date once there is one.

use crate::go_traversal::each_block_in_declaration;
use crate::syntax::{GoBuiltin, GoDeclaration, GoExpression, GoPackage, GoStatement, GoType};

pub(super) fn presize_filled_objects(declarations: &mut [GoDeclaration]) {
    for declaration in declarations {
        each_block_in_declaration(declaration, |block| {
            for position in 0..block.len() {
                let Some((name, values)) = new_object(&block[position]) else { continue };
                let next = (position + 1..block.len())
                    .find(|&next| !matches!(block[next], GoStatement::Line(_)));
                let Some(array) = next.and_then(|next| filled_from(&block[next], name)) else {
                    continue;
                };
                let made = presized(values, array);
                if let GoStatement::Define { values, .. } = &mut block[position] {
                    values[0] = made;
                }
            }
        });
    }
}

/// `name := object.New[V]()`: the name and the type of the values.
fn new_object(statement: &GoStatement) -> Option<(&str, GoType)> {
    let GoStatement::Define { names, values } = statement else { return None };
    let ([name], [value]) = (names.as_slice(), values.as_slice()) else { return None };
    let GoExpression::Call { function, arguments } = value.unattributed() else { return None };
    let GoExpression::Instantiation { function, arguments: types } = function.unattributed() else {
        return None;
    };
    let new = function.unattributed().is_qualified(GoPackage::Object, "New");
    match (new, arguments.as_slice(), types.as_slice()) {
        (true, [], [values]) => Some((name, values.clone())),
        _ => None,
    }
}

/// The array a loop ranges over when its body pokes entries into the object `name`.
fn filled_from(statement: &GoStatement, name: &str) -> Option<String> {
    let GoStatement::Range { iterable, body, .. } = statement else { return None };
    let GoExpression::Identifier(array) = iterable.unattributed() else { return None };
    body.iter().any(|statement| pokes(statement, name)).then(|| array.clone())
}

fn pokes(statement: &GoStatement, name: &str) -> bool {
    let GoStatement::Expression(GoExpression::Call { function, arguments }) = statement else {
        return false;
    };
    let function = match function.unattributed() {
        GoExpression::Instantiation { function, .. } => function.as_ref(),
        function => function,
    };
    let is_poke = function.unattributed().is_qualified(GoPackage::Object, "Poke");
    is_poke
        && matches!(arguments.last().map(GoExpression::unattributed),
            Some(GoExpression::Identifier(object)) if object == name)
}

/// The empty table with room for an entry per element of `array`.
fn presized(values: GoType, array: String) -> GoExpression {
    let new = GoExpression::qualified(GoPackage::Object, "NewWithCapacity");
    let new = GoExpression::Instantiation { function: Box::new(new), arguments: vec![values] };
    let length = GoExpression::Call {
        function: Box::new(GoExpression::builtin(GoBuiltin::Len)),
        arguments: vec![GoExpression::Identifier(array)],
    };
    GoExpression::Call { function: Box::new(new), arguments: vec![length] }
}
