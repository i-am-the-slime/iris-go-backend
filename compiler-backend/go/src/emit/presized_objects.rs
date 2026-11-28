//! An object made empty and then filled by a loop over an array is made for as many entries.
//!
//! `Object.fromFoldable` and an `STObject` filled by `for_` start from `object.New[V]()` and poke
//! one entry per element: `m := object.New[int](); for _, word := range words { object.Poke(word,
//! 1, m) }`. The table's keys, values and index then grow as it fills, copying each several
//! times. Made with room for an entry per element,
//!
//! ```go
//! m := &struct{ Index map[string]int; Ints int; Keys []string; Vals []int }{
//!     Index: make(map[string]int, len(words)),
//!     Keys:  make([]string, 0, len(words)),
//!     Vals:  make([]int, 0, len(words)),
//! }
//! ```
//!
//! it never grows. It is the empty table still: no entries, no array-index keys, and an index
//! that every operation of the runtime keeps up to date once there is one.

use crate::go_traversal::each_block_in_declaration;
use crate::syntax::{
    GoBuiltin, GoDeclaration, GoExpression, GoPackage, GoStatement, GoType, StructField,
};

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
    let poke =
        |function: &GoExpression| function.unattributed().is_qualified(GoPackage::Object, "Poke");
    let function = match function.unattributed() {
        GoExpression::Instantiation { function, .. } => function.as_ref(),
        function => function,
    };
    poke(function)
        && matches!(arguments.last().map(GoExpression::unattributed),
            Some(GoExpression::Identifier(object)) if object == name)
}

/// The empty table with room for an entry per element of `array`.
fn presized(values: GoType, array: String) -> GoExpression {
    let length = || GoExpression::Call {
        function: Box::new(GoExpression::builtin(GoBuiltin::Len)),
        arguments: vec![GoExpression::Identifier(array.clone())],
    };
    let make = |type_: GoType, sizes: Vec<GoExpression>| {
        let mut arguments = vec![GoExpression::Type(type_)];
        arguments.extend(sizes);
        GoExpression::Call { function: Box::new(GoExpression::builtin(GoBuiltin::Make)), arguments }
    };
    let index = GoType::Named("map[string]int".into());
    let keys = GoType::Slice(Box::new(GoType::String));
    let vals = GoType::Slice(Box::new(values));
    let table = GoType::Struct(vec![
        StructField::new("Index", index.clone()),
        StructField::new("Ints", GoType::Int),
        StructField::new("Keys", keys.clone()),
        StructField::new("Vals", vals.clone()),
    ]);
    let zero = || GoExpression::Integer(0);
    GoExpression::Address(Box::new(GoExpression::Composite {
        type_: table,
        fields: vec![
            (Some("Index".into()), make(index, vec![length()])),
            (Some("Keys".into()), make(keys, vec![zero(), length()])),
            (Some("Vals".into()), make(vals, vec![zero(), length()])),
        ],
    }))
}
