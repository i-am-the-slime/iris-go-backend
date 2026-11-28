//! An array of an array's own indices that only a loop reads becomes the loop's counter.
//!
//! `for_ (Array.drop 1 (indices cells))` in `Data.Array.ST.Indexed`, or any `mapWithIndex` that
//! keeps only the index, builds the indices before the loop walks them:
//!
//! ```go
//! positions := make([]int, len(cells))
//! for slot := range cells { positions[slot] = slot }
//! for _, cell := range array.Slice(1, len(cells), positions) { … }
//! ```
//!
//! counts instead, `for cell := 1; cell < len(cells); cell++ { … }`. The array may be read by
//! nothing else, the loop may not write its element or the array it counts up to, and a slice of
//! it must start at a constant and end at its length.

use crate::syntax::{GoBuiltin, GoDeclaration, GoExpression, GoStatement, GoType};

use super::aliases::{mentions, writes};

pub(super) fn count_instead_of_listing_indices(declarations: &mut [GoDeclaration]) {
    for declaration in declarations {
        crate::go_traversal::each_block_in_declaration(declaration, |block| {
            let mut position = 0;
            while position < block.len() {
                if !count_at(block, position) {
                    position += 1;
                }
            }
        });
    }
}

/// `positions := make([]int, len(cells))` and the loop that fills it with its indices.
struct Indices {
    array: String,
    counted: String,
    slot: String,
    filling: usize,
}

fn count_at(block: &mut Vec<GoStatement>, position: usize) -> bool {
    let Some(indices) = indices_at(block, position) else { return false };
    let Some(walking) = walk_after(block, &indices) else { return false };
    let GoStatement::Range { element, iterable, body, .. } = &mut block[walking] else {
        unreachable!("invariant violated: the walk is a range loop")
    };
    let start = match iterable {
        GoExpression::Call { arguments, .. } => arguments[0].clone(),
        _ => GoExpression::Integer(0),
    };
    let variable = if element == "_" { indices.slot.clone() } else { element.clone() };
    block[walking] = GoStatement::Counting {
        variable,
        start,
        end: length_of(&indices.counted),
        body: std::mem::take(body),
    };
    block.remove(indices.filling);
    block.remove(position);
    true
}

fn indices_at(block: &[GoStatement], position: usize) -> Option<Indices> {
    let GoStatement::Define { names, values } = &block[position] else { return None };
    let [array] = names.as_slice() else { return None };
    let [GoExpression::Call { function, arguments }] = values.as_slice() else { return None };
    let is_make = function.is_builtin(GoBuiltin::Make);
    let [GoExpression::Type(GoType::Slice(element)), length] = arguments.as_slice() else {
        return None;
    };
    let counted = counted_by(length)?;
    if !is_make || **element != GoType::Int {
        return None;
    }
    let filling = (position + 1..block.len()).find(|&index| !is_line(&block[index]))?;
    let GoStatement::Range { index: Some(slot), element, iterable, body } = &block[filling] else {
        return None;
    };
    let fills = element == "_"
        && matches!(iterable, GoExpression::Identifier(name) if *name == counted)
        && body.iter().filter(|statement| !is_line(statement)).count() == 1
        && body.iter().any(|statement| assigns_index(statement, array, slot));
    fills.then(|| Indices { array: array.clone(), counted, slot: slot.clone(), filling })
}

/// `array[slot] = slot`.
fn assigns_index(statement: &GoStatement, array: &str, slot: &str) -> bool {
    let GoStatement::Assign { targets, values } = statement else { return false };
    let [GoExpression::Index { value, index }] = targets.as_slice() else { return false };
    let [GoExpression::Identifier(assigned)] = values.as_slice() else { return false };
    matches!(value.as_ref(), GoExpression::Identifier(name) if name == array)
        && matches!(index.as_ref(), GoExpression::Identifier(name) if name == slot)
        && assigned == slot
}

/// The position of the one loop that walks the indices, when nothing else reads them.
fn walk_after(block: &mut [GoStatement], indices: &Indices) -> Option<usize> {
    let after = indices.filling + 1;
    let mut positions = after..block.len();
    let walking = positions.find(|&index| mentions(&mut block[index], &indices.array))?;
    let GoStatement::Range { index: None, element, iterable, body } = &mut block[walking] else {
        return None;
    };
    let walks = match iterable {
        GoExpression::Identifier(name) => *name == indices.array,
        GoExpression::Call { function, arguments } => {
            matches!(function.as_ref(), GoExpression::Qualified { name, .. } if name == "Slice")
                && matches!(arguments.as_slice(), [GoExpression::Integer(start), end, GoExpression::Identifier(sliced)]
                    if *start >= 0 && counted_by(end).as_deref() == Some(indices.counted.as_str()) && *sliced == indices.array)
        }
        _ => false,
    };
    let element = element.clone();
    let body_keeps = !body.iter_mut().any(|statement| {
        mentions(statement, &indices.array)
            || writes(statement, &indices.counted)
            || (element != "_" && writes(statement, &element))
    });
    let later = &mut block[walking + 1..];
    let unread_after = !later.iter_mut().any(|statement| mentions(statement, &indices.array));
    let between = &mut block[after..walking];
    let untouched_before = !between.iter_mut().any(|statement| writes(statement, &indices.counted));
    (walks && body_keeps && unread_after && untouched_before).then_some(walking)
}

/// The array whose length `len(array)` is.
fn counted_by(length: &GoExpression) -> Option<String> {
    let GoExpression::Call { function, arguments } = length else { return None };
    let is_len = function.is_builtin(GoBuiltin::Len);
    match arguments.as_slice() {
        [GoExpression::Identifier(array)] if is_len => Some(array.clone()),
        _ => None,
    }
}

fn length_of(array: &str) -> GoExpression {
    GoExpression::Call {
        function: Box::new(GoExpression::builtin(GoBuiltin::Len)),
        arguments: vec![GoExpression::Identifier(array.into())],
    }
}

pub(in crate::emit) fn is_line(statement: &GoStatement) -> bool {
    matches!(statement, GoStatement::Line(_))
}
