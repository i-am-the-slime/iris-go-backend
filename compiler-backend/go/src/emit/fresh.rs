//! A slice just made empty has no spare capacity to clip.
//!
//! A fold that appends to its accumulator clips the initial value, so that appending never
//! writes into an array someone else holds: `accumulator := []int32{}; accumulator =
//! slices.Clip(accumulator)`. An empty literal has no capacity, and the clip does nothing.

use crate::go_traversal::each_block_in_declaration;
use crate::syntax::{GoDeclaration, GoExpression, GoStatement, GoType};

pub(super) fn drop_clips_of_fresh_slices(declarations: &mut [GoDeclaration]) {
    for declaration in declarations {
        each_block_in_declaration(declaration, |block| {
            let mut position = 0;
            while position < block.len() {
                let fresh = fresh_slice(&block[position]);
                let next = (position + 1..block.len())
                    .find(|&next| !matches!(block[next], GoStatement::Line(_)));
                match (fresh, next) {
                    (Some(name), Some(next)) if clips(&block[next], name) => {
                        block.remove(next);
                    }
                    _ => position += 1,
                }
            }
        });
    }
}

fn fresh_slice(statement: &GoStatement) -> Option<&str> {
    let GoStatement::Define { names, values } = statement else { return None };
    match (names.as_slice(), values.as_slice()) {
        ([name], [GoExpression::Composite { type_: GoType::Slice(_), fields }])
            if fields.is_empty() =>
        {
            Some(name)
        }
        _ => None,
    }
}

fn clips(statement: &GoStatement, name: &str) -> bool {
    let GoStatement::Assign { targets, values } = statement else { return false };
    let ([GoExpression::Identifier(target)], [GoExpression::Call { function, arguments }]) =
        (targets.as_slice(), values.as_slice())
    else {
        return false;
    };
    target == name
        && matches!(function.as_ref(),
            GoExpression::Qualified { package, name } if package == "slices" && name == "Clip")
        && matches!(arguments.as_slice(), [GoExpression::Identifier(clipped)] if clipped == name)
}
