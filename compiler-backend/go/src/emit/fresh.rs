//! A slice just made empty has no spare capacity to clip.
//!
//! A fold that appends to its accumulator clips the initial value, so that appending never
//! writes into an array someone else holds: `accumulator := []int{}; accumulator =
//! slices.Clip(accumulator)`. An empty literal has no capacity, and the clip does nothing.

use crate::go_traversal::each_block_in_declaration;
use crate::syntax::{GoDeclaration, GoExpression, GoStatement, GoType};

pub(super) fn drop_clips_of_fresh_slices(declarations: &mut [GoDeclaration]) {
    for declaration in declarations {
        each_block_in_declaration(declaration, |block| {
            let mut position = 0;
            while position < block.len() {
                let fresh = fresh_slice(&block[position])
                    .map(|(name, type_)| (name.to_string(), type_.clone()));
                let next = (position + 1..block.len())
                    .find(|&next| !matches!(block[next], GoStatement::Line(_)));
                let (Some((name, type_)), Some(next)) = (fresh, next) else {
                    position += 1;
                    continue;
                };
                if clips(&block[next], &name) {
                    block.remove(next);
                } else if let Some(capacity) = grown(&block[next], &name) {
                    let made = GoExpression::Call {
                        function: Box::new(GoExpression::Identifier("make".into())),
                        arguments: vec![
                            GoExpression::Type(type_),
                            GoExpression::Integer(0),
                            capacity,
                        ],
                    };
                    block[position] = GoStatement::Define { names: vec![name], values: vec![made] };
                    block.remove(next);
                } else {
                    position += 1;
                }
            }
        });
    }
}

fn fresh_slice(statement: &GoStatement) -> Option<(&str, &GoType)> {
    let GoStatement::Define { names, values } = statement else { return None };
    match (names.as_slice(), values.as_slice()) {
        ([name], [GoExpression::Composite { type_: type_ @ GoType::Slice(_), fields }])
            if fields.is_empty() =>
        {
            Some((name, type_))
        }
        _ => None,
    }
}

fn clips(statement: &GoStatement, name: &str) -> bool {
    let GoStatement::Assign { targets, values } = statement else { return false };
    matches!((targets.as_slice(), values.as_slice()),
        ([GoExpression::Identifier(target)], [value]) if target == name && clip_of(value, name))
}

fn grown(statement: &GoStatement, name: &str) -> Option<GoExpression> {
    let GoStatement::Assign { targets, values } = statement else { return None };
    let ([GoExpression::Identifier(target)], [GoExpression::Call { function, arguments }]) =
        (targets.as_slice(), values.as_slice())
    else {
        return None;
    };
    let [clip, capacity] = arguments.as_slice() else { return None };
    (target == name && is_slices_function(function, "Grow") && clip_of(clip, name))
        .then(|| capacity.clone())
}

fn clip_of(value: &GoExpression, name: &str) -> bool {
    let GoExpression::Call { function, arguments } = value else { return false };
    is_slices_function(function, "Clip")
        && matches!(arguments.as_slice(), [GoExpression::Identifier(clipped)] if clipped == name)
}

fn is_slices_function(function: &GoExpression, expected: &str) -> bool {
    matches!(function, GoExpression::Qualified { package, name } if package == "slices" && name == expected)
}
