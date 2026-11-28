//! Arrays that a tail loop maps from one iteration to the next, built in recycled buffers.
//!
//! `go i xs = if i >= n then xs else go (i + 1) (map f xs)` allocates an array per iteration,
//! although the array of the iteration before last is dead by the time the next one is built.
//! The loop keeps the two arrays it built last, and each `map` writes into the older one:
//!
//! ```go
//! var xsOwned, xsSpare []T
//! for {
//!     ...
//!     mapped := recycle(xsSpare, len(xs))
//!     for index, x := range xs {
//!         mapped[index] = f(x)
//!     }
//!     xsOwned, xsSpare = mapped, xsOwned
//!     i, xs = i + 1, mapped
//! }
//! ```
//!
//! The callback may read `xs` as a whole, which a map in place could not allow: it writes into
//! a buffer that nothing reads. The buffer is the array that `xs` held an iteration before, and
//! it is dead when nothing that reaches the next iteration can refer to it. That holds when
//!
//! - the loop is pure,
//! - its elements, and every value of the iteration that is computed from the parameter but is
//!   not the loop's final result, hold no references: numbers, strings, records and data types
//!   of them, but no arrays and no functions.
//!
//! The array the loop is called with is not its own, so the first two iterations allocate.

use rustc_hash::FxHashSet;

use super::uniqueness::{TailLoop, next_iterations};
use super::{Emitter, call, identifier_expression};
use crate::foreign::{Boundary, Foreign, Iteration};
use crate::monomorphic::traversal::mentions_local;
use crate::monomorphic::{Expression, ExpressionKind, Function, FunctionId};
use crate::monotype::{Monotype, MonotypeId};
use crate::syntax::{GoExpression, GoStatement, GoType};

/// The two arrays a loop parameter recycles, by their variables.
#[derive(Clone)]
pub(super) struct Recycled {
    pub owned: String,
    pub spare: String,
}

impl<'q, Q> Emitter<'_, '_, 'q, Q>
where
    Q: checking::ExternalQueries,
{
    /// The maps that every jump of the loop of `function` passes as its parameter at `position`,
    /// when they may write into the loop's recycled buffers: a value that reaches past the
    /// iteration may be computed from the parameter only when it holds no references.
    pub(super) fn recycled_maps(
        &mut self,
        id: FunctionId,
        function: &Function,
        position: usize,
    ) -> Option<Vec<*const Expression>> {
        let parameter = &function.parameters[position];
        let Monotype::Array(element) = *self.monotypes.get(parameter.monotype) else {
            return None;
        };
        if self.holds_references(element, &mut FxHashSet::default()) {
            return None;
        }
        let tail_loop = TailLoop {
            function: id,
            arity: function.parameters.len(),
            position,
            parameter: parameter.id,
        };
        let next = next_iterations(tail_loop, &function.body, &mut |value| {
            mentions_local(value, tail_loop.parameter)
                && self.holds_references(value.monotype, &mut FxHashSet::default())
        })?;
        let maps = next
            .into_iter()
            .filter(|next| is_map(next) && next.monotype == parameter.monotype)
            .map(|map| {
                let ExpressionKind::Foreign { arguments, .. } = &map.kind else {
                    unreachable!("invariant violated: a map is a foreign call")
                };
                std::ptr::from_ref(&arguments[0])
            });
        let maps: Vec<*const Expression> = maps.collect();
        (!maps.is_empty()).then_some(maps)
    }

    /// Whether a value of this type may refer to an array or a function.
    fn holds_references(&mut self, monotype: MonotypeId, seen: &mut FxHashSet<MonotypeId>) -> bool {
        if !seen.insert(monotype) {
            return false;
        }
        match self.monotypes.get(monotype).clone() {
            Monotype::Int
            | Monotype::Number
            | Monotype::Boolean
            | Monotype::Char
            | Monotype::String
            | Monotype::Unit
            | Monotype::BigInt => false,
            Monotype::Record(fields) => {
                fields.iter().any(|field| self.holds_references(field.monotype, seen))
            }
            Monotype::Data(data) => self.constructor_fields(&data).map_or(true, |fields| {
                fields.into_iter().any(|field| self.holds_references(field, seen))
            }),
            _ => true,
        }
    }

    /// `recycle(spare, count)`: the recycled buffer holding `count` elements, grown when it
    /// cannot hold them, or emptied for appending without a count.
    pub(super) fn recycled_buffer(
        &mut self,
        recycled: &Recycled,
        count: Option<GoExpression>,
    ) -> GoExpression {
        let recycle = self.support_function("recycle", RECYCLE_SOURCE);
        let count = count.unwrap_or(GoExpression::Integer(0));
        call(identifier_expression(&recycle), vec![identifier_expression(&recycled.spare), count])
    }

    /// `owned, spare = mapped, owned`: the array just built is the loop's, and the one it held
    /// before is free once the loop jumps.
    pub(super) fn rotate(recycled: &Recycled, mapped: &str) -> GoStatement {
        GoStatement::Assign {
            targets: vec![
                identifier_expression(&recycled.owned),
                identifier_expression(&recycled.spare),
            ],
            values: vec![identifier_expression(mapped), identifier_expression(&recycled.owned)],
        }
    }

    /// `var owned, spare []T`, both empty until the loop builds its first arrays.
    pub(super) fn recycled_declarations(recycled: &Recycled, type_: &GoType) -> [GoStatement; 2] {
        [&recycled.owned, &recycled.spare].map(|name| GoStatement::Variable {
            name: name.clone(),
            type_: type_.clone(),
            value: None,
        })
    }
}

const RECYCLE_SOURCE: &str =
    "func {name}[T any, N ~int | ~int32 | ~int64](buffer []T, count N) []T {
\tif cap(buffer) < int(count) {
\t\treturn make([]T, count)
\t}
\treturn buffer[:count]
}
";

fn is_map(expression: &Expression) -> bool {
    matches!(
        expression.kind,
        ExpressionKind::Foreign {
            foreign: Foreign::Call {
                boundary: Boundary {
                    iteration: Some(Iteration::Map | Iteration::MapWithIndex),
                    ..
                },
                ..
            },
            ..
        }
    )
}
