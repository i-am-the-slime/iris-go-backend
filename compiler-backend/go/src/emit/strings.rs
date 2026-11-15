//! A PureScript string is a sequence of UTF-16 code units; go-support's prim package holds it in a
//! Go string as WTF-8, where a lone leading surrogate directly followed by a lone trailing one must
//! be spelled as the code point they form. Two such halves can only meet where two strings are
//! appended, and only where neither side of the join is a non-empty string constant, whose ends
//! are never lone surrogates. So an append is Go's own `+` wherever every join has a constant on
//! one side, and `prim.Append` or `prim.Concat`, which join the halves, otherwise. Text leaving
//! the program goes through `prim.ToUTF8`, which writes each lone surrogate as U+FFFD.

use super::{Emitter, binary, call, identifier_expression};
use crate::foreign::{GoFunction, GoPackage};
use crate::syntax::GoExpression;

impl<'q, Q> Emitter<'_, '_, 'q, Q>
where
    Q: checking::ExternalQueries,
{
    /// `left <> right` for strings, with the appends either side already emitted flattened into
    /// one chain.
    pub(super) fn string_append(
        &mut self,
        left: GoExpression,
        right: GoExpression,
    ) -> GoExpression {
        let mut operands = vec![];
        flatten(left, &mut operands);
        flatten(right, &mut operands);
        if operands.windows(2).all(|join| is_text_constant(&join[0]) || is_text_constant(&join[1]))
        {
            return operands
                .into_iter()
                .reduce(|left, right| binary("+", left, right))
                .expect("invariant violated: an append has two operands");
        }
        let name = if operands.len() == 2 { "Append" } else { "Concat" };
        call(self.go_function(GoFunction { package: GoPackage::Prim, name }), operands)
    }

    /// The appending of `suffix` to a string accumulated in a byte buffer.
    pub(super) fn buffer_append(
        &mut self,
        buffer: GoExpression,
        suffix: GoExpression,
    ) -> GoExpression {
        if is_text_constant(&suffix) {
            let spread = GoExpression::Spread(Box::new(suffix));
            return call(identifier_expression("append"), vec![buffer, spread]);
        }
        let append = GoFunction { package: GoPackage::Prim, name: "AppendString" };
        call(self.go_function(append), vec![buffer, suffix])
    }

    /// A string as it leaves the program as UTF-8 text, each lone surrogate U+FFFD.
    pub(super) fn printable(&mut self, text: GoExpression) -> GoExpression {
        if matches!(text, GoExpression::String(_)) {
            return text;
        }
        call(self.go_function(GoFunction { package: GoPackage::Prim, name: "ToUTF8" }), vec![text])
    }
}

/// The operands of an append chain: a string `+` is one already emitted, and so are calls to
/// `prim.Append` and `prim.Concat`.
fn flatten(expression: GoExpression, operands: &mut Vec<GoExpression>) {
    match expression {
        GoExpression::Binary { operator: "+", left, right } => {
            flatten(*left, operands);
            flatten(*right, operands);
        }
        GoExpression::Call { function, arguments } if is_prim_append(&function) => {
            operands.extend(arguments);
        }
        expression => operands.push(expression),
    }
}

fn is_prim_append(function: &GoExpression) -> bool {
    matches!(
        function,
        GoExpression::Qualified { package, name }
            if package == GoPackage::Prim.name() && (name == "Append" || name == "Concat")
    )
}

/// A non-empty string constant of valid UTF-8, which begins and ends with whole code points.
fn is_text_constant(expression: &GoExpression) -> bool {
    matches!(expression, GoExpression::String(text) if !text.is_empty())
}
