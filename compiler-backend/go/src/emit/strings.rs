//! A PureScript string is a sequence of UTF-16 code units; go-support's prim package holds it in a
//! Go string as WTF-8, where a lone leading surrogate directly followed by a lone trailing one must
//! be spelled as the code point they form. Two such halves can only meet where two strings are
//! appended, and only where neither side of the join is known to end in whole characters: a
//! non-empty string constant, or the result of a go-support function that always begins and ends
//! in ASCII, such as `prim.ShowInt`. So an append is Go's own `+` wherever every join has such an
//! operand on one side, and `prim.Append` or `prim.Concat`, which join the halves, otherwise. Text leaving
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
        let operands = joined_constants(operands);
        if let [operand] = operands.as_slice() {
            return operand.clone();
        }
        if operands.windows(2).all(|join| has_whole_ends(&join[0]) || has_whole_ends(&join[1])) {
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
        if has_whole_ends(&suffix) {
            let spread = GoExpression::Spread(Box::new(suffix));
            return call(identifier_expression("append"), vec![buffer, spread]);
        }
        let append = GoFunction { package: GoPackage::Prim, name: "AppendString" };
        call(self.go_function(append), vec![buffer, suffix])
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

/// The operands with each run of string constants written as one, `"x2"` for `"x" + "2"`.
fn joined_constants(operands: Vec<GoExpression>) -> Vec<GoExpression> {
    let mut joined: Vec<GoExpression> = Vec::with_capacity(operands.len());
    for operand in operands {
        if let (Some(GoExpression::String(previous)), GoExpression::String(text)) =
            (joined.last_mut(), &operand)
        {
            previous.push_str(text);
            continue;
        }
        joined.push(operand);
    }
    joined
}

fn is_prim_append(function: &GoExpression) -> bool {
    matches!(
        function,
        GoExpression::Qualified { package, name }
            if package == GoPackage::Prim.name() && (name == "Append" || name == "Concat")
    )
}

/// A string that begins and ends with whole code points: a non-empty constant of valid UTF-8, or
/// what a go-support function returns that never returns an empty string and always begins and
/// ends in ASCII (digits, signs, quotes and brackets).
fn has_whole_ends(expression: &GoExpression) -> bool {
    match expression {
        GoExpression::String(text) => !text.is_empty(),
        GoExpression::Call { function, .. } => {
            super::standard::is_ascii_ended(function)
                || matches!(
                    &**function,
                    GoExpression::Qualified { package, name }
                        if package == GoPackage::Prim.name() && ASCII_ENDED.contains(&name.as_str())
                )
        }
        _ => false,
    }
}

/// Whether a call of the function only joins or shows values as text: it has no effect and
/// cannot fail, so a call whose text goes unread can be left out.
pub(super) fn only_writes_text(function: &GoExpression) -> bool {
    super::standard::is_ascii_ended(function)
        || is_prim_append(function)
        || matches!(
            function,
            GoExpression::Qualified { package, name }
                if package == GoPackage::Prim.name()
                    && matches!(name.as_str(), "ShowInt" | "ShowNumber" | "ShowString" | "ShowChar")
        )
}

/// The go-support prim functions whose result is never empty and begins and ends in ASCII.
const ASCII_ENDED: &[&str] = &[
    "ShowInt",
    "ShowNumber",
    "ShowString",
    "ShowChar",
    "ShowArray",
    "IntToStringAs",
    "NumberToString",
    "NumberToFixed",
    "NumberToPrecision",
    "NumberToExponential",
];
