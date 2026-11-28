//! A program whose entry is a value rather than an effect prints that value, as Go's `fmt.Println`
//! would: scalars as their text and arrays as `[a b c]`. The text is built with typed go-support
//! and `strings` calls and written with `console.Print`, so a program links neither `fmt` nor
//! `reflect`. A value of another type (a record, a data type, a function) has no such text.

use super::{Emitter, binary, builtin_call, call, identifier_expression, length};
use crate::foreign::GoFunction;
use crate::monotype::{Monotype, MonotypeId};
use crate::syntax::{GoBinaryOperator, GoBuiltin, GoExpression, GoPackage, GoStatement, GoType};

impl<'q, Q> Emitter<'_, '_, 'q, Q>
where
    Q: checking::ExternalQueries,
{
    /// The statements that print the entry's value, or `None` when its type has no text.
    pub(super) fn print_entry_value(
        &mut self,
        entry: &str,
        monotype: MonotypeId,
    ) -> Option<Vec<GoStatement>> {
        let mut statements = vec![];
        let text =
            self.text_of(identifier_expression(entry), monotype, entry, 0, &mut statements)?;
        let print = self.performing(GoFunction { package: GoPackage::Console, name: "Print" });
        statements.push(GoStatement::Expression(call(print, vec![text])));
        Some(statements)
    }

    /// `value`'s text, with the loops that build an array's text pushed onto `out`. `depth`
    /// counts the arrays `value` is an element of.
    fn text_of(
        &mut self,
        value: GoExpression,
        monotype: MonotypeId,
        entry: &str,
        depth: usize,
        out: &mut Vec<GoStatement>,
    ) -> Option<GoExpression> {
        Some(match self.monotypes.get(monotype).clone() {
            Monotype::String => value,
            Monotype::Int => self.prim_text("ShowInt", value),
            Monotype::Number => self.prim_text("NumberToString", value),
            Monotype::Char => self.prim_text("CharSingleton", value),
            Monotype::Boolean => {
                let format = self.qualified(GoPackage::Strconv, "FormatBool");
                call(format, vec![value])
            }
            Monotype::Array(element) => self.array_text(value, element, entry, depth, out)?,
            _ => return None,
        })
    }

    /// `[a b c]`: the elements' texts joined by blanks.
    fn array_text(
        &mut self,
        array: GoExpression,
        element: MonotypeId,
        entry: &str,
        depth: usize,
        out: &mut Vec<GoStatement>,
    ) -> Option<GoExpression> {
        let texts = match self.monotypes.get(element) {
            Monotype::String => array,
            _ => identifier_expression(&self.element_texts(array, element, entry, depth, out)?),
        };
        let join = self.qualified(GoPackage::Strings, "Join");
        let joined = call(join, vec![texts, GoExpression::String(" ".into())]);
        let open = binary(GoBinaryOperator::Add, GoExpression::String("[".into()), joined);
        Some(binary(GoBinaryOperator::Add, open, GoExpression::String("]".into())))
    }

    /// The name of a slice of the texts of `array`'s elements, which the loop pushed onto `out`
    /// collects.
    fn element_texts(
        &mut self,
        array: GoExpression,
        element: MonotypeId,
        entry: &str,
        depth: usize,
        out: &mut Vec<GoStatement>,
    ) -> Option<String> {
        let texts = printing_name("texts", depth, entry);
        let item = printing_name("element", depth, entry);
        let mut body = vec![];
        let text =
            self.text_of(identifier_expression(&item), element, entry, depth + 1, &mut body)?;
        let make = builtin_call(
            GoBuiltin::Make,
            vec![
                GoExpression::Type(GoType::Slice(Box::new(GoType::String))),
                GoExpression::Integer(0),
                length(array.clone()),
            ],
        );
        let append = builtin_call(GoBuiltin::Append, vec![identifier_expression(&texts), text]);
        body.push(GoStatement::Assign {
            targets: vec![identifier_expression(&texts)],
            values: vec![append],
        });
        out.push(GoStatement::Define { names: vec![texts.clone()], values: vec![make] });
        out.push(GoStatement::Range { index: None, element: item, iterable: array, body });
        Some(texts)
    }

    fn prim_text(&mut self, name: &'static str, value: GoExpression) -> GoExpression {
        call(self.go_function(GoFunction { package: GoPackage::Prim, name }), vec![value])
    }
}

/// A local of `main`, numbered by the depth of the array it prints, that is not the entry's name.
fn printing_name(base: &str, depth: usize, entry: &str) -> String {
    let name = if depth == 0 { base.to_string() } else { format!("{base}{}", depth + 1) };
    if name == entry { format!("{name}_") } else { name }
}
