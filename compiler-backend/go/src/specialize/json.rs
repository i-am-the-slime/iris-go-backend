//! Yoga.JSON's `readJSON` and `writeJSON` at a type whose dictionary is
//! Yoga.JSON's own instances throughout, approved as a `primitives::known` entry: the emitter
//! reads the text straight into the program's values and writes them straight out
//! (`emit::json`). A dictionary with any other instance in it, a program's own or one of
//! Yoga.JSON's that the typed codec does not implement, keeps Yoga.JSON's definition.

use checking::core::Type;
use checking::evidence::InstanceCandidateOrigin;

use super::Specializer;
use crate::dictionary::Dictionary;
use crate::error::GoResult;
use crate::foreign::{Foreign, JsonCodec};
use crate::mono::{Expression, ExpressionKind};
use crate::monotype::MonotypeId;

impl<'q, Q> Specializer<'q, Q>
where
    Q: checking::ExternalQueries,
{
    /// Whether every instance in the codec's dictionary is one the typed codec implements.
    pub(super) fn json_codec_known(
        &mut self,
        codec: JsonCodec,
        dictionaries: &[Dictionary],
    ) -> GoResult<bool> {
        let [dictionary] = dictionaries else { return Ok(false) };
        self.json_instance_known(codec, dictionary, Position::Root)
    }

    fn json_instance_known(
        &mut self,
        codec: JsonCodec,
        dictionary: &Dictionary,
        position: Position,
    ) -> GoResult<bool> {
        let instance = match dictionary {
            Dictionary::Instance(instance) => instance.clone(),
            Dictionary::Symbol(_) | Dictionary::Trivial => return Ok(true),
            Dictionary::Reflectable(_) | Dictionary::Runtime(_) => return Ok(false),
        };
        let Some((class, head)) = self.instance_head(instance.origin)? else { return Ok(false) };
        let known = match (class.as_str(), head.as_str()) {
            ("Yoga.JSON.ReadForeign" | "Yoga.JSON.WriteForeign", head) => match head {
                "Prim.Int"
                | "Prim.Number"
                | "Prim.String"
                | "Prim.Boolean"
                | "Prim.Array"
                | "Prim.Record"
                | "Data.Nullable.Nullable"
                | "Foreign.Object.Object" => true,
                // JSON.stringify writes nothing for an undefined at the top, and Yoga.JSON
                // reads `Just Nothing` back as `Nothing`.
                "Data.Maybe.Maybe" => match position {
                    Position::Root => codec == JsonCodec::Read,
                    Position::Inner => true,
                    Position::Optional => false,
                },
                _ => false,
            },
            (
                "Yoga.JSON.ReadForeignFields" | "Yoga.JSON.WriteForeignFields",
                "Prim.RowList.Cons" | "Prim.RowList.Nil",
            ) => true,
            _ => false,
        };
        if !known {
            return Ok(false);
        }
        let inner = match head.as_str() {
            "Data.Maybe.Maybe" | "Data.Nullable.Nullable" => Position::Optional,
            _ => Position::Inner,
        };
        for context in instance.context.iter() {
            if !self.json_instance_known(codec, context, inner)? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    /// The qualified names of an instance's class and of the type constructor at the head of
    /// its first argument.
    pub(super) fn instance_head(
        &mut self,
        origin: InstanceCandidateOrigin,
    ) -> GoResult<Option<(String, String)>> {
        let (module, declaration) = self.instance_declaration(origin)?;
        let mut type_id = module.checked.tree[declaration].type_id;
        let mut arguments = vec![];
        let head = loop {
            match self.context.types.lookup(self.context.types.strip_annotations(type_id)).clone() {
                Type::Forall(_, inner)
                | Type::Constrained(_, inner)
                | Type::ConstraintOrigin(_, inner)
                | Type::Kinded(inner, _) => type_id = inner,
                Type::Application(function, argument) => {
                    arguments.push(argument);
                    type_id = function;
                }
                Type::KindApplication(function, _) => type_id = function,
                Type::Constructor(file_id, item) => break (file_id, item),
                _ => return Ok(None),
            }
        };
        let Some(&first) = arguments.last() else { return Ok(None) };
        let mut type_id = first;
        let argument = loop {
            match self.context.types.lookup(self.context.types.strip_annotations(type_id)).clone() {
                Type::Application(function, _) | Type::KindApplication(function, _) => {
                    type_id = function
                }
                Type::Kinded(inner, _) => type_id = inner,
                Type::Constructor(file_id, item) => break (file_id, item),
                _ => return Ok(None),
            }
        };
        Ok(Some((self.type_constructor_name(head)?, self.type_constructor_name(argument)?)))
    }

    fn type_constructor_name(
        &mut self,
        (file_id, item): (files::FileId, indexing::TypeItemId),
    ) -> GoResult<String> {
        let module = self.context.module(file_id)?;
        let name = module.indexed.items[item].name.clone().unwrap_or_default();
        Ok(format!("{}.{name}", module.name))
    }

    /// `\value -> writeJSON value`, written straight from the value.
    pub(super) fn json_write(&mut self, monotype: MonotypeId) -> Expression {
        self.foreign(Foreign::Json(JsonCodec::Write).interned(), monotype)
    }

    /// `\text -> readJSON text`, read straight into the value. Its first argument, Yoga.JSON's
    /// `reference text`, is evaluated only when the text does not decode.
    pub(super) fn json_read(&mut self, reference: Expression) -> Expression {
        let (text, result) = self
            .monotypes
            .function_parts(reference.monotype)
            .expect("invariant violated: readJSON is a function of the text");
        let text = self.fresh_local(self.monotypes.value_name(text), text);
        let reread = ExpressionKind::Apply {
            function: Box::new(reference),
            arguments: vec![text.expression()],
        };
        let arguments = vec![Expression::new(reread, result), text.expression()];
        let foreign = Foreign::Json(JsonCodec::Read).interned();
        let body = Expression::new(ExpressionKind::Foreign { foreign, arguments }, result);
        self.lambda(vec![text], body)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Position {
    Root,
    Inner,
    /// The payload of a Maybe or Nullable.
    Optional,
}
