//! Yoga.JSON's `readJSON` and `writeJSON` at a type whose dictionary is
//! Yoga.JSON's own instances throughout, approved as a `primitives::known` entry: the emitter
//! reads the text straight into the program's values and writes them straight out
//! (`emit::json`). A dictionary with any other instance in it, a program's own or one of
//! Yoga.JSON's that the typed codec does not implement, keeps Yoga.JSON's definition.

use checking::core::Type;
use checking::evidence::InstanceCandidateOrigin;

use files::FileId;
use indexing::TermItemId;

use super::{Definition, Scope, SpecializationKey, Specializer};
use crate::dictionary::{Dictionary, InstanceDictionary};
use crate::error::GoResult;
use crate::foreign::{Foreign, JsonCodec};
use crate::monomorphic::{Expression, ExpressionKind};
use crate::monotype::MonotypeId;
use crate::primitives::Primitive;
use crate::types::Substitution;

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
            // A variant is written as an object of its one label; reading one tries every
            // label in turn, which the typed codec does not do.
            ("Yoga.JSON.WriteForeign", "Data.Variant.Variant") => true,
            ("Yoga.JSON.WriteForeignVariant", "Prim.RowList.Cons" | "Prim.RowList.Nil") => true,
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
                    Position::Optional | Position::Payload => false,
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
        let inner = match (class.as_str(), head.as_str()) {
            (_, "Data.Maybe.Maybe" | "Data.Nullable.Nullable") => Position::Optional,
            // A variant's payload is its object's one member, which a Nothing would leave out.
            ("Yoga.JSON.WriteForeignVariant", _) => Position::Payload,
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

    /// `show` of `NonEmptyList ForeignError`, the errors a Yoga.JSON read fails with: each error
    /// by Foreign's own `show`, and the list around them by go-support, rather than by
    /// Data.List's chunked map and fold written out at every use.
    pub(super) fn show_foreign_errors(
        &mut self,
        scope: &mut Scope,
        member: (FileId, TermItemId),
        (module, name): (&str, &str),
        instance: &InstanceDictionary,
        monotype: MonotypeId,
    ) -> GoResult<Option<Expression>> {
        if (module, name) != ("Data.Show", "show") {
            return Ok(None);
        }
        let (Some(&element), [element_show @ Dictionary::Instance(shown)]) =
            (instance.types.first(), instance.context.as_ref())
        else {
            return Ok(None);
        };
        let list = self.instance_head(instance.origin)?;
        let error = self.instance_head(shown.origin)?;
        let show = |head: &str| Some(("Data.Show.Show".to_string(), head.to_string()));
        if list != show("Data.List.Types.NonEmptyList") || error != show("Foreign.ForeignError") {
            return Ok(None);
        }
        let Some((errors, text)) = self.monotypes.function_parts(monotype) else {
            return Ok(None);
        };
        let element = self.closed_monotype(scope, element)?;
        let element_monotype = self.monotypes.function(element, text);
        let element_show = self.member_reference(
            scope,
            member,
            element_show.clone(),
            &Substitution::default(),
            vec![],
            element_monotype,
        )?;
        let errors = self.fresh_local("errors".into(), errors);
        let arguments = vec![element_show, errors.expression()];
        let foreign = Foreign::ShowForeignErrors.interned();
        let body = Expression::new(ExpressionKind::Foreign { foreign, arguments }, text);
        Ok(Some(self.lambda(vec![errors], body)))
    }

    /// Whether the definition is Yoga.JSON's `readJSON` at a type the typed codec reads, whose
    /// specialization then reads the text straight into the value.
    pub(super) fn reads_json_directly(&mut self, key: &SpecializationKey) -> GoResult<bool> {
        let Definition::Value { file_id, term } = key.definition else { return Ok(false) };
        let module = self.context.module(file_id)?;
        let name = module.indexed.items[term].name.clone().unwrap_or_default();
        if crate::primitives::known(&module.name, &name) != Some(Primitive::ReadJson) {
            return Ok(false);
        }
        self.json_codec_known(JsonCodec::Read, &key.dictionaries)
    }

    /// `\text -> readJSON text`, read straight into the value. Its first argument, Yoga.JSON's
    /// `reference text`, is evaluated only when the text does not decode. The specialization
    /// of `readJSON` is this function, which the simplifier keeps out of line: its slow path
    /// is Yoga.JSON's whole reader.
    pub(super) fn json_read(&mut self, reference: Expression) -> Expression {
        let (text, result) = self
            .monotypes
            .function_parts(reference.monotype)
            .expect("invariant violated: readJSON is a function of the text");
        let text = self.fresh_local("text".into(), text);
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
    /// The payload of a variant.
    Payload,
}
