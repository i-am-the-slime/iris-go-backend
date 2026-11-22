use checking::evidence::InstanceCandidateOrigin;
use files::FileId;
use indexing::TermItemId;
use smol_str::SmolStr;

use super::{Scope, Specializer};
use crate::dictionary::Dictionary;
use crate::error::GoResult;
use crate::foreign::{Foreign, Operator};
use crate::monomorphic::{
    Alternative, Expression, ExpressionKind, Guarded, Literal, Pattern, PatternKind,
};
use crate::monotype::{Monotype, MonotypeId};
use crate::types::Substitution;

struct ShownConstructor {
    name: SmolStr,
    fields: Vec<Dictionary>,
}

impl<'q, Q> Specializer<'q, Q>
where
    Q: checking::ExternalQueries,
{
    pub(super) fn generic_show(
        &mut self,
        scope: &mut Scope,
        dictionaries: &[Dictionary],
        monotype: MonotypeId,
    ) -> GoResult<Option<Expression>> {
        let [Dictionary::Instance(generic), shown] = dictionaries else { return Ok(None) };
        if !matches!(generic.origin, InstanceCandidateOrigin::Derive(..)) {
            return Ok(None);
        }
        let Some((argument, text)) = self.monotypes.function_parts(monotype) else {
            return Ok(None);
        };
        let mut constructors = vec![];
        if !self.shown_constructors(shown, &mut constructors)? {
            return Ok(None);
        }
        let Some(show) = self.show_member()? else { return Ok(None) };
        let value = self.fresh_local(self.monotypes.value_name(argument), argument);
        let Monotype::Data(data) = self.monotypes.get(argument).clone() else {
            let [ShownConstructor { name, fields }] = constructors.as_slice() else {
                return Ok(None);
            };
            let [field] = fields.as_slice() else { return Ok(None) };
            let shown_field = self.shown_field(scope, show, field, value.expression(), text)?;
            let body = self.constructor_text(name, vec![shown_field], text);
            return Ok(Some(self.lambda(vec![value], body)));
        };
        let declared = self
            .monotypes
            .constructors(&mut self.context, &data)
            .map_err(|failure| failure.at(&scope.definition))?;
        if declared.len() != constructors.len() {
            return Ok(None);
        }
        let mut alternatives = Vec::with_capacity(constructors.len());
        for (index, (declared, shown)) in declared.iter().zip(&constructors).enumerate() {
            if declared.name != shown.name || declared.fields.len() != shown.fields.len() {
                return Ok(None);
            }
            let mut patterns = vec![];
            let mut texts = vec![];
            for (&field, dictionary) in declared.fields.iter().zip(&shown.fields) {
                let local = self.fresh_local(self.monotypes.value_name(field), field);
                let shown_field =
                    self.shown_field(scope, show, dictionary, local.expression(), text)?;
                texts.push(shown_field);
                patterns.push(Pattern { kind: PatternKind::Variable(local), monotype: field });
            }
            let kind = PatternKind::Constructor {
                data: data.clone(),
                constructor: index,
                arguments: patterns,
            };
            let pattern = Pattern { kind, monotype: argument };
            let body = self.constructor_text(&shown.name, texts, text);
            let body = Guarded::Unconditional(body);
            alternatives.push(Alternative { patterns: vec![pattern], body, position: None });
        }
        let case = ExpressionKind::Case { scrutinees: vec![value.expression()], alternatives };
        let body = Expression::new(case, text);
        Ok(Some(self.lambda(vec![value], body)))
    }

    fn shown_constructors(
        &mut self,
        dictionary: &Dictionary,
        constructors: &mut Vec<ShownConstructor>,
    ) -> GoResult<bool> {
        let Dictionary::Instance(instance) = dictionary else { return Ok(false) };
        let Some((class, head)) = self.instance_head(instance.origin)? else { return Ok(false) };
        match (class.as_str(), head.as_str(), &*instance.context) {
            ("Data.Show.Generic.GenericShow", "Data.Generic.Rep.Sum", [left, right]) => Ok(self
                .shown_constructors(left, constructors)?
                && self.shown_constructors(right, constructors)?),
            (
                "Data.Show.Generic.GenericShow",
                "Data.Generic.Rep.Constructor",
                [arguments, Dictionary::Symbol(name)],
            ) => {
                let mut fields = vec![];
                if !self.shown_arguments(arguments, &mut fields)? {
                    return Ok(false);
                }
                constructors.push(ShownConstructor { name: name.clone(), fields });
                Ok(true)
            }
            _ => Ok(false),
        }
    }

    fn shown_arguments(
        &mut self,
        dictionary: &Dictionary,
        fields: &mut Vec<Dictionary>,
    ) -> GoResult<bool> {
        let Dictionary::Instance(instance) = dictionary else { return Ok(false) };
        let Some((class, head)) = self.instance_head(instance.origin)? else { return Ok(false) };
        match (class.as_str(), head.as_str(), &*instance.context) {
            ("Data.Show.Generic.GenericShowArgs", "Data.Generic.Rep.NoArguments", []) => Ok(true),
            ("Data.Show.Generic.GenericShowArgs", "Data.Generic.Rep.Product", [left, right]) => {
                Ok(self.shown_arguments(left, fields)? && self.shown_arguments(right, fields)?)
            }
            ("Data.Show.Generic.GenericShowArgs", "Data.Generic.Rep.Argument", [show]) => {
                fields.push(show.clone());
                Ok(true)
            }
            _ => Ok(false),
        }
    }

    fn show_member(&mut self) -> GoResult<Option<(FileId, TermItemId)>> {
        let Some(file_id) = self.context.queries.module_file("Data.Show") else {
            return Ok(None);
        };
        let module = self.context.module(file_id)?;
        let member =
            module.indexed.items.iter_terms().find_map(|(item, indexed)| {
                (indexed.name.as_deref() == Some("show")).then_some(item)
            });
        Ok(member.map(|member| (file_id, member)))
    }

    fn shown_field(
        &mut self,
        scope: &mut Scope,
        show: (FileId, TermItemId),
        dictionary: &Dictionary,
        field: Expression,
        text: MonotypeId,
    ) -> GoResult<Expression> {
        let monotype = self.monotypes.function(field.monotype, text);
        let function = self.member_reference(
            scope,
            show,
            dictionary.clone(),
            &Substitution::default(),
            vec![],
            monotype,
        )?;
        let kind = ExpressionKind::Apply { function: Box::new(function), arguments: vec![field] };
        Ok(Expression::new(kind, text))
    }

    fn constructor_text(
        &mut self,
        name: &str,
        fields: Vec<Expression>,
        text: MonotypeId,
    ) -> Expression {
        let constant = |value: &str| {
            Expression::new(ExpressionKind::Literal(Literal::String(value.to_string())), text)
        };
        if fields.is_empty() {
            return constant(name);
        }
        let append = Foreign::Operator(Operator::StringAppend).interned();
        let mut parts = vec![constant("("), constant(name)];
        for field in fields {
            parts.push(constant(" "));
            parts.push(field);
        }
        parts.push(constant(")"));
        parts
            .into_iter()
            .reduce(|left, right| {
                let kind =
                    ExpressionKind::Foreign { foreign: append, arguments: vec![left, right] };
                Expression::new(kind, text)
            })
            .expect("invariant violated: a constructor's text has parts")
    }
}
