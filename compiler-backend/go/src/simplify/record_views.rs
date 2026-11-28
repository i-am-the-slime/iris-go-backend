use super::Simplifier;
use crate::foreign::{self, Foreign, GoFunction};
use crate::monomorphic::{Binding, Expression, ExpressionKind, Literal};
use crate::monotype::{Monotype, MonotypeId, RecordField};
use crate::purity::is_trivial;
use crate::syntax::GoPackage;

impl Simplifier<'_> {
    pub(super) fn is_record_view(&self, from: MonotypeId, to: MonotypeId) -> bool {
        matches!(
            (self.monotypes.get(from), self.monotypes.get(to)),
            (Monotype::Record(_), Monotype::Object(_) | Monotype::Opaque)
                | (Monotype::Object(_), Monotype::Record(_))
        )
    }

    pub(super) fn shared_view(&mut self, value: Expression) -> Expression {
        let monotype = value.monotype;
        if let ExpressionKind::Let { bindings, body } = value.kind {
            let body = self.shared_view(*body);
            return Expression::new(
                ExpressionKind::Let { bindings, body: Box::new(body) },
                monotype,
            );
        }
        let ExpressionKind::Coerce(viewed) = value.kind else { return value };
        if is_view_source(&viewed) || !self.is_record_view(viewed.monotype, monotype) {
            return Expression::new(ExpressionKind::Coerce(viewed), monotype);
        }
        let viewed = *viewed;
        let viewed_monotype = viewed.monotype;
        let mut bindings = vec![];
        let viewed = match viewed.kind {
            ExpressionKind::Record(fields) => {
                let fields = fields.into_iter().map(|(label, field)| {
                    if is_trivial(&field) {
                        return (label, field);
                    }
                    let local = self.named_local(&label, field.monotype);
                    let reference = local.expression();
                    self.view_fields.insert(local.id);
                    bindings.push(Binding { local, value: field });
                    (label, reference)
                });
                let fields = fields.collect();
                Expression::new(ExpressionKind::Record(fields), viewed_monotype)
            }
            kind => {
                let local = self.named_local("viewed", viewed_monotype);
                let reference = local.expression();
                self.view_fields.insert(local.id);
                bindings.push(Binding { local, value: Expression::new(kind, viewed_monotype) });
                reference
            }
        };
        let view = Expression::new(ExpressionKind::Coerce(Box::new(viewed)), monotype);
        Expression::new(ExpressionKind::Let { bindings, body: Box::new(view) }, monotype)
    }

    pub(super) fn remember_record_view(&mut self, binding: &Binding) {
        if let Some(viewed) = self.viewed_value(&binding.value) {
            self.record_views.insert(binding.local.id, viewed);
        }
    }

    pub(super) fn is_viewed_record(&self, value: &Expression) -> bool {
        self.viewed_value(value).is_some()
    }

    fn viewed_value(&self, value: &Expression) -> Option<Expression> {
        match &value.kind {
            ExpressionKind::Let { body, .. } => self.viewed_value(body),
            ExpressionKind::Coerce(viewed)
                if is_view_source(viewed)
                    && self.is_record_view(viewed.monotype, value.monotype) =>
            {
                Some((**viewed).clone())
            }
            _ => None,
        }
    }

    pub(super) fn record_seen_through(&self, value: &Expression) -> Option<Expression> {
        match &value.kind {
            ExpressionKind::Coerce(inner) => Some((**inner).clone()),
            ExpressionKind::Local(id) => self.record_views.get(id).cloned(),
            _ => None,
        }
    }

    fn viewed_record(&self, value: &Expression) -> Option<Expression> {
        let viewed = self.record_seen_through(value)?;
        matches!(self.monotypes.get(viewed.monotype), Monotype::Record(_)).then_some(viewed)
    }

    pub(super) fn field_of_viewed_object(
        &mut self,
        record: Expression,
        label: &str,
        monotype: MonotypeId,
    ) -> Result<Expression, Expression> {
        let ExpressionKind::Coerce(object) = &record.kind else { return Err(record) };
        let Monotype::Object(element) = *self.monotypes.get(object.monotype) else {
            return Err(record);
        };
        let ExpressionKind::Coerce(object) = record.kind else { unreachable!() };
        let read = self.object_index(*object, label, element);
        Ok(self.coerce(read, monotype))
    }

    pub(super) fn viewed_object_operation(
        &mut self,
        foreign: &'static Foreign,
        arguments: Vec<Expression>,
        monotype: MonotypeId,
    ) -> Result<Expression, Vec<Expression>> {
        let Some(record) = arguments.first().and_then(|object| self.viewed_record(object)) else {
            return Err(arguments);
        };
        let Monotype::Record(fields) = self.monotypes.get(record.monotype).clone() else {
            return Err(arguments);
        };
        let Foreign::Call { function: GoFunction { package: GoPackage::Object, name }, .. } =
            foreign
        else {
            return Err(arguments);
        };
        match (*name, arguments.as_slice()) {
            ("UnsafeIndex", [_, key]) => {
                let ExpressionKind::Literal(Literal::String(label)) = &key.kind else {
                    return Err(arguments);
                };
                let Some(field) = fields.iter().find(|field| field.label.as_str() == label) else {
                    return Err(arguments);
                };
                Ok(self.coerce(field_access(record, field), monotype))
            }
            ("Size", [_]) => {
                let size = Literal::Int(fields.len() as i64);
                Ok(Expression::new(ExpressionKind::Literal(size), monotype))
            }
            ("FmapObject", [_, _]) => {
                let [_, function] = <[Expression; 2]>::try_from(arguments).unwrap_or_else(|_| {
                    unreachable!("invariant violated: a map has two arguments")
                });
                Ok(self.mapped_record(record, &fields, function, monotype))
            }
            _ => Err(arguments),
        }
    }

    fn mapped_record(
        &mut self,
        record: Expression,
        fields: &[RecordField],
        function: Expression,
        object: MonotypeId,
    ) -> Expression {
        let Monotype::Object(element) = *self.monotypes.get(object) else {
            unreachable!("invariant violated: a map over an object makes an object")
        };
        let mut bindings = vec![];
        let function = match is_trivial(&function) {
            true => function,
            false => {
                let local = self.named_local("function", function.monotype);
                let reference = local.expression();
                bindings.push(Binding { local, value: function });
                reference
            }
        };
        let mapped_fields: Vec<RecordField> = fields
            .iter()
            .map(|field| RecordField { label: field.label.clone(), monotype: element })
            .collect();
        let mapped = self.monotypes.intern(Monotype::Record(mapped_fields.into()));
        let values = fields.iter().map(|field| {
            let applied = ExpressionKind::Apply {
                function: Box::new(function.clone()),
                arguments: vec![field_access(record.clone(), field)],
            };
            (field.label.clone(), Expression::new(applied, element))
        });
        let values = values.collect();
        let mapped = Expression::new(ExpressionKind::Record(values), mapped);
        let view = Expression::new(ExpressionKind::Coerce(Box::new(mapped)), object);
        let kind = ExpressionKind::Let { bindings, body: Box::new(view) };
        let expression = match kind {
            ExpressionKind::Let { bindings, body } if bindings.is_empty() => *body,
            kind => Expression::new(kind, object),
        };
        self.expression(expression)
    }

    fn object_index(&mut self, object: Expression, label: &str, element: MonotypeId) -> Expression {
        let string = self.monotypes.intern(Monotype::String);
        let key = ExpressionKind::Literal(Literal::String(label.to_string()));
        let arguments = vec![object, Expression::new(key, string)];
        Expression::new(
            ExpressionKind::Foreign { foreign: &foreign::OBJECT_INDEX, arguments },
            element,
        )
    }
}

fn field_access(record: Expression, field: &RecordField) -> Expression {
    let access = ExpressionKind::Access { record: Box::new(record), label: field.label.clone() };
    Expression::new(access, field.monotype)
}

fn is_view_source(value: &Expression) -> bool {
    match &value.kind {
        ExpressionKind::Record(fields) => fields.iter().all(|(_, field)| is_trivial(field)),
        _ => is_trivial(value),
    }
}
