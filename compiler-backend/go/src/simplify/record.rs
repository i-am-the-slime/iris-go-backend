use smol_str::SmolStr;

use super::Simplifier;
use crate::foreign::{self, Foreign, RecordOperation};
use crate::monomorphic::{Binding, Expression, ExpressionKind, Literal, Local, LocalId};
use crate::monotype::{Monotype, MonotypeId};

type Fields = Vec<(SmolStr, Expression)>;

impl Simplifier<'_> {
    pub(super) fn record_operation(
        &mut self,
        operation: RecordOperation,
        arguments: Vec<Expression>,
        monotype: MonotypeId,
    ) -> Expression {
        let mut bindings = vec![];
        let Some(fields) = self.operate(operation, &arguments, monotype, &mut bindings) else {
            let foreign = Foreign::Record(operation).interned();
            let kind = ExpressionKind::Foreign { foreign, arguments };
            return Expression::new(kind, monotype);
        };
        let Some(fields) = self.retyped(fields, monotype) else {
            let foreign = Foreign::Record(operation).interned();
            let kind = ExpressionKind::Foreign { foreign, arguments };
            return Expression::new(kind, monotype);
        };
        let mut record = Expression::new(ExpressionKind::Record(fields), monotype);
        for bindings in bindings.into_iter().rev() {
            record =
                Expression::new(ExpressionKind::Let { bindings, body: Box::new(record) }, monotype);
        }
        self.expression(record)
    }

    pub(super) fn coerce(&mut self, mut value: Expression, monotype: MonotypeId) -> Expression {
        if self.monotypes.same_without_causes(value.monotype, monotype) {
            value.monotype = monotype;
            return value;
        }
        // Unit has one value, so a coerced one is it, whatever it was before.
        if let Monotype::Unit = self.monotypes.get(monotype)
            && crate::purity::is_discardable(&value)
        {
            return Expression::new(ExpressionKind::Unit, monotype);
        }
        if let Some(widened) = self.widened_record(&value, monotype) {
            return widened;
        }
        if let Monotype::Record(_) = self.monotypes.get(value.monotype)
            && let Monotype::Opaque = self.monotypes.get(monotype)
        {
            return self.foreign_record(value, monotype);
        }
        if let Monotype::Record(_) = self.monotypes.get(value.monotype)
            && let Monotype::Object(element) = *self.monotypes.get(monotype)
        {
            return self.homogeneous_object(value, element, monotype);
        }
        Expression::new(ExpressionKind::Coerce(Box::new(value)), monotype)
    }

    /// A record narrowed by a coercion, updated, and coerced back to a type with more fields:
    /// a Go struct of the narrow type has no room for the fields it lost, so the update is made
    /// to the record before it was narrowed, which still holds them, as JavaScript's copy does.
    fn widened_record(&mut self, value: &Expression, wide: MonotypeId) -> Option<Expression> {
        let Monotype::Record(wide_fields) = self.monotypes.get(wide).clone() else { return None };
        let Monotype::Record(narrow_fields) = self.monotypes.get(value.monotype).clone() else {
            return None;
        };
        let holds = |fields: &[crate::monotype::RecordField]| {
            wide_fields.iter().all(|wide| fields.iter().any(|field| field.label == wide.label))
        };
        if holds(&narrow_fields) {
            return None;
        }
        match &value.kind {
            ExpressionKind::Coerce(before) => {
                let Monotype::Record(before_fields) = self.monotypes.get(before.monotype).clone()
                else {
                    return None;
                };
                holds(&before_fields).then(|| self.coerce((**before).clone(), wide))
            }
            ExpressionKind::Update { record, updates } => {
                let keeps_types = updates.iter().all(|update| {
                    let label = match update {
                        crate::monomorphic::RecordUpdate::Leaf { label, .. }
                        | crate::monomorphic::RecordUpdate::Branch { label, .. } => label,
                    };
                    let narrow = narrow_fields.iter().find(|field| field.label == *label);
                    let wide = wide_fields.iter().find(|field| field.label == *label);
                    matches!((narrow, wide), (Some(narrow), Some(wide))
                        if self.monotypes.same_without_causes(narrow.monotype, wide.monotype))
                });
                if !keeps_types {
                    return None;
                }
                let record = self.widened_record(record, wide)?;
                let kind =
                    ExpressionKind::Update { record: Box::new(record), updates: updates.clone() };
                Some(Expression::new(kind, wide).replacing(value.position))
            }
            ExpressionKind::Let { bindings, body } => {
                let body = self.widened_record(body, wide)?;
                let kind = ExpressionKind::Let { bindings: bindings.clone(), body: Box::new(body) };
                Some(Expression::new(kind, wide).replacing(value.position))
            }
            ExpressionKind::Local(id) => {
                let bound = self.narrowed_records.get(id)?.clone();
                self.widened_record(&bound, wide)
            }
            _ => None,
        }
    }

    pub(super) fn remember_record_order(&mut self, binding: &Binding) {
        if matches!(binding.value.kind, ExpressionKind::Update { .. } | ExpressionKind::Coerce(_))
            && let Monotype::Record(_) = self.monotypes.get(binding.value.monotype)
        {
            self.narrowed_records.insert(binding.local.id, binding.value.clone());
        }
        if let Some(order) = self.record_order(&binding.value) {
            self.record_orders.insert(binding.local.id, order);
        }
    }

    fn record_order(&self, record: &Expression) -> Option<Vec<SmolStr>> {
        match &record.kind {
            ExpressionKind::Record(fields) => {
                Some(fields.iter().map(|(label, _)| label.clone()).collect())
            }
            ExpressionKind::Let { body, .. } => self.record_order(body),
            ExpressionKind::Local(id) => self.record_orders.get(id).cloned(),
            _ => None,
        }
    }

    fn foreign_record(&mut self, record: Expression, foreign: MonotypeId) -> Expression {
        let mut bindings = vec![];
        let Some(fields) = self.fields(&record, &mut bindings) else {
            return Expression::new(ExpressionKind::Coerce(Box::new(record)), foreign);
        };
        let string = self.monotypes.intern(Monotype::String);
        let keys = self.monotypes.intern(Monotype::Array(string));
        let values = self.monotypes.intern(Monotype::Array(foreign));
        let (labels, fields): (Vec<_>, Vec<_>) = fields
            .into_iter()
            .map(|(label, value)| {
                let label = ExpressionKind::Literal(Literal::String(label.to_string()));
                let value = ExpressionKind::Coerce(Box::new(value));
                (Expression::new(label, string), Expression::new(value, foreign))
            })
            .unzip();
        let arguments = vec![
            Expression::new(ExpressionKind::Array(labels), keys),
            Expression::new(ExpressionKind::Array(fields), values),
        ];
        let kind = ExpressionKind::Foreign { foreign: &foreign::FOREIGN_RECORD, arguments };
        let mut converted = Expression::new(kind, foreign);
        for bindings in bindings.into_iter().rev() {
            let kind = ExpressionKind::Let { bindings, body: Box::new(converted) };
            converted = Expression::new(kind, foreign);
        }
        self.expression(converted)
    }

    fn homogeneous_object(
        &mut self,
        record: Expression,
        element: MonotypeId,
        object: MonotypeId,
    ) -> Expression {
        let mut bindings = vec![];
        let Some(fields) = self.fields(&record, &mut bindings) else {
            return Expression::new(ExpressionKind::Coerce(Box::new(record)), object);
        };
        let string = self.monotypes.intern(Monotype::String);
        let keys = self.monotypes.intern(Monotype::Array(string));
        let values = self.monotypes.intern(Monotype::Array(element));
        let (labels, fields): (Vec<_>, Vec<_>) = fields
            .into_iter()
            .map(|(label, value)| {
                let label = ExpressionKind::Literal(Literal::String(label.to_string()));
                (Expression::new(label, string), self.coerce(value, element))
            })
            .unzip();
        let arguments = vec![
            Expression::new(ExpressionKind::Array(labels), keys),
            Expression::new(ExpressionKind::Array(fields), values),
        ];
        let kind = ExpressionKind::Foreign { foreign: &foreign::OBJECT_FROM_ENTRIES, arguments };
        let mut converted = Expression::new(kind, object);
        for bindings in bindings.into_iter().rev() {
            let kind = ExpressionKind::Let { bindings, body: Box::new(converted) };
            converted = Expression::new(kind, object);
        }
        self.expression(converted)
    }

    pub(super) fn settle_records(&mut self, expression: &mut Expression) {
        if let ExpressionKind::Let { bindings, body } = &mut expression.kind {
            for binding in bindings.iter_mut() {
                self.settle_records(&mut binding.value);
                self.remember_record_order(binding);
            }
            self.settle_records(body);
            // A settled operation may no longer read a binding (`shrinkImpl`'s
            // keys), which then goes as any unused binding does.
            let unused = |binding: &Binding, bindings: &[Binding], body: &Expression| {
                crate::purity::occurrences(body, binding.local.id).total == 0
                    && bindings.iter().all(|other| {
                        crate::purity::occurrences(&other.value, binding.local.id).total == 0
                    })
                    && !crate::purity::runs_effect(self, &binding.value)
            };
            while let Some(position) =
                bindings.iter().position(|binding| unused(binding, bindings, body))
            {
                bindings.remove(position);
            }
            if bindings.is_empty() {
                let body = std::mem::replace(
                    &mut **body,
                    Expression::new(ExpressionKind::Unit, expression.monotype),
                );
                *expression = body;
            }
            return;
        }
        crate::monomorphic::traversal::for_each_child_mut(expression, &mut |child| {
            self.settle_records(child)
        });
        let monotype = expression.monotype;
        match &mut expression.kind {
            ExpressionKind::Foreign { foreign: Foreign::Record(operation), arguments } => {
                let operation = *operation;
                let arguments = std::mem::take(arguments);
                *expression = self.record_operation(operation, arguments, monotype);
            }
            ExpressionKind::Coerce(value) => {
                let value = std::mem::replace(
                    &mut **value,
                    Expression::new(ExpressionKind::Unit, monotype),
                );
                *expression = self.coerce(value, monotype);
            }
            _ => {}
        }
    }

    fn operate(
        &mut self,
        operation: RecordOperation,
        arguments: &[Expression],
        monotype: MonotypeId,
        bindings: &mut Vec<Vec<Binding>>,
    ) -> Option<Fields> {
        match (operation, arguments) {
            (RecordOperation::Shrink, [_keys, record]) => {
                let Monotype::Record(kept) = self.monotypes.get(monotype).clone() else {
                    return None;
                };
                let mut fields = self.fields(record, bindings)?;
                fields.retain(|(field, _)| kept.iter().any(|kept| kept.label == *field));
                Some(fields)
            }
            (RecordOperation::Insert, [label, value, record]) => {
                let label = literal_label(label)?;
                let mut fields = self.fields(record, bindings)?;
                assign(&mut fields, label, value.clone());
                Some(fields)
            }
            (RecordOperation::Modify, [label, function, record]) => {
                let label = literal_label(label)?;
                let mut fields = self.fields(record, bindings)?;
                let (_, previous) = fields.iter_mut().find(|(field, _)| *field == label)?;
                let result = self.monotypes.result_after(function.monotype, 1);
                let modified = ExpressionKind::Apply {
                    function: Box::new(function.clone()),
                    arguments: vec![previous.clone()],
                };
                *previous = Expression::new(modified, result);
                Some(fields)
            }
            (RecordOperation::Delete, [label, record]) => {
                let label = literal_label(label)?;
                let mut fields = self.fields(record, bindings)?;
                fields.retain(|(field, _)| *field != label);
                Some(fields)
            }
            (RecordOperation::Rename, [from, to, record]) => {
                let from = literal_label(from)?;
                let to = literal_label(to)?;
                let mut fields = self.fields(record, bindings)?;
                let position = fields.iter().position(|(field, _)| *field == from)?;
                let (_, value) = fields.remove(position);
                assign(&mut fields, to, value);
                Some(fields)
            }
            (RecordOperation::Union, [left, right]) => {
                let left = self.fields(left, bindings)?;
                let mut fields = self.fields(right, bindings)?;
                for (label, value) in left {
                    assign(&mut fields, label, value);
                }
                Some(fields)
            }
            _ => None,
        }
    }

    fn fields(&mut self, record: &Expression, bindings: &mut Vec<Vec<Binding>>) -> Option<Fields> {
        match &record.kind {
            ExpressionKind::Record(fields) => Some(fields.clone()),
            ExpressionKind::Let { bindings: inner, body } => {
                bindings.push(inner.clone());
                self.fields(body, bindings)
            }
            _ => {
                let Monotype::Record(types) = self.monotypes.get(record.monotype).clone() else {
                    return None;
                };
                let order = match self.record_order(record) {
                    Some(order) if order.len() == types.len() => order,
                    _ if !self.records_settled => return None,
                    _ => types.iter().map(|field| field.label.clone()).collect(),
                };
                let record = self.shared(record.clone(), bindings);
                let mut fields = Vec::with_capacity(order.len());
                for label in order {
                    let field = types.iter().find(|field| field.label == label)?;
                    let kind = ExpressionKind::Access {
                        record: Box::new(record.clone()),
                        label: label.clone(),
                    };
                    fields.push((label, Expression::new(kind, field.monotype)));
                }
                Some(fields)
            }
        }
    }

    fn retyped(&mut self, fields: Fields, monotype: MonotypeId) -> Option<Fields> {
        let Monotype::Record(types) = self.monotypes.get(monotype).clone() else {
            return None;
        };
        if fields.len() != types.len() {
            return None;
        }
        let mut retyped = Vec::with_capacity(fields.len());
        for (label, value) in fields {
            let field = types.iter().find(|field| field.label == label)?;
            if self.monotypes.same_without_causes(value.monotype, field.monotype) {
                retyped.push((label, value));
                continue;
            }
            let coerced = ExpressionKind::Coerce(Box::new(value));
            retyped.push((label, Expression::new(coerced, field.monotype)));
        }
        Some(retyped)
    }

    fn shared(&mut self, record: Expression, bindings: &mut Vec<Vec<Binding>>) -> Expression {
        if let ExpressionKind::Local(_) = record.kind {
            return record;
        }
        let template = Local { id: LocalId(0), name: "record".into(), monotype: record.monotype };
        let local = self.fresh(&template);
        let reference = Expression::new(ExpressionKind::Local(local.id), local.monotype);
        bindings.push(vec![Binding { local, value: record }]);
        reference
    }
}

fn assign(fields: &mut Fields, label: SmolStr, value: Expression) {
    match fields.iter_mut().find(|(field, _)| *field == label) {
        Some((_, previous)) => *previous = value,
        None => fields.push((label, value)),
    }
}

fn literal_label(label: &Expression) -> Option<SmolStr> {
    match &label.kind {
        ExpressionKind::Literal(Literal::String(label)) => Some(SmolStr::from(label.as_str())),
        _ => None,
    }
}

impl Simplifier<'_> {
    /// `unsafeHas label record` with a label known only at run time asks
    /// whether the label is one of the record type's.
    pub(super) fn record_has(
        &mut self,
        arguments: Vec<Expression>,
        monotype: MonotypeId,
    ) -> Expression {
        let Some(fields) = self.dynamic_fields(&arguments) else {
            let kind = ExpressionKind::Foreign { foreign: &Foreign::RecordHas, arguments };
            return Expression::new(kind, monotype);
        };
        let [label, _record]: [Expression; 2] =
            arguments.try_into().expect("invariant violated: unsafeHas has two arguments");
        let mut bindings = vec![];
        let label = self.shared_operand(label, "label", &mut bindings);
        let mut has = Expression::new(ExpressionKind::Literal(Literal::Boolean(false)), monotype);
        for field in fields.iter().rev() {
            let kind = ExpressionKind::If {
                condition: Box::new(self.label_is(&label, &field.label)),
                then: Box::new(Expression::new(
                    ExpressionKind::Literal(Literal::Boolean(true)),
                    monotype,
                )),
                otherwise: Box::new(has),
            };
            has = Expression::new(kind, monotype);
        }
        self.expression(self.bound(bindings, has))
    }

    /// The fields of a record read through `unsafeGet` or `unsafeHas` when the
    /// label is not a literal and the record's type is a closed record.
    fn dynamic_fields(
        &self,
        arguments: &[Expression],
    ) -> Option<Vec<crate::monotype::RecordField>> {
        let [label, record] = arguments else { return None };
        if let ExpressionKind::Literal(Literal::String(_)) = label.kind {
            return None;
        }
        match self.monotypes.get(record.monotype) {
            Monotype::Record(fields) => Some(fields.to_vec()),
            _ => None,
        }
    }

    fn label_is(&mut self, label: &Expression, expected: &SmolStr) -> Expression {
        let boolean = self.monotypes.intern(Monotype::Boolean);
        let expected = Expression::new(
            ExpressionKind::Literal(Literal::String(expected.to_string())),
            label.monotype,
        );
        let equal = foreign::Operator::Compare(foreign::Comparison::Equal);
        let foreign = Foreign::Operator(equal).interned();
        let arguments = vec![label.clone(), expected];
        Expression::new(ExpressionKind::Foreign { foreign, arguments }, boolean)
    }

    fn bound(&self, bindings: Vec<Binding>, body: Expression) -> Expression {
        if bindings.is_empty() {
            return body;
        }
        let monotype = body.monotype;
        Expression::new(ExpressionKind::Let { bindings, body: Box::new(body) }, monotype)
    }
}
