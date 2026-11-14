//! Let-bound values that are only taken apart. A record whose every use reads
//! a field, or a constructor whose every use is matched, never needs to exist
//! as a whole: its fields become lets of their own, each read becomes the
//! field's local, and each match sees the constructor and resolves.

use smol_str::{SmolStr, format_smolstr};

use super::{Simplifier, column_outcomes, for_each_child, for_each_child_mut, local_expression};
use crate::mono::{
    Alternative, Binding, Expression, ExpressionKind, Guard, Guarded, Local, LocalId,
};

impl Simplifier<'_> {
    /// The body with the binding's value taken apart, when every use of the
    /// binding takes it apart; otherwise the binding and body unchanged.
    pub(super) fn unpack(
        &mut self,
        binding: Binding,
        body: Expression,
    ) -> Result<Expression, (Binding, Expression)> {
        let id = binding.local.id;
        let monotype = binding.local.monotype;
        let unpackable = binding.value.monotype == monotype
            && match &binding.value.kind {
                ExpressionKind::Record(_) => only_taken_apart(&body, id, monotype, None),
                ExpressionKind::Construct { arguments, .. } if !arguments.is_empty() => {
                    only_taken_apart(&body, id, monotype, Some(&binding.value))
                }
                _ => false,
            };
        if !unpackable {
            return Err((binding, body));
        }
        let Binding { local, value } = binding;
        let mut fields = vec![];
        let shape = match value.kind {
            ExpressionKind::Record(values) => {
                let mut labels = vec![];
                for (label, value) in values {
                    let name = format_smolstr!("{}{}", local.name, capitalised(&label));
                    fields.push(self.field_binding(name, value));
                    labels.push(label);
                }
                Shape::Record(labels)
            }
            ExpressionKind::Construct { data, constructor, arguments } => {
                for argument in arguments {
                    fields.push(self.field_binding(local.name.clone(), argument));
                }
                let arguments = fields.iter().map(|field| local_expression(&field.local)).collect();
                let kind = ExpressionKind::Construct { data, constructor, arguments };
                Shape::Construct(Expression::new(kind, value.monotype))
            }
            _ => unreachable!("invariant violated: only records and constructors unpack"),
        };
        let locals: Vec<Local> = fields.iter().map(|field| field.local.clone()).collect();
        let mut body = body;
        take_apart(&mut body, id, &shape, &locals);
        // A read became its field's local; a match resolves only when it is
        // simplified again.
        if let Shape::Construct(_) = shape {
            body = self.expression(body);
        }
        Ok(self.let_bindings(fields, body))
    }

    fn field_binding(&mut self, name: SmolStr, value: Expression) -> Binding {
        let template = Local { id: LocalId(0), name, monotype: value.monotype };
        Binding { local: self.fresh(&template), value }
    }
}

enum Shape {
    Record(Vec<SmolStr>),
    Construct(Expression),
}

/// Whether every occurrence of the local reads a field of it or is matched by
/// a case that the constructor resolves.
fn only_taken_apart(
    expression: &Expression,
    id: LocalId,
    monotype: crate::monotype::MonotypeId,
    construct: Option<&Expression>,
) -> bool {
    let is_whole = |expression: &Expression| {
        matches!(expression.kind, ExpressionKind::Local(found) if found == id)
            && expression.monotype == monotype
    };
    match &expression.kind {
        ExpressionKind::Local(found) => *found != id,
        ExpressionKind::Access { record, .. } if construct.is_none() && is_whole(record) => true,
        ExpressionKind::Case { scrutinees, alternatives } => {
            let mut taken_apart = true;
            for (column, scrutinee) in scrutinees.iter().enumerate() {
                taken_apart &= match construct {
                    Some(construct) if is_whole(scrutinee) => {
                        column_outcomes(construct, alternatives, column).is_some()
                    }
                    _ => only_taken_apart(scrutinee, id, monotype, construct),
                };
            }
            for_each_alternative_child(alternatives, &mut |child| {
                taken_apart = taken_apart && only_taken_apart(child, id, monotype, construct)
            });
            taken_apart
        }
        _ => {
            let mut taken_apart = true;
            for_each_child(expression, &mut |child| {
                taken_apart = taken_apart && only_taken_apart(child, id, monotype, construct)
            });
            taken_apart
        }
    }
}

fn take_apart(expression: &mut Expression, id: LocalId, shape: &Shape, fields: &[Local]) {
    let is_whole = |expression: &Expression| matches!(expression.kind, ExpressionKind::Local(found) if found == id);
    match (&mut expression.kind, shape) {
        (ExpressionKind::Access { record, label }, Shape::Record(labels)) if is_whole(record) => {
            let position = labels
                .iter()
                .position(|field| field == label)
                .expect("invariant violated: a record has the field its type promises");
            let monotype = expression.monotype;
            let mut field = local_expression(&fields[position]);
            if field.monotype != monotype {
                field = Expression::new(ExpressionKind::Coerce(Box::new(field)), monotype);
            }
            *expression = field;
            return;
        }
        (ExpressionKind::Case { scrutinees, .. }, Shape::Construct(construct)) => {
            for scrutinee in scrutinees.iter_mut().filter(|scrutinee| is_whole(scrutinee)) {
                *scrutinee = construct.clone();
            }
        }
        _ => {}
    }
    for_each_child_mut(expression, &mut |child| take_apart(child, id, shape, fields));
}

/// The guards and bodies of a case's alternatives.
fn for_each_alternative_child<'e>(
    alternatives: &'e [Alternative],
    visitor: &mut impl FnMut(&'e Expression),
) {
    for alternative in alternatives {
        match &alternative.body {
            Guarded::Unconditional(body) => visitor(body),
            Guarded::Guards(branches) => {
                for branch in branches {
                    for guard in &branch.guards {
                        match guard {
                            Guard::Boolean(condition) => visitor(condition),
                            Guard::Pattern { value, .. } => visitor(value),
                        }
                    }
                    visitor(&branch.body);
                }
            }
        }
    }
}

fn capitalised(label: &str) -> String {
    let mut characters = label.chars();
    match characters.next() {
        Some(first) => first.to_uppercase().chain(characters).collect(),
        None => String::new(),
    }
}
