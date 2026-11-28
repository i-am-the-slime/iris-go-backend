use smol_str::SmolStr;

use super::super::Representation;
use super::{Rewrite, applied, hash_map, let_in, take};
use crate::emit::local_uses;
use crate::foreign::{Foreign, OBJECT_FROM_ENTRIES, Operator};
use crate::maps::{HashMapOperation, ObjectOperation};
use crate::monomorphic::{Binding, Expression, ExpressionKind, Literal, LocalId};
use crate::monotype::{Monotype, MonotypeId, RecordField};

impl Rewrite<'_> {
    pub(super) fn native_object(&mut self, expression: &mut Expression) {
        let hash = expression.monotype;
        let ExpressionKind::Foreign { foreign, arguments } = &mut expression.kind else { return };
        let Some(operation) = ObjectOperation::of(foreign, arguments) else { return };
        let arguments = std::mem::take(arguments);
        *expression = match operation {
            ObjectOperation::Empty => self.new_table(hash),
            ObjectOperation::Insert => hash_map(HashMapOperation::Insert, arguments, hash),
            ObjectOperation::Remove => hash_map(HashMapOperation::Delete, arguments, hash),
            _ => unreachable!("invariant violated: an object operation that answers no object"),
        };
    }

    pub(super) fn read_object(&mut self, expression: &mut Expression) {
        let monotype = expression.monotype;
        let ExpressionKind::Foreign { foreign, arguments } = &mut expression.kind else { return };
        let Some(operation) = ObjectOperation::of(foreign, arguments) else { return };
        let Some(position) = operation.map_position() else { return };
        let Monotype::HashMap(..) = self.monotypes.get(arguments[position].monotype) else {
            return;
        };
        let hash = arguments[position].monotype;
        let mut arguments = std::mem::take(arguments).into_iter();
        let mut next = || arguments.next().expect("invariant violated: an object's argument");
        *expression = match operation {
            ObjectOperation::Size => hash_map(HashMapOperation::Size, vec![next()], monotype),
            ObjectOperation::IsEmpty => {
                let _predicate = next();
                hash_map(HashMapOperation::IsEmpty, vec![next()], monotype)
            }
            ObjectOperation::Lookup => {
                let (nothing, just, key, table) = (next(), next(), next(), next());
                self.looked_up(nothing, just, key, table, monotype)
            }
            ObjectOperation::LookupST => {
                let (nothing, just, key, table) = (next(), next(), next(), next());
                let result = self.effect_result(monotype);
                let looked_up = self.looked_up(nothing, just, key, table, result);
                performed(looked_up, monotype)
            }
            ObjectOperation::Peek => {
                let (just, nothing, key, table) = (next(), next(), next(), next());
                let result = self.effect_result(monotype);
                let looked_up = self.looked_up(nothing, just, key, table, result);
                performed(looked_up, monotype)
            }
            ObjectOperation::Poke => {
                let arguments = vec![next(), next(), next()];
                let inserted = hash_map(HashMapOperation::Insert, arguments, hash);
                self.performed_write(inserted)
            }
            ObjectOperation::Delete => {
                let deleted = hash_map(HashMapOperation::Delete, vec![next(), next()], hash);
                self.performed_write(deleted)
            }
            ObjectOperation::Empty
            | ObjectOperation::New
            | ObjectOperation::Insert
            | ObjectOperation::Remove => {
                unreachable!("invariant violated: an object operation that reads none")
            }
        };
    }

    pub(super) fn new_in_effect(&mut self, action: &mut Expression, hash: MonotypeId) {
        let ExpressionKind::Foreign { foreign, arguments } = &action.kind else { return };
        if ObjectOperation::of(foreign, arguments) != Some(ObjectOperation::New) {
            return;
        }
        let made = self.new_table(hash);
        *action = self.performed_write(made);
    }

    pub(super) fn object_table(&mut self, table: Expression, object: MonotypeId) -> Expression {
        let Monotype::HashMap(key, value) = *self.monotypes.get(table.monotype) else {
            return table;
        };
        let keys_type = self.monotypes.intern(Monotype::Array(key));
        let values_type = self.monotypes.intern(Monotype::Array(value));
        let fields = vec![
            RecordField { label: SmolStr::new("keys"), monotype: keys_type },
            RecordField { label: SmolStr::new("values"), monotype: values_type },
        ];
        let entries_type = self.monotypes.intern(Monotype::Record(fields.into()));
        let entries = self.fresh("entries", entries_type);
        let sorted = hash_map(HashMapOperation::SortedEntries, vec![table], entries_type);
        let field = |label: &str, monotype: MonotypeId| {
            let record = Box::new(entries.expression());
            Expression::new(ExpressionKind::Access { record, label: SmolStr::new(label) }, monotype)
        };
        let arguments = vec![field("keys", keys_type), field("values", values_type)];
        let foreign = ExpressionKind::Foreign { foreign: &OBJECT_FROM_ENTRIES, arguments };
        let built = Expression::new(foreign, object);
        let_in(vec![Binding { local: entries.clone(), value: sorted }], built)
    }

    pub(super) fn summed(&self, expression: &Expression) -> Option<Expression> {
        let ExpressionKind::EffectBind { action, local, body } = &expression.kind else {
            return None;
        };
        let ExpressionKind::Foreign { foreign, arguments } = &action.kind else { return None };
        if ObjectOperation::of(foreign, arguments) != Some(ObjectOperation::LookupST) {
            return None;
        }
        let [addend, add, key, table] = &arguments[..] else { return None };
        let (ExpressionKind::Local(addend_id), ExpressionKind::Local(key_id)) =
            (&addend.kind, &key.kind)
        else {
            return None;
        };
        let ExpressionKind::Local(table_id) = table.kind else { return None };
        if !self.is_go_map(table_id) || !adds_to(add, *addend_id) {
            return None;
        }
        let poke = match &body.kind {
            ExpressionKind::EffectBind { action, body: rest, .. }
                if local_uses(rest, local.id) == 0 =>
            {
                action
            }
            _ => body,
        };
        let ExpressionKind::Foreign { foreign, arguments } = &poke.kind else { return None };
        if ObjectOperation::of(foreign, arguments) != Some(ObjectOperation::Poke) {
            return None;
        }
        let pokes_sum = is_local(&arguments[0], *key_id)
            && is_local(&arguments[1], local.id)
            && is_local(&arguments[2], table_id);
        pokes_sum.then(|| addend.clone())
    }

    pub(super) fn add_in_place(&mut self, expression: &mut Expression, addend: Expression) {
        let ExpressionKind::EffectBind { body, .. } = &mut expression.kind else { return };
        let mut body = take(body);
        let poke = match &mut body.kind {
            ExpressionKind::EffectBind { action, .. } => action.as_mut(),
            _ => &mut body,
        };
        let ExpressionKind::Foreign { arguments, .. } = &mut poke.kind else { return };
        let [inserted] = &mut arguments[..] else { return };
        let ExpressionKind::Foreign { foreign, arguments } = &mut inserted.kind else { return };
        if **foreign != Foreign::HashMap(HashMapOperation::Insert) {
            return;
        }
        arguments[1] = addend;
        *foreign = Foreign::HashMap(HashMapOperation::Add).interned();
        *expression = body;
    }

    fn is_go_map(&self, local: LocalId) -> bool {
        let Some(slots) = self.decided.locals.get(&local) else { return false };
        slots.len() == 1 && self.decided.representation(slots[0]) == Representation::GoMap
    }

    fn new_table(&mut self, hash: MonotypeId) -> Expression {
        let int = self.monotypes.intern(Monotype::Int);
        let hint = Expression::new(ExpressionKind::Literal(Literal::Int(0)), int);
        hash_map(HashMapOperation::New, vec![hint], hash)
    }

    fn performed_write(&mut self, written: Expression) -> Expression {
        let monotype = self.monotypes.intern(Monotype::Effect(written.monotype));
        performed(written, monotype)
    }

    fn effect_result(&self, monotype: MonotypeId) -> MonotypeId {
        self.monotypes.effect_result(monotype).unwrap_or(monotype)
    }

    fn looked_up(
        &mut self,
        nothing: Expression,
        just: Expression,
        key: Expression,
        table: Expression,
        monotype: MonotypeId,
    ) -> Expression {
        if is_boolean(&nothing, false) && answers_boolean(&just, true) {
            return hash_map(HashMapOperation::Member, vec![key, table], monotype);
        }
        if self.is_maybe(&nothing, &just, monotype) {
            return hash_map(HashMapOperation::Lookup, vec![key, table], monotype);
        }
        let boolean = self.monotypes.intern(Monotype::Boolean);
        let value = self.shapes_value(table.monotype);
        let mut bindings = vec![];
        let key = self.named("key", key, &mut bindings);
        let table = self.named("table", table, &mut bindings);
        let found = hash_map(HashMapOperation::Member, vec![key.clone(), table.clone()], boolean);
        let entry = hash_map(HashMapOperation::Get, vec![key, table], value);
        let choice = ExpressionKind::If {
            condition: Box::new(found),
            then: Box::new(applied(just, vec![entry], monotype)),
            otherwise: Box::new(nothing),
        };
        let_in(bindings, Expression::new(choice, monotype))
    }

    fn is_maybe(&self, nothing: &Expression, just: &Expression, monotype: MonotypeId) -> bool {
        let Monotype::Data(data) = self.monotypes.get(monotype) else { return false };
        let Some(constructors) = self.monotypes.known_constructors(data) else { return false };
        let [absent, present] = &constructors[..] else { return false };
        if absent.name != "Nothing" || present.name != "Just" || present.fields.len() != 1 {
            return false;
        }
        let nothing_made = matches!(
            &nothing.kind,
            ExpressionKind::Construct { data: made, constructor: 0, arguments }
                if made == data && arguments.is_empty()
        );
        let ExpressionKind::Lambda { parameters, body } = &just.kind else { return false };
        let [parameter] = &parameters[..] else { return false };
        let just_made = matches!(
            &body.kind,
            ExpressionKind::Construct { data: made, constructor: 1, arguments }
                if made == data
                    && matches!(&arguments[..], [argument]
                        if matches!(argument.kind, ExpressionKind::Local(id) if id == parameter.id))
        );
        nothing_made && just_made
    }
}

fn performed(value: Expression, monotype: MonotypeId) -> Expression {
    let foreign = Foreign::EffectPure.interned();
    Expression::new(ExpressionKind::Foreign { foreign, arguments: vec![value] }, monotype)
}

fn is_boolean(expression: &Expression, value: bool) -> bool {
    let ExpressionKind::Literal(Literal::Boolean(literal)) = expression.kind else { return false };
    literal == value
}

fn answers_boolean(function: &Expression, value: bool) -> bool {
    let ExpressionKind::Lambda { parameters, body } = &function.kind else { return false };
    parameters.len() == 1 && is_boolean(body, value)
}

fn adds_to(function: &Expression, addend: LocalId) -> bool {
    let ExpressionKind::Lambda { parameters, body } = &function.kind else { return false };
    let [entry] = &parameters[..] else { return false };
    let ExpressionKind::Foreign { foreign: Foreign::Operator(Operator::IntAdd), arguments } =
        &body.kind
    else {
        return false;
    };
    match &arguments[..] {
        [left, right] => {
            (is_local(left, addend) && is_local(right, entry.id))
                || (is_local(left, entry.id) && is_local(right, addend))
        }
        _ => false,
    }
}

fn is_local(expression: &Expression, id: LocalId) -> bool {
    matches!(expression.kind, ExpressionKind::Local(local) if local == id)
}
