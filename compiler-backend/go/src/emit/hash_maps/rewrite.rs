//! The program once its Go maps are chosen: every value of a web that is a Go map has the Go map
//! type, its map operations are the Go map's, and a version that goes where a tree is wanted is
//! converted there ([`conversions`]).
//!
//! `insertWith`, `alter` and `update` become the lookups and writes that do them, with the
//! function they apply bound to what it is given.

use rustc_hash::{FxHashMap, FxHashSet};
use smol_str::SmolStr;

use super::{Decided, MapShape, is_fold_left};
use crate::foreign::{Foreign, Operator};
use crate::maps::{HashMapOperation, MapOperation};
use crate::monomorphic::traversal::{for_each_child_mut, visit};
use crate::monomorphic::{
    Alternative, Binding, Expression, ExpressionKind, Function, FunctionId, Guarded, Literal,
    Local, LocalId, Pattern, PatternKind, Program,
};
use crate::monotype::{DataType, Monotype, MonotypeId, Monotypes};

mod conversions;

/// The conversions between a Go map and the tree for one map type.
#[derive(Clone, Copy)]
struct Conversions {
    to_tree: FunctionId,
    from_tree: FunctionId,
}

pub(super) struct Rewrite<'r> {
    program: &'r mut Program,
    monotypes: &'r mut Monotypes,
    operations: &'r FxHashMap<FunctionId, MapOperation>,
    shapes: &'r FxHashMap<MonotypeId, MapShape>,
    decided: Decided,
    next_local: u32,
    conversions: FxHashMap<MonotypeId, Conversions>,
    origin: Option<files::FileId>,
}

impl<'r> Rewrite<'r> {
    pub(super) fn new(
        program: &'r mut Program,
        monotypes: &'r mut Monotypes,
        operations: &'r FxHashMap<FunctionId, MapOperation>,
        shapes: &'r FxHashMap<MonotypeId, MapShape>,
        decided: Decided,
    ) -> Rewrite<'r> {
        let next_local = crate::emit::reuse::first_unused_local(program);
        let origin = operations.keys().next().and_then(|&id| program.function(id).origin);
        Rewrite {
            program,
            monotypes,
            operations,
            shapes,
            decided,
            next_local,
            conversions: FxHashMap::default(),
            origin,
        }
    }

    fn hash_type(&mut self, tree: MonotypeId) -> MonotypeId {
        let shape = self.shapes[&tree];
        self.monotypes.intern(Monotype::HashMap(shape.key, shape.value))
    }

    fn unit(&mut self) -> MonotypeId {
        self.monotypes.intern(Monotype::Unit)
    }

    pub(super) fn rewrite(mut self) {
        let mut retyped = FxHashSet::default();
        let original = self.program.functions.len();
        for index in 0..original {
            let id = FunctionId(index as u32);
            if self.operations.contains_key(&id) {
                continue;
            }
            let unit = self.unit();
            // The analysis knows the body by where it stood, and the function moves out to be
            // rewritten.
            let body = std::ptr::from_ref(&self.program.functions[index].body);
            let mut function =
                std::mem::replace(&mut self.program.functions[index], placeholder_function(unit));
            for parameter in &mut function.parameters {
                if self.is_native_local(parameter.id) {
                    parameter.monotype = self.hash_type(parameter.monotype);
                    retyped.insert(id);
                }
            }
            if self.decided.results.get(&id).is_some_and(|&node| self.decided.is_native(node)) {
                function.result = self.hash_type(function.result);
                retyped.insert(id);
            }
            self.expression_at(&mut function.body, body);
            self.program.functions[index] = function;
        }
        retyped
            .extend((original..self.program.functions.len()).map(|index| FunctionId(index as u32)));
        let types: FxHashMap<FunctionId, MonotypeId> = retyped
            .iter()
            .map(|&id| {
                let function = self.program.function(id);
                let parameters: Vec<MonotypeId> =
                    function.parameters.iter().map(|parameter| parameter.monotype).collect();
                let result = function.result;
                (id, self.function_type(&parameters, result))
            })
            .collect();
        for function in &mut self.program.functions {
            retype_references(&mut function.body, &types);
        }
    }

    fn function_type(&mut self, parameters: &[MonotypeId], result: MonotypeId) -> MonotypeId {
        parameters
            .iter()
            .rev()
            .fold(result, |result, &parameter| self.monotypes.function(parameter, result))
    }

    fn is_native_local(&self, id: LocalId) -> bool {
        self.decided.locals.get(&id).is_some_and(|&node| self.decided.is_native(node))
    }

    fn expression(&mut self, expression: &mut Expression) {
        let at = std::ptr::from_ref(expression);
        self.expression_at(expression, at);
    }

    /// The expression that the analysis saw at `at`.
    fn expression_at(&mut self, expression: &mut Expression, at: *const Expression) {
        let native =
            self.decided.expressions.get(&at).is_some_and(|&node| self.decided.is_native(node));
        let to_tree = self.decided.to_tree.contains(&at);
        let from_tree = self.decided.from_tree.contains(&at);
        for_each_child_mut(expression, &mut |child| self.expression(child));
        self.retype_binders(expression);
        if native {
            let tree = expression.monotype;
            self.native(expression);
            self.size_hint(expression);
            if to_tree {
                let conversions = self.conversions(tree);
                *expression = call(conversions.to_tree, vec![take(expression)], tree);
            }
        } else if from_tree {
            let tree = expression.monotype;
            let conversions = self.conversions(tree);
            let hash = self.hash_type(tree);
            *expression = call(conversions.from_tree, vec![take(expression)], hash);
        } else if to_tree {
            // A call of a function that answers a Go map, where a tree is wanted.
            let tree = expression.monotype;
            expression.monotype = self.hash_type(tree);
            let conversions = self.conversions(tree);
            *expression = call(conversions.to_tree, vec![take(expression)], tree);
        } else {
            self.read(expression);
        }
    }

    /// A fold over an array that only inserts into a Go map it starts empty: the map is made
    /// for as many entries as the array has.
    fn size_hint(&mut self, expression: &mut Expression) {
        let int = self.monotypes.intern(Monotype::Int);
        let ExpressionKind::Foreign { foreign, arguments } = &mut expression.kind else { return };
        if !is_fold_left(foreign, arguments) {
            return;
        }
        let [callback, seed, array] = arguments.as_mut_slice() else { return };
        if !matches!(array.kind, ExpressionKind::Local(_)) {
            return;
        }
        let ExpressionKind::Foreign {
            foreign: Foreign::HashMap(HashMapOperation::New),
            arguments: hint,
        } = &mut seed.kind
        else {
            return;
        };
        if !matches!(hint[0].kind, ExpressionKind::Literal(Literal::Int(0))) {
            return;
        }
        let ExpressionKind::Lambda { body, .. } = &callback.kind else { return };
        let mut only_inserts = true;
        visit(body, &mut |node| {
            if let ExpressionKind::Foreign { foreign: Foreign::HashMap(operation), .. } = &node.kind
            {
                only_inserts &= *operation == HashMapOperation::Insert;
            }
        });
        if only_inserts {
            let length = Foreign::Operator(Operator::ArrayLength).interned();
            let arguments = vec![array.clone()];
            hint[0] = Expression::new(ExpressionKind::Foreign { foreign: length, arguments }, int);
        }
    }

    /// A lookup, membership test or size of a Go map, as the Go map operation.
    fn read(&mut self, expression: &mut Expression) {
        let ExpressionKind::Apply { function, arguments } = &mut expression.kind else { return };
        let ExpressionKind::Function(id) = function.kind else { return };
        let Some(&operation) = self.operations.get(&id) else { return };
        if !operation.reads() || operation.arity() != arguments.len() {
            return;
        }
        let Some(position) = operation.map_position() else { return };
        if !matches!(self.monotypes.get(arguments[position].monotype), Monotype::HashMap(..)) {
            return;
        }
        let read = match operation {
            MapOperation::Lookup => HashMapOperation::Lookup,
            MapOperation::Member => HashMapOperation::Member,
            MapOperation::Size => HashMapOperation::Size,
            MapOperation::IsEmpty => HashMapOperation::IsEmpty,
            _ => unreachable!("invariant violated: a map read that builds"),
        };
        let arguments = std::mem::take(arguments);
        *expression = hash_map(read, arguments, expression.monotype);
    }

    /// The locals a native map is bound to by a `let` or a fold's callback, and the callback's
    /// type.
    fn retype_binders(&mut self, expression: &mut Expression) {
        match &mut expression.kind {
            ExpressionKind::Let { bindings, .. } => {
                for binding in bindings {
                    if self.is_native_local(binding.local.id) {
                        binding.local.monotype = self.hash_type(binding.local.monotype);
                    }
                }
            }
            ExpressionKind::Lambda { parameters, body } => {
                let mut changed =
                    matches!(self.monotypes.get(body.monotype), Monotype::HashMap(..));
                for parameter in parameters.iter_mut() {
                    if self.is_native_local(parameter.id) {
                        parameter.monotype = self.hash_type(parameter.monotype);
                        changed = true;
                    }
                }
                if changed {
                    let parameters: Vec<MonotypeId> =
                        parameters.iter().map(|parameter| parameter.monotype).collect();
                    let result = body.monotype;
                    expression.monotype = self.function_type(&parameters, result);
                }
            }
            _ => {}
        }
    }

    /// A map-typed expression of a web that is a Go map: its type, and the operation it is.
    fn native(&mut self, expression: &mut Expression) {
        let tree = expression.monotype;
        let hash = self.hash_type(tree);
        expression.monotype = hash;
        let operation = match &expression.kind {
            ExpressionKind::Apply { function, arguments } => match function.kind {
                ExpressionKind::Function(id) => self
                    .operations
                    .get(&id)
                    .copied()
                    .filter(|operation| operation.arity() == arguments.len()),
                _ => None,
            },
            ExpressionKind::Function(id) => self.operations.get(&id).copied(),
            _ => None,
        };
        let Some(operation) = operation else { return };
        let arguments = match &mut expression.kind {
            ExpressionKind::Apply { arguments, .. } => std::mem::take(arguments),
            _ => vec![],
        };
        *expression = self.operation(operation, arguments, hash);
    }

    /// A map operation of a Go map, as the Go map operations that do it.
    fn operation(
        &mut self,
        operation: MapOperation,
        arguments: Vec<Expression>,
        hash: MonotypeId,
    ) -> Expression {
        let int = self.monotypes.intern(Monotype::Int);
        let mut arguments = arguments.into_iter();
        let mut next = || arguments.next().expect("invariant violated: a map operation's argument");
        match operation {
            MapOperation::Empty => {
                let hint = Expression::new(ExpressionKind::Literal(Literal::Int(0)), int);
                hash_map(HashMapOperation::New, vec![hint], hash)
            }
            MapOperation::Singleton => {
                let (key, value) = (next(), next());
                hash_map(HashMapOperation::Singleton, vec![key, value], hash)
            }
            MapOperation::Insert => {
                let (key, value, table) = (next(), next(), next());
                hash_map(HashMapOperation::Insert, vec![key, value, table], hash)
            }
            MapOperation::Delete => {
                let (key, table) = (next(), next());
                hash_map(HashMapOperation::Delete, vec![key, table], hash)
            }
            MapOperation::InsertWith => {
                let (combine, key, value, table) = (next(), next(), next(), next());
                self.insert_with(combine, key, value, table, hash)
            }
            MapOperation::Alter => {
                let (change, key, table) = (next(), next(), next());
                self.alter(change, key, table, hash)
            }
            MapOperation::Update => {
                let (change, key, table) = (next(), next(), next());
                self.update(change, key, table, hash)
            }
            MapOperation::Difference => {
                let (table, other) = (next(), next());
                hash_map(HashMapOperation::Difference, vec![table, other], hash)
            }
            MapOperation::Lookup
            | MapOperation::Member
            | MapOperation::Size
            | MapOperation::IsEmpty => {
                unreachable!("invariant violated: a map read answers a map")
            }
        }
    }

    fn fresh(&mut self, name: &str, monotype: MonotypeId) -> Local {
        Local::fresh(&mut self.next_local, SmolStr::new(name), monotype)
    }

    /// `insertWith f k v m`: `f old v` under `k` when `m` holds `old` there, `v` otherwise.
    fn insert_with(
        &mut self,
        combine: Expression,
        key: Expression,
        value: Expression,
        table: Expression,
        hash: MonotypeId,
    ) -> Expression {
        let boolean = self.monotypes.intern(Monotype::Boolean);
        let mut bindings = vec![];
        let key = self.named("key", key, &mut bindings);
        let value = self.named("value", value, &mut bindings);
        let table = self.named("table", table, &mut bindings);
        let found = hash_map(HashMapOperation::Member, vec![key.clone(), table.clone()], boolean);
        let old = hash_map(HashMapOperation::Get, vec![key.clone(), table.clone()], value.monotype);
        let combined = applied(combine, vec![old, value.clone()], value.monotype);
        let monotype = value.monotype;
        let choice = ExpressionKind::If {
            condition: Box::new(found),
            then: Box::new(combined),
            otherwise: Box::new(value),
        };
        let stored = Expression::new(choice, monotype);
        let inserted = hash_map(HashMapOperation::Insert, vec![key, stored, table], hash);
        let_in(bindings, inserted)
    }

    /// The expression itself when it is a local or a literal, otherwise a local bound to it.
    fn named(
        &mut self,
        name: &str,
        expression: Expression,
        bindings: &mut Vec<Binding>,
    ) -> Expression {
        if matches!(expression.kind, ExpressionKind::Local(_) | ExpressionKind::Literal(_)) {
            return expression;
        }
        let local = self.fresh(name, expression.monotype);
        let reference = local.expression();
        bindings.push(Binding { local, value: expression });
        reference
    }

    /// `alter f k m`: what `f` makes of the entry under `k`, which deletes it when nothing.
    fn alter(
        &mut self,
        change: Expression,
        key: Expression,
        table: Expression,
        hash: MonotypeId,
    ) -> Expression {
        let Some((maybe, _)) = self.monotypes.function_parts(change.monotype) else {
            unreachable!("invariant violated: alter's change is no function")
        };
        let mut bindings = vec![];
        let key = self.named("key", key, &mut bindings);
        let table = self.named("table", table, &mut bindings);
        let current = hash_map(HashMapOperation::Lookup, vec![key.clone(), table.clone()], maybe);
        let changed = applied(change, vec![current], maybe);
        let stored = self.stored(changed, key, table, hash);
        let_in(bindings, stored)
    }

    /// `update f k m`: `m` without an entry under `k`, otherwise what `f` makes of it.
    fn update(
        &mut self,
        change: Expression,
        key: Expression,
        table: Expression,
        hash: MonotypeId,
    ) -> Expression {
        let Some((value_type, maybe)) = self.monotypes.function_parts(change.monotype) else {
            unreachable!("invariant violated: update's change is no function")
        };
        let Monotype::Data(data) = self.monotypes.get(maybe).clone() else {
            unreachable!("invariant violated: update's change answers no Maybe")
        };
        let mut bindings = vec![];
        let key_ref = self.named("key", key, &mut bindings);
        let table_ref = self.named("table", table, &mut bindings);
        let old = self.fresh("old", value_type);
        let current =
            hash_map(HashMapOperation::Lookup, vec![key_ref.clone(), table_ref.clone()], maybe);
        let changed = applied(change, vec![old.expression()], maybe);
        let stored = self.stored(changed, key_ref, table_ref.clone(), hash);
        let alternatives = vec![
            alternative(constructor(&data, 0, vec![], maybe), table_ref),
            alternative(constructor(&data, 1, vec![variable(&old)], maybe), stored),
        ];
        let case = ExpressionKind::Case { scrutinees: vec![current], alternatives };
        let_in(bindings, Expression::new(case, hash))
    }

    /// Writes a `Maybe` under a key: deletes the key at nothing.
    fn stored(
        &mut self,
        maybe_value: Expression,
        key: Expression,
        table: Expression,
        hash: MonotypeId,
    ) -> Expression {
        let maybe = maybe_value.monotype;
        let Monotype::Data(data) = self.monotypes.get(maybe).clone() else {
            unreachable!("invariant violated: a stored value is no Maybe")
        };
        let value_type = self.shapes_value(hash);
        let new = self.fresh("new", value_type);
        let deleted = hash_map(HashMapOperation::Delete, vec![key.clone(), table.clone()], hash);
        let inserted = hash_map(HashMapOperation::Insert, vec![key, new.expression(), table], hash);
        let alternatives = vec![
            alternative(constructor(&data, 0, vec![], maybe), deleted),
            alternative(constructor(&data, 1, vec![variable(&new)], maybe), inserted),
        ];
        Expression::new(ExpressionKind::Case { scrutinees: vec![maybe_value], alternatives }, hash)
    }

    fn shapes_value(&self, hash: MonotypeId) -> MonotypeId {
        match self.monotypes.get(hash) {
            Monotype::HashMap(_, value) => *value,
            _ => unreachable!("invariant violated: no Go map type"),
        }
    }
}

fn placeholder_function(unit: MonotypeId) -> Function {
    Function {
        name: SmolStr::new_static(""),
        origin: None,
        parameters: vec![],
        result: unit,
        body: Expression::new(ExpressionKind::Unit, unit),
        position: None,
    }
}

fn take(expression: &mut Expression) -> Expression {
    let monotype = expression.monotype;
    std::mem::replace(expression, Expression::new(ExpressionKind::Unit, monotype))
}

fn call(function: FunctionId, arguments: Vec<Expression>, result: MonotypeId) -> Expression {
    // The callee's type is set once every function's type is known.
    let callee = Expression::new(ExpressionKind::Function(function), result);
    Expression::new(ExpressionKind::Apply { function: Box::new(callee), arguments }, result)
}

fn hash_map(
    operation: HashMapOperation,
    arguments: Vec<Expression>,
    monotype: MonotypeId,
) -> Expression {
    let foreign = Foreign::HashMap(operation).interned();
    Expression::new(ExpressionKind::Foreign { foreign, arguments }, monotype)
}

/// `f a b`, as `f`'s body with its parameters bound when `f` is a lambda.
fn applied(function: Expression, arguments: Vec<Expression>, monotype: MonotypeId) -> Expression {
    match function.kind {
        ExpressionKind::Lambda { parameters, body } if parameters.len() == arguments.len() => {
            let bindings = parameters
                .into_iter()
                .zip(arguments)
                .map(|(local, value)| Binding { local, value })
                .collect();
            Expression::new(ExpressionKind::Let { bindings, body }, monotype)
        }
        kind => {
            let function = Expression { kind, ..function };
            Expression::new(
                ExpressionKind::Apply { function: Box::new(function), arguments },
                monotype,
            )
        }
    }
}

fn variable(local: &Local) -> Pattern {
    Pattern { kind: PatternKind::Variable(local.clone()), monotype: local.monotype }
}

fn constructor(
    data: &DataType,
    constructor: usize,
    arguments: Vec<Pattern>,
    monotype: MonotypeId,
) -> Pattern {
    Pattern {
        kind: PatternKind::Constructor { data: data.clone(), constructor, arguments },
        monotype,
    }
}

fn alternative(pattern: Pattern, body: Expression) -> Alternative {
    Alternative { patterns: vec![pattern], body: Guarded::Unconditional(body), position: None }
}

/// Gives every reference to a function whose type changed its new type.
fn retype_references(expression: &mut Expression, types: &FxHashMap<FunctionId, MonotypeId>) {
    if let ExpressionKind::Function(id) = expression.kind
        && let Some(&monotype) = types.get(&id)
    {
        expression.monotype = monotype;
    }
    for_each_child_mut(expression, &mut |child| retype_references(child, types));
}

fn let_in(bindings: Vec<Binding>, body: Expression) -> Expression {
    if bindings.is_empty() {
        return body;
    }
    let monotype = body.monotype;
    Expression::new(ExpressionKind::Let { bindings, body: Box::new(body) }, monotype)
}
