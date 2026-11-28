//! The program once its Go maps are chosen: every value of a web that is a Go map has the Go map
//! type, its map operations are the Go map's, and a version that goes where a tree is wanted is
//! converted there ([`conversions`]).
//!
//! `insertWith`, `alter` and `update` become the lookups and writes that do them, with the
//! function they apply bound to what it is given.

use rustc_hash::{FxHashMap, FxHashSet};
use smol_str::SmolStr;

use super::{
    Conversion, Decided, Layouts, MapShape, PRODUCT_LABELS, Representation, fields_of, is_fold_left,
};
use crate::foreign::{Foreign, Iteration, Operator};
use crate::maps::{HashMapOperation, MapOperation};
use crate::monomorphic::traversal::{for_each_child_mut, visit};
use crate::monomorphic::{
    Alternative, Binding, Expression, ExpressionKind, Function, FunctionId, Guarded, Literal,
    Local, LocalId, Pattern, PatternKind, Program,
};
use crate::monotype::{DataType, Monotype, MonotypeId, Monotypes, RecordField};

mod conversions;
mod objects;

/// The conversions between a Go map, or a map kept in order, and the tree for one map type.
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
    conversions: FxHashMap<(MonotypeId, Representation), Conversions>,
    /// The function that builds the tree of a map type from its sorted entries.
    builders: FxHashMap<MonotypeId, FunctionId>,
    layouts: Layouts,
    retyped: FxHashMap<(MonotypeId, Vec<Representation>), MonotypeId>,
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
        let tree_operation = operations.iter().find(|&(_, operation)| !operation.reads_objects());
        let origin = tree_operation.and_then(|(&id, _)| program.function(id).origin);
        Rewrite {
            program,
            monotypes,
            operations,
            shapes,
            decided,
            next_local,
            conversions: FxHashMap::default(),
            builders: FxHashMap::default(),
            layouts: Layouts::default(),
            retyped: FxHashMap::default(),
            origin,
        }
    }

    /// The type of a map of the tree type in a native representation.
    fn native_type(&mut self, tree: MonotypeId, representation: Representation) -> MonotypeId {
        let shape = self.shapes[&tree];
        match representation {
            Representation::GoMap => {
                self.monotypes.intern(Monotype::HashMap(shape.key, shape.value))
            }
            Representation::Ordered => {
                self.monotypes.intern(Monotype::OrderedMap(shape.key, shape.value))
            }
            Representation::Tree => tree,
        }
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
            let placeholder = placeholder_function(unit);
            let mut function = std::mem::replace(&mut self.program.functions[index], placeholder);
            for parameter in &mut function.parameters {
                let monotype = self.local_type(parameter.id, parameter.monotype);
                if monotype != parameter.monotype {
                    parameter.monotype = monotype;
                    retyped.insert(id);
                }
            }
            if let Some(slots) = self.decided.results.get(&id) {
                let representations = self.decided.representations(slots);
                let monotype = self.retype(function.result, &representations);
                if monotype != function.result {
                    function.result = monotype;
                    retyped.insert(id);
                }
            }
            self.expression_at(&mut function.body, body);
            self.program.functions[index] = function;
        }
        retyped
            .extend((original..self.program.functions.len()).map(|index| FunctionId(index as u32)));
        let types = retyped.iter().map(|&id| {
            let function = self.program.function(id);
            let parameters = function.parameters.iter().map(|parameter| parameter.monotype);
            let parameters: Vec<MonotypeId> = parameters.collect();
            let result = function.result;
            (id, self.function_type(&parameters, result))
        });
        let types: FxHashMap<FunctionId, MonotypeId> = types.collect();
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

    /// The type of a local, with the native maps its slots are.
    fn local_type(&mut self, id: LocalId, monotype: MonotypeId) -> MonotypeId {
        let Some(slots) = self.decided.locals.get(&id) else { return monotype };
        let representations = self.decided.representations(slots);
        self.retype(monotype, &representations)
    }

    /// The type of values whose slots are in the representations given.
    fn retype(&mut self, monotype: MonotypeId, representations: &[Representation]) -> MonotypeId {
        if !representations.iter().any(|slot| slot.is_native()) {
            return monotype;
        }
        let key = (monotype, representations.to_vec());
        if let Some(&retyped) = self.retyped.get(&key) {
            return retyped;
        }
        let retyped = if self.shapes.contains_key(&monotype) {
            self.native_type(monotype, representations[0])
        } else {
            let layout = self.layouts.layout(self.monotypes, self.shapes, monotype);
            let Some(fields) = fields_of(self.monotypes, monotype) else {
                unreachable!("invariant violated: slots of neither a map nor a record")
            };
            let fields = fields.iter().map(|field| match layout.field(&field.label) {
                Some(slots) => {
                    let range = slots.start..slots.start + slots.width;
                    let monotype = self.retype(field.monotype, &representations[range]);
                    RecordField { label: field.label.clone(), monotype }
                }
                None => field.clone(),
            });
            let fields: Vec<RecordField> = fields.collect();
            let record = self.monotypes.intern(Monotype::Record(fields.into()));
            if let Some(spellings) = self.monotypes.record_spellings.get(&monotype).cloned() {
                self.monotypes.record_spellings.entry(record).or_insert(spellings);
            }
            record
        };
        self.retyped.insert(key, retyped);
        retyped
    }

    fn expression(&mut self, expression: &mut Expression) {
        let at = std::ptr::from_ref(expression);
        self.expression_at(expression, at);
    }

    /// The expression that the analysis saw at `at`.
    fn expression_at(&mut self, expression: &mut Expression, at: *const Expression) {
        let slots = self.decided.expressions.get(&at);
        let own = slots.map(|slots| self.decided.representations(slots));
        let conversion = self.decided.conversions.remove(&at);
        let scrutinee_types: Vec<MonotypeId> = match &expression.kind {
            ExpressionKind::Case { scrutinees, .. } => {
                scrutinees.iter().map(|scrutinee| scrutinee.monotype).collect()
            }
            _ => vec![],
        };
        let addend = self.summed(expression);
        for_each_child_mut(expression, &mut |child| self.expression(child));
        self.retype_binders(expression, &scrutinee_types);
        if let Some(addend) = addend {
            self.add_in_place(expression, addend);
        }
        let Some(own) = own else {
            self.read(expression);
            self.retype_effect(expression);
            return;
        };
        let natives = conversion.as_ref().map_or(own, |conversion| conversion.from.clone());
        let tree = expression.monotype;
        expression.monotype = self.retype(tree, &natives);
        if expression.monotype != tree {
            as_record(expression);
        }
        if self.shapes.contains_key(&tree) && natives[0].is_native() {
            self.native(expression);
            self.size_hint(expression);
        } else {
            self.read(expression);
        }
        match conversion {
            Some(Conversion { from, to }) => {
                *expression = self.convert(take(expression), tree, &from, &to);
            }
            None if self.decided.copies.contains(&at) => {
                *expression = self.copied(take(expression), tree, &natives);
            }
            None => {}
        }
    }

    /// A copy of a value whose maps a fold starts from, which the fold may then change in
    /// place: a Go map's `maps.Clone`, and every other value through the tree.
    fn copied(
        &mut self,
        value: Expression,
        tree: MonotypeId,
        representations: &[Representation],
    ) -> Expression {
        if !representations.iter().any(|slot| slot.is_native()) {
            return value;
        }
        if self.shapes.contains_key(&tree) && representations[0] == Representation::GoMap {
            let monotype = value.monotype;
            return hash_map(HashMapOperation::Copy, vec![value], monotype);
        }
        let trees = vec![Representation::Tree; representations.len()];
        let converted = self.convert(value, tree, representations, &trees);
        self.convert(converted, tree, &trees, representations)
    }

    /// A value of type `tree` whose slots are in the representations `from`, as one whose slots
    /// are in those of `to`: each map that changes is converted, through the tree between two
    /// native representations, and a record rebuilt of its fields.
    fn convert(
        &mut self,
        value: Expression,
        tree: MonotypeId,
        from: &[Representation],
        to: &[Representation],
    ) -> Expression {
        if from == to {
            return value;
        }
        let target = self.retype(tree, to);
        if self.shapes.contains_key(&tree) {
            let value = match from[0] {
                Representation::Tree => value,
                native => call(self.conversions(tree, native).to_tree, vec![value], tree),
            };
            return match to[0] {
                Representation::Tree => value,
                native => call(self.conversions(tree, native).from_tree, vec![value], target),
            };
        }
        if let Monotype::Data(data) = self.monotypes.get(tree).clone() {
            return self.convert_product(value, tree, &data, from, to);
        }
        let mut bindings = vec![];
        let record = self.named("record", value, &mut bindings);
        let layout = self.layouts.layout(self.monotypes, self.shapes, tree);
        let Monotype::Record(fields) = self.monotypes.get(tree).clone() else {
            unreachable!("invariant violated: slots of neither a map nor a record")
        };
        let mut built = vec![];
        for field in fields.iter() {
            let field_slots = layout.field(&field.label);
            let slots = field_slots.map(|slots| slots.start..slots.start + slots.width);
            let (from, to) = match slots {
                Some(range) => (&from[range.clone()], &to[range]),
                None => (&[][..], &[][..]),
            };
            let monotype = self.retype(field.monotype, from);
            let label = field.label.clone();
            let access = ExpressionKind::Access { record: Box::new(record.clone()), label };
            let read = Expression::new(access, monotype);
            let converted = self.convert(read, field.monotype, from, to);
            built.push((field.label.clone(), converted));
        }
        let rebuilt = Expression::new(ExpressionKind::Record(built), target);
        let_in(bindings, rebuilt)
    }

    /// A product converted: its fields read off the record it is where it holds Go maps, or
    /// bound by a pattern on it where it is the data type, each converted, and built into the
    /// record or the construction that `to` makes of it. A product built where it is converted
    /// converts its fields where they are.
    fn convert_product(
        &mut self,
        value: Expression,
        tree: MonotypeId,
        data: &DataType,
        from: &[Representation],
        to: &[Representation],
    ) -> Expression {
        let target = self.retype(tree, to);
        let layout = self.layouts.layout(self.monotypes, self.shapes, tree);
        let Some(fields) = fields_of(self.monotypes, tree) else {
            unreachable!("invariant violated: a converted product is none")
        };
        let slots = |label: &str| {
            layout.field(label).map_or(0..0, |field| field.start..field.start + field.width)
        };
        let convert_parts = |rewrite: &mut Rewrite<'r>, parts: Vec<Expression>| {
            let converted = parts.into_iter().zip(fields.iter()).map(|(part, field)| {
                let range = slots(&field.label);
                rewrite.convert(part, field.monotype, &from[range.clone()], &to[range])
            });
            converted.collect::<Vec<Expression>>()
        };
        let build = |parts: Vec<Expression>| {
            if to.iter().any(|native| native.is_native()) {
                let labelled = fields.iter().map(|field| field.label.clone()).zip(parts);
                Expression::new(ExpressionKind::Record(labelled.collect()), target)
            } else {
                let data = data.clone();
                let kind = ExpressionKind::Construct { data, constructor: 0, arguments: parts };
                Expression::new(kind, target)
            }
        };
        match value.kind {
            ExpressionKind::Record(built) => {
                let parts = built.into_iter().map(|(_, value)| value).collect();
                build(convert_parts(self, parts))
            }
            ExpressionKind::Construct { arguments, .. } => build(convert_parts(self, arguments)),
            kind if from.iter().any(|native| native.is_native()) => {
                let mut bindings = vec![];
                let value = Expression { kind, ..value };
                let record = self.named("record", value, &mut bindings);
                let parts = fields.iter().map(|field| {
                    let monotype = self.retype(field.monotype, &from[slots(&field.label)]);
                    let label = field.label.clone();
                    let record = Box::new(record.clone());
                    Expression::new(ExpressionKind::Access { record, label }, monotype)
                });
                let parts = parts.collect();
                let_in(bindings, build(convert_parts(self, parts)))
            }
            kind => {
                let value = Expression { kind, ..value };
                let locals = fields.iter().map(|field| self.fresh("field", field.monotype));
                let locals: Vec<Local> = locals.collect();
                let parts = locals.iter().map(Local::expression).collect();
                let built = build(convert_parts(self, parts));
                let pattern = constructor(data, 0, locals.iter().map(variable).collect(), tree);
                let alternatives = vec![alternative(pattern, built)];
                let case = ExpressionKind::Case { scrutinees: vec![value], alternatives };
                Expression::new(case, target)
            }
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
        let Some(array) = as_long_as(array) else { return };
        let array = array.clone();
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
            let arguments = vec![array];
            hint[0] = Expression::new(ExpressionKind::Foreign { foreign: length, arguments }, int);
        }
    }

    /// A lookup, membership test or size of a Go map, as the Go map operation.
    fn read(&mut self, expression: &mut Expression) {
        if let ExpressionKind::Foreign { .. } = expression.kind {
            self.read_object(expression);
            return;
        }
        let ExpressionKind::Apply { function, arguments } = &mut expression.kind else { return };
        let ExpressionKind::Function(id) = function.kind else { return };
        let Some(&operation) = self.operations.get(&id) else { return };
        if !operation.reads() || operation.arity() != arguments.len() {
            return;
        }
        let Some(position) = operation.map_position() else { return };
        if !matches!(
            self.monotypes.get(arguments[position].monotype),
            Monotype::HashMap(..) | Monotype::OrderedMap(..)
        ) {
            return;
        }
        let read = match operation {
            MapOperation::Lookup => HashMapOperation::Lookup,
            MapOperation::Member => HashMapOperation::Member,
            MapOperation::Size => HashMapOperation::Size,
            MapOperation::IsEmpty => HashMapOperation::IsEmpty,
            MapOperation::FindMin => HashMapOperation::Min,
            MapOperation::FindMax => HashMapOperation::Max,
            MapOperation::LookupLE => HashMapOperation::AtMost,
            MapOperation::LookupLT => HashMapOperation::Below,
            MapOperation::LookupGE => HashMapOperation::AtLeast,
            MapOperation::LookupGT => HashMapOperation::Above,
            MapOperation::AscendingEntries => {
                let object = self.program.function(id).parameters[0].monotype;
                let table = take(&mut arguments[0]);
                arguments[0] = self.object_table(table, object);
                return;
            }
            _ => unreachable!("invariant violated: a map read that builds"),
        };
        let arguments = std::mem::take(arguments);
        *expression = hash_map(read, arguments, expression.monotype);
    }

    /// The locals a native map is bound to by a `let`, a fold's callback or a pattern on a
    /// record whose type changed from `scrutinee_types`.
    fn retype_binders(&mut self, expression: &mut Expression, scrutinee_types: &[MonotypeId]) {
        match &mut expression.kind {
            ExpressionKind::Let { bindings, .. } => {
                for binding in bindings {
                    let local = &mut binding.local;
                    local.monotype = self.local_type(local.id, local.monotype);
                }
            }
            ExpressionKind::EffectBind { action, local, .. } => {
                let original = local.monotype;
                local.monotype = self.local_type(local.id, original);
                if local.monotype != original {
                    // The foreign that hands the maps back answers them as they are.
                    action.monotype = match self.monotypes.effect_result(action.monotype) {
                        Some(_) => self.monotypes.intern(Monotype::Effect(local.monotype)),
                        None => local.monotype,
                    };
                    self.new_in_effect(action, local.monotype);
                }
            }
            ExpressionKind::Lambda { parameters, body } => {
                let original = self.results_after(expression.monotype, parameters.len());
                let mut changed = body.monotype != original;
                for parameter in parameters.iter_mut() {
                    let monotype = self.local_type(parameter.id, parameter.monotype);
                    if monotype != parameter.monotype {
                        parameter.monotype = monotype;
                        changed = true;
                    }
                }
                if changed {
                    let parameters = parameters.iter().map(|parameter| parameter.monotype);
                    let parameters: Vec<MonotypeId> = parameters.collect();
                    let result = body.monotype;
                    expression.monotype = self.function_type(&parameters, result);
                }
            }
            ExpressionKind::Case { scrutinees, alternatives } => {
                for (position, scrutinee) in scrutinees.iter().enumerate() {
                    let original = scrutinee_types[position];
                    if scrutinee.monotype == original {
                        continue;
                    }
                    for alternative in alternatives.iter_mut() {
                        let pattern = &mut alternative.patterns[position];
                        self.retype_pattern(pattern, original, scrutinee.monotype);
                    }
                }
            }
            _ => {}
        }
    }

    fn retype_effect(&mut self, expression: &mut Expression) {
        let Some(result) = self.monotypes.effect_result(expression.monotype) else { return };
        if self.layouts.layout(self.monotypes, self.shapes, result).width == 0 {
            return;
        }
        let inner = match &expression.kind {
            ExpressionKind::EffectPure(value) => {
                self.monotypes.intern(Monotype::Effect(value.monotype))
            }
            ExpressionKind::EffectBind { body, .. } | ExpressionKind::Let { body, .. } => {
                body.monotype
            }
            ExpressionKind::If { then, .. } => then.monotype,
            ExpressionKind::Case { alternatives, .. } => match alternatives.first() {
                Some(Alternative { body: Guarded::Unconditional(body), .. }) => body.monotype,
                _ => return,
            },
            _ => return,
        };
        if self.monotypes.effect_result(inner).is_some() {
            expression.monotype = inner;
        }
    }

    /// The result of a function type once `count` arguments are applied.
    fn results_after(&self, mut monotype: MonotypeId, count: usize) -> MonotypeId {
        for _ in 0..count {
            let Some((_, result)) = self.monotypes.function_parts(monotype) else { break };
            monotype = result;
        }
        monotype
    }

    /// A pattern on a record whose fields' maps are Go maps: the record patterns and the locals
    /// they bind take the record's type.
    fn retype_pattern(
        &mut self,
        pattern: &mut Pattern,
        original: MonotypeId,
        monotype: MonotypeId,
    ) {
        if pattern.monotype != original {
            return;
        }
        pattern.monotype = monotype;
        if let PatternKind::Constructor { arguments, .. } = &mut pattern.kind {
            // A pattern on a product that holds Go maps, which is a record there.
            let arguments = std::mem::take(arguments);
            let labels = PRODUCT_LABELS.iter().map(|&label| SmolStr::new_static(label));
            pattern.kind = PatternKind::Record(labels.zip(arguments).collect());
        }
        match &mut pattern.kind {
            PatternKind::Variable(local) => local.monotype = monotype,
            PatternKind::Record(fields) => {
                let Some(originals) = fields_of(self.monotypes, original) else { return };
                let Monotype::Record(types) = self.monotypes.get(monotype).clone() else { return };
                for (label, field) in fields {
                    let typed = |fields: &[RecordField]| {
                        fields
                            .iter()
                            .find(|typed| typed.label == *label)
                            .map(|typed| typed.monotype)
                    };
                    if let (Some(original), Some(monotype)) = (typed(&originals), typed(&types))
                        && original != monotype
                    {
                        self.retype_pattern(field, original, monotype);
                    }
                }
            }
            _ => {}
        }
    }

    /// A map-typed expression of a web that is a Go map: its type, and the operation it is.
    fn native(&mut self, expression: &mut Expression) {
        if let ExpressionKind::Foreign { .. } = expression.kind {
            self.native_object(expression);
            return;
        }
        let hash = expression.monotype;
        let operation = match &expression.kind {
            ExpressionKind::Apply { function, arguments } => match function.kind {
                ExpressionKind::Function(id) => self
                    .operations
                    .get(&id)
                    .copied()
                    .filter(|operation| operation.arity() == arguments.len()),
                _ => None,
            },
            ExpressionKind::Function(id) => self.operations.get(id).copied(),
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
            | MapOperation::IsEmpty
            | MapOperation::FindMin
            | MapOperation::FindMax
            | MapOperation::LookupLE
            | MapOperation::LookupLT
            | MapOperation::LookupGE
            | MapOperation::LookupGT
            | MapOperation::AscendingEntries => {
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
        if self.adds_integers(&combine) {
            // An Int absent counts from zero, `0 + v` being `v`: `m[k] += v`.
            return hash_map(HashMapOperation::Add, vec![key, value, table], hash);
        }
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

    /// Whether a function of two Ints adds them: `(+)` of Int, or a lambda that does.
    fn adds_integers(&self, function: &Expression) -> bool {
        let (parameters, body) = match &function.kind {
            ExpressionKind::Lambda { parameters, body } => (parameters, body.as_ref()),
            ExpressionKind::Function(id) => {
                let function = self.program.function(*id);
                (&function.parameters, &function.body)
            }
            _ => return false,
        };
        let [left, right] = &parameters[..] else { return false };
        let int = |local: &Local| matches!(self.monotypes.get(local.monotype), Monotype::Int);
        let ExpressionKind::Foreign { foreign, arguments } = &body.kind else { return false };
        let Foreign::Operator(Operator::IntAdd) = foreign else { return false };
        let is = |expression: &Expression, local: &Local| matches!(expression.kind, ExpressionKind::Local(id) if id == local.id);
        let adds = match &arguments[..] {
            [first, second] => {
                (is(first, left) && is(second, right)) || (is(first, right) && is(second, left))
            }
            _ => false,
        };
        adds && int(left) && int(right)
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
        let arguments = vec![key_ref.clone(), table_ref.clone()];
        let current = hash_map(HashMapOperation::Lookup, arguments, maybe);
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
            Monotype::HashMap(_, value) | Monotype::OrderedMap(_, value) => *value,
            _ => unreachable!("invariant violated: no Go map type"),
        }
    }
}

/// A product built where it holds Go maps: the record it is there.
fn as_record(expression: &mut Expression) {
    let ExpressionKind::Construct { arguments, .. } = &mut expression.kind else { return };
    let arguments = std::mem::take(arguments);
    let labels = PRODUCT_LABELS.iter().map(|&label| SmolStr::new_static(label));
    expression.kind = ExpressionKind::Record(labels.zip(arguments).collect());
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

/// The local an array is as long as: the array itself, or what a `map` maps over.
fn as_long_as(array: &Expression) -> Option<&Expression> {
    match &array.kind {
        ExpressionKind::Local(_) => Some(array),
        ExpressionKind::Foreign { foreign: Foreign::Call { boundary, .. }, arguments }
            if matches!(boundary.iteration, Some(Iteration::Map | Iteration::MapWithIndex))
                && arguments.len() == 2 =>
        {
            as_long_as(&arguments[1])
        }
        _ => None,
    }
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
