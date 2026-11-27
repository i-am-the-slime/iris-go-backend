//! Which `Data.Map`s are Go maps: those the program owns along their whole life and only builds,
//! updates and queries by key ([`crate::maps`]).
//!
//! A map value goes through the program as a *web*: the locals, parameters and results it is
//! bound to, the map operations that update it, the branches that choose between versions of it,
//! the folds that carry it and the record fields that hold it. A web is a Go map when
//!
//! - every operation on it is one a Go map does ([`MapOperation`]), at a key whose `Ord` is
//!   Go's `==` and sort;
//! - every local it is bound to is used linearly ([`uniqueness::is_unique`]): read by those
//!   operations, then passed on at most once, so that no version is seen after the next one
//!   was made from it in place; a record local is linear in each field that holds a map
//!   ([`uniqueness::is_unique_field`]);
//! - it is made by those operations, or is a fold's seed that the fold then owns.
//!
//! A value has a *slot* for every map it holds: a map has one, a record one for each map its
//! fields hold, in the order of its fields ([`Layout`]), and every slot is a node of a web. A
//! product, a data type of one constructor such as `Tuple`, holds its maps as a record of its
//! fields does, and is that record where it holds Go maps.
//!
//! Anything else a version of the map meets, a function that walks the tree or a value that
//! keeps it, takes the tree: the map's entries are sorted once by key and built into a balanced
//! tree there, a value of its own that nothing writes. Nothing writes or hands on the map after
//! it was converted ([`Ordering`]), so that it is converted at most once on its way. A fold that
//! starts from a tree turns it into a Go map first, and owns that map.
//!
//! A function's parameters and result are one web for all its callers, so the callers that hand
//! it Go maps call a variant of it made for them ([`callers`]), and the others the function.

use std::rc::Rc;
use std::sync::Arc;

use rustc_hash::{FxHashMap, FxHashSet};
use smol_str::SmolStr;

use super::uniqueness::{self, Forced, Scope, Shapes};
use crate::foreign::{Foreign, Iteration};
use crate::maps::MapOperation;
use crate::monomorphic::traversal::for_each_child;
use crate::monomorphic::{
    Alternative, Binding, Expression, ExpressionKind, Function, FunctionId, Guard, Guarded, Local,
    LocalId, Pattern, PatternKind, Program, RecordUpdate,
};
use crate::monotype::{DataType, Monotype, MonotypeId, Monotypes, RecordField};

mod callers;
mod rewrite;

pub(super) use self::callers::HASHED;
use self::callers::Specialised;
use self::rewrite::Rewrite;

/// The names of the map operations that some Go map does.
pub(crate) fn operations_used(
    program: &Program,
    monotypes: &Monotypes,
    operations: &FxHashMap<FunctionId, MapOperation>,
) -> FxHashSet<SmolStr> {
    if operations.is_empty() || !uniqueness::enabled() {
        return FxHashSet::default();
    }
    let shapes = map_shapes(program, operations);
    // The map operations keep their places among the functions when variants are added.
    let decided = match callers::specialise(program, monotypes, operations, &shapes) {
        Specialised::Unchanged(decided) | Specialised::Variants(_, decided) => decided,
    };
    decided
        .calls
        .iter()
        .filter(|&&(_, node)| decided.is_native(node))
        .map(|&(id, _)| program.function(id).name.clone())
        .collect()
}

/// Rewrites the program so that the maps that may be Go maps are, and their operations Go map
/// operations.
pub(super) fn choose_hash_maps(
    program: &mut Program,
    monotypes: &mut Monotypes,
    operations: &FxHashMap<FunctionId, MapOperation>,
) {
    if operations.is_empty() || !uniqueness::enabled() {
        return;
    }
    let shapes = map_shapes(program, operations);
    if shapes.is_empty() {
        return;
    }
    let webs = match callers::specialise(program, monotypes, operations, &shapes) {
        Specialised::Unchanged(decided) => decided,
        Specialised::Variants(specialised, decided) => {
            // The functions move with their program, so that the analysis still finds them.
            *program = specialised;
            decided
        }
    };
    if webs.native_nodes.is_empty() {
        return;
    }
    Rewrite::new(program, monotypes, operations, &shapes, webs).rewrite();
}

/// What the program's map values do, as found and decided, and what they could be with
/// variants ([`Hopes`]).
fn analyse_hopefully(
    program: &Program,
    monotypes: &Monotypes,
    operations: &FxHashMap<FunctionId, MapOperation>,
    shapes: &FxHashMap<MonotypeId, MapShape>,
) -> (Decided, Hopes) {
    let readers = readers(program, operations, shapes);
    let mut finder = Webs::new(program, monotypes, operations, shapes, &readers);
    finder.find();
    let calls = finder.settle(Hope::Calls).tree;
    finder.could_take = calls.clone();
    let hopes = Hopes { results: finder.settle(Hope::Results).tree, calls };
    (finder.decide(), hopes)
}

/// What the program's map values do, as found and decided.
fn analyse(
    program: &Program,
    monotypes: &Monotypes,
    operations: &FxHashMap<FunctionId, MapOperation>,
    shapes: &FxHashMap<MonotypeId, MapShape>,
) -> Decided {
    let readers = readers(program, operations, shapes);
    let mut finder = Webs::new(program, monotypes, operations, shapes, &readers);
    finder.find();
    finder.decide()
}

/// The key and value of a map type that some map operation works on.
#[derive(Clone, Copy)]
struct MapShape {
    key: MonotypeId,
    value: MonotypeId,
}

fn map_shapes(
    program: &Program,
    operations: &FxHashMap<FunctionId, MapOperation>,
) -> FxHashMap<MonotypeId, MapShape> {
    let mut keys: FxHashMap<MonotypeId, MonotypeId> = FxHashMap::default();
    let mut values: FxHashMap<MonotypeId, MonotypeId> = FxHashMap::default();
    for (&id, &operation) in operations {
        let function = program.function(id);
        let map = match operation.map_position() {
            Some(position) => function.parameters[position].monotype,
            None => function.result,
        };
        let parameter = |index: usize| function.parameters[index].monotype;
        match operation {
            MapOperation::Singleton | MapOperation::Insert => {
                keys.insert(map, parameter(0));
                values.insert(map, parameter(1));
            }
            MapOperation::InsertWith => {
                keys.insert(map, parameter(1));
                values.insert(map, parameter(2));
            }
            MapOperation::Delete | MapOperation::Lookup | MapOperation::Member => {
                keys.insert(map, parameter(0));
            }
            MapOperation::Alter | MapOperation::Update => {
                keys.insert(map, parameter(1));
            }
            MapOperation::Empty
            | MapOperation::Size
            | MapOperation::IsEmpty
            | MapOperation::Difference => {}
        }
    }
    keys.into_iter()
        .filter_map(|(map, key)| Some((map, MapShape { key, value: *values.get(&map)? })))
        .collect()
}

/// The slots of a type's values: one for a map, the slots of each field for a record, in the
/// order of its fields, and none for anything else.
#[derive(Default)]
struct Layout {
    width: usize,
    /// The record fields that have slots.
    fields: Vec<FieldSlots>,
    /// The labels that lead to each slot's map.
    paths: Vec<Vec<SmolStr>>,
}

struct FieldSlots {
    label: SmolStr,
    monotype: MonotypeId,
    start: usize,
    width: usize,
}

impl Layout {
    fn field(&self, label: &str) -> Option<&FieldSlots> {
        self.fields.iter().find(|field| field.label == label)
    }
}

/// The layouts of the types met, made at first need.
#[derive(Default)]
struct Layouts {
    known: FxHashMap<MonotypeId, Rc<Layout>>,
    /// The types whose layouts are being made, so that a type that holds itself has no slots.
    visiting: FxHashSet<MonotypeId>,
}

/// The labels a product's fields have where it holds Go maps and is a record.
const PRODUCT_LABELS: &[&str] = &[
    "first", "second", "third", "fourth", "fifth", "sixth", "seventh", "eighth", "ninth", "tenth",
];

/// The fields of a record, or of a product, a data type of one constructor, as the record a
/// product is where it holds Go maps: its fields labelled by their order.
fn fields_of(monotypes: &Monotypes, monotype: MonotypeId) -> Option<Arc<[RecordField]>> {
    match monotypes.get(monotype) {
        Monotype::Record(fields) => Some(Arc::clone(fields)),
        Monotype::Data(data) => {
            let fields = product_fields(monotypes, data)?;
            let labelled = fields.iter().zip(PRODUCT_LABELS).map(|(&monotype, &label)| {
                RecordField { label: SmolStr::new_static(label), monotype }
            });
            Some(labelled.collect())
        }
        _ => None,
    }
}

/// The fields of a data type of one constructor, of a few fields, that nothing refutes.
fn product_fields(monotypes: &Monotypes, data: &DataType) -> Option<Vec<MonotypeId>> {
    let constructors = monotypes.known_constructors(data)?;
    let [constructor] = &constructors[..] else { return None };
    let count = constructor.fields.len();
    let fits = !constructor.refuted && count > 0 && count <= PRODUCT_LABELS.len();
    fits.then(|| constructor.fields.clone())
}

/// Whether the type is a product ([`product_fields`]).
fn is_product(monotypes: &Monotypes, monotype: MonotypeId) -> bool {
    match monotypes.get(monotype) {
        Monotype::Data(data) => product_fields(monotypes, data).is_some(),
        _ => false,
    }
}

impl Layouts {
    fn layout(
        &mut self,
        monotypes: &Monotypes,
        shapes: &FxHashMap<MonotypeId, MapShape>,
        monotype: MonotypeId,
    ) -> Rc<Layout> {
        if let Some(layout) = self.known.get(&monotype) {
            return Rc::clone(layout);
        }
        let layout = if shapes.contains_key(&monotype) {
            Layout { width: 1, fields: vec![], paths: vec![vec![]] }
        } else if let Some(record) = fields_of(monotypes, monotype) {
            if !self.visiting.insert(monotype) {
                return Rc::new(Layout::default());
            }
            let mut fields = vec![];
            let mut width = 0;
            let mut paths = vec![];
            for field in record.iter() {
                let inner = self.layout(monotypes, shapes, field.monotype);
                for path in &inner.paths {
                    let mut labels = vec![field.label.clone()];
                    labels.extend(path.iter().cloned());
                    paths.push(labels);
                }
                if inner.width > 0 {
                    let label = field.label.clone();
                    let (monotype, start) = (field.monotype, width);
                    fields.push(FieldSlots { label, monotype, start, width: inner.width });
                    width += inner.width;
                }
            }
            self.visiting.remove(&monotype);
            Layout { width, fields, paths }
        } else {
            Layout::default()
        };
        let layout = Rc::new(layout);
        self.known.insert(monotype, Rc::clone(&layout));
        layout
    }
}

/// A place a map value is bound to or made at.
type Node = usize;

/// The nodes of a value's slots ([`Layout`]).
type Slots = Vec<Node>;

#[derive(Clone, Copy, PartialEq, Eq)]
enum Flow {
    /// A map stored in a record field or read from one.
    Argument,
    /// An argument to a function's parameter.
    Call,
    /// A function's result to its call.
    Result,
    /// A fold's seed, to the accumulator the fold owns.
    Seed,
}

struct SoftEdge {
    from: Slots,
    to: Slots,
    flow: Flow,
    at: *const Expression,
}

/// The code a local is used in, by address.
#[derive(Clone, Copy)]
enum ScopeAt {
    Expression(*const Expression),
    Guarded(*const Guarded),
}

impl ScopeAt {
    fn of(scope: Scope<'_>) -> ScopeAt {
        match scope {
            Scope::Expression(expression) => ScopeAt::Expression(expression),
            Scope::Guarded(guarded) => ScopeAt::Guarded(guarded),
        }
    }

    /// SAFETY of the pointers: the program is borrowed for the whole analysis.
    fn scope<'p>(self) -> Scope<'p> {
        match self {
            ScopeAt::Expression(expression) => Scope::Expression(unsafe { &*expression }),
            ScopeAt::Guarded(guarded) => Scope::Guarded(unsafe { &*guarded }),
        }
    }
}

/// A local that the slots of a map, or of a record's field, are bound to, which must use them
/// linearly.
struct Linear {
    node: Node,
    local: LocalId,
    path: Vec<SmolStr>,
    scope: ScopeAt,
}

/// What the program does with its map values, as webs of nodes.
struct Webs<'p> {
    program: &'p Program,
    monotypes: &'p Monotypes,
    operations: &'p FxHashMap<FunctionId, MapOperation>,
    shapes: &'p FxHashMap<MonotypeId, MapShape>,
    readers: &'p FxHashSet<LocalId>,
    layouts: Layouts,
    parents: Vec<Node>,
    /// Whether the node must be a tree: it is made or used in a way only the tree does.
    tree: Vec<bool>,
    locals: FxHashMap<LocalId, Slots>,
    results: FxHashMap<FunctionId, Slots>,
    /// The slots of every expression whose type has some.
    expressions: FxHashMap<*const Expression, Slots>,
    /// The expressions whose value, with its maps, goes somewhere only a tree may go.
    escapes: Vec<(Slots, *const Expression)>,
    soft: Vec<SoftEdge>,
    /// The nodes that a map operation reads or writes.
    operated: Vec<Node>,
    linear: Vec<Linear>,
    /// The map operations the program calls, each with the node of the map it works on.
    calls: Vec<(FunctionId, Node)>,
    /// The calls of the program's own functions with all their parameters.
    sites: Vec<CallSite>,
    site_of: FxHashMap<*const Expression, usize>,
    /// Whether each web is a tree under [`Hope::Calls`], once that is settled.
    could_take: Vec<bool>,
}

/// Which calls are taken to hand on no trees, as if each called the variant of its function
/// made for what it passes ([`callers`]).
#[derive(Clone, Copy, PartialEq, Eq)]
enum Hope {
    None,
    /// No call's result is a tree when the call hands its callee a Go map that the callee could
    /// take ([`Hope::Calls`]): a variant made for it could give Go maps back.
    Results,
    /// No parameter or result is a tree but by what its function does itself.
    Calls,
}

/// The webs as they would be under each [`Hope`]: whether each node is a tree.
pub(super) struct Hopes {
    results: Vec<bool>,
    calls: Vec<bool>,
}

/// A call of one of the program's functions with all its parameters: the slots of each
/// argument that hands its maps to the parameter.
pub(super) struct CallSite {
    pub(super) call: *const Expression,
    pub(super) callee: FunctionId,
    pub(super) arguments: Vec<Option<Slots>>,
    /// Each node of the arguments with the node of the parameter it is handed to.
    handed: Vec<(Node, Node)>,
}

/// The representation of each slot of a value: a Go map, or the tree.
type Natives = Vec<bool>;

/// A value that changes representation where it is: from the representation of its slots to
/// another.
struct Conversion {
    from: Natives,
    to: Natives,
}

/// The webs that are Go maps, and where values change representation.
struct Decided {
    native_nodes: FxHashSet<Node>,
    expressions: FxHashMap<*const Expression, Slots>,
    locals: FxHashMap<LocalId, Slots>,
    results: FxHashMap<FunctionId, Slots>,
    conversions: FxHashMap<*const Expression, Conversion>,
    parents: Vec<Node>,
    calls: Vec<(FunctionId, Node)>,
    sites: Vec<CallSite>,
}

impl Decided {
    fn root(&self, mut node: Node) -> Node {
        while self.parents[node] != node {
            node = self.parents[node];
        }
        node
    }

    fn is_native(&self, node: Node) -> bool {
        self.native_nodes.contains(&self.root(node))
    }

    fn natives(&self, slots: &[Node]) -> Natives {
        slots.iter().map(|&node| self.is_native(node)).collect()
    }
}

impl<'p> Webs<'p> {
    fn new(
        program: &'p Program,
        monotypes: &'p Monotypes,
        operations: &'p FxHashMap<FunctionId, MapOperation>,
        shapes: &'p FxHashMap<MonotypeId, MapShape>,
        readers: &'p FxHashSet<LocalId>,
    ) -> Webs<'p> {
        Webs {
            program,
            monotypes,
            operations,
            shapes,
            readers,
            layouts: Layouts::default(),
            parents: vec![],
            tree: vec![],
            locals: FxHashMap::default(),
            results: FxHashMap::default(),
            expressions: FxHashMap::default(),
            escapes: vec![],
            soft: vec![],
            operated: vec![],
            linear: vec![],
            calls: vec![],
            sites: vec![],
            site_of: FxHashMap::default(),
            could_take: vec![],
        }
    }

    fn is_map(&self, monotype: MonotypeId) -> bool {
        self.shapes.contains_key(&monotype)
    }

    fn layout(&mut self, monotype: MonotypeId) -> Rc<Layout> {
        self.layouts.layout(self.monotypes, self.shapes, monotype)
    }

    /// Whether values of the type hold maps.
    fn holds_maps(&mut self, monotype: MonotypeId) -> bool {
        self.layout(monotype).width > 0
    }

    fn fresh(&mut self, tree: bool) -> Node {
        let node = self.parents.len();
        self.parents.push(node);
        self.tree.push(tree);
        node
    }

    fn fresh_slots(&mut self, monotype: MonotypeId, tree: bool) -> Slots {
        let width = self.layout(monotype).width;
        (0..width).map(|_| self.fresh(tree)).collect()
    }

    fn root(&mut self, node: Node) -> Node {
        let mut root = node;
        while self.parents[root] != root {
            root = self.parents[root];
        }
        let mut current = node;
        while self.parents[current] != root {
            let next = self.parents[current];
            self.parents[current] = root;
            current = next;
        }
        root
    }

    fn join(&mut self, left: Node, right: Node) -> Node {
        let (left, right) = (self.root(left), self.root(right));
        if left != right {
            self.parents[right] = left;
            self.tree[left] |= self.tree[right];
        }
        left
    }

    fn join_slots(&mut self, left: &[Node], right: &[Node]) {
        for (&left, &right) in left.iter().zip(right) {
            self.join(left, right);
        }
    }

    fn force_tree(&mut self, node: Node) {
        let root = self.root(node);
        self.tree[root] = true;
    }

    fn force_trees(&mut self, slots: &[Node]) {
        for &node in slots {
            self.force_tree(node);
        }
    }

    fn local(&mut self, id: LocalId, monotype: MonotypeId) -> Slots {
        if let Some(slots) = self.locals.get(&id) {
            return slots.clone();
        }
        let slots = self.fresh_slots(monotype, false);
        self.locals.insert(id, slots.clone());
        slots
    }

    fn result(&mut self, id: FunctionId) -> Slots {
        if let Some(slots) = self.results.get(&id) {
            return slots.clone();
        }
        let result = self.program.function(id).result;
        let slots = self.fresh_slots(result, false);
        self.results.insert(id, slots.clone());
        slots
    }

    fn soft(&mut self, from: Slots, to: Slots, flow: Flow, at: &Expression) {
        let at = std::ptr::from_ref(at);
        self.soft.push(SoftEdge { from, to, flow, at });
    }

    fn operation(&self, function: &Expression, arguments: &[Expression]) -> Option<MapOperation> {
        map_operation(self.operations, function, arguments)
    }

    /// The function a call calls with all its parameters, when it is one that is not a map
    /// operation.
    fn called(&self, function: &Expression, arguments: usize) -> Option<FunctionId> {
        let ExpressionKind::Function(id) = function.kind else { return None };
        let callee = self.program.function(id);
        (!self.operations.contains_key(&id) && callee.parameters.len() == arguments).then_some(id)
    }

    fn find(&mut self) {
        let program = self.program;
        for (index, function) in program.functions.iter().enumerate() {
            let id = FunctionId(index as u32);
            if self.operations.contains_key(&id) {
                continue;
            }
            self.function(id, function);
        }
    }

    fn function(&mut self, id: FunctionId, function: &'p Function) {
        for parameter in &function.parameters {
            if self.holds_maps(parameter.monotype) {
                let slots = self.local(parameter.id, parameter.monotype);
                self.require_linear(&slots, parameter, Scope::Expression(&function.body));
            }
        }
        if self.holds_maps(function.result) {
            let body = self.value(&function.body);
            let result = self.result(id);
            self.join_slots(&body, &result);
            if function.parameters.is_empty() {
                // A constant is one value that every use shares.
                self.force_trees(&result);
            }
        } else {
            self.expression(&function.body);
        }
    }

    /// The local must use the maps it holds linearly: a map as a whole, a record each map it
    /// holds by the fields that lead to it.
    fn require_linear(&mut self, slots: &[Node], local: &Local, scope: Scope<'p>) {
        let mut reads =
            Reads { program: self.program, operations: self.operations, readers: self.readers };
        let at = ScopeAt::of(scope);
        let layout = self.layout(local.monotype);
        for (&node, path) in slots.iter().zip(&layout.paths) {
            self.linear.push(Linear { node, local: local.id, path: path.clone(), scope: at });
            if !is_linear(&mut reads, local.id, path, scope) {
                self.force_tree(node);
            }
        }
    }

    /// Every function of `id` is used as a value, or called with other than all its
    /// parameters: its map parameters and result are trees.
    fn opaque_function(&mut self, id: FunctionId) {
        if self.operations.contains_key(&id) {
            return;
        }
        let function = self.program.function(id);
        for parameter in &function.parameters {
            if self.holds_maps(parameter.monotype) {
                let slots = self.local(parameter.id, parameter.monotype);
                self.force_trees(&slots);
            }
        }
        if self.holds_maps(function.result) {
            let slots = self.result(id);
            self.force_trees(&slots);
        }
    }

    /// The slots of the value of an expression whose type has some.
    fn value(&mut self, expression: &'p Expression) -> Slots {
        let slots = self.value_unrecorded(expression);
        self.expressions.insert(std::ptr::from_ref(expression), slots.clone());
        slots
    }

    fn value_unrecorded(&mut self, expression: &'p Expression) -> Slots {
        match &expression.kind {
            ExpressionKind::Local(id) => self.local(*id, expression.monotype),
            ExpressionKind::Function(id) => match self.operations.get(id) {
                Some(MapOperation::Empty) if self.is_map(expression.monotype) => {
                    let node = self.fresh(false);
                    self.calls.push((*id, node));
                    vec![node]
                }
                _ => {
                    let function = self.program.function(*id);
                    if function.parameters.is_empty() {
                        self.result(*id)
                    } else {
                        self.fresh_slots(expression.monotype, true)
                    }
                }
            },
            ExpressionKind::Apply { function, arguments } => {
                if let Some(operation) = self.operation(function, arguments) {
                    return vec![self.operation_value(expression, function, operation, arguments)];
                }
                if let Some(id) = self.called(function, arguments.len()) {
                    self.arguments(expression, id, arguments);
                    let result = self.result(id);
                    let answer = self.fresh_slots(expression.monotype, false);
                    self.soft(result, answer.clone(), Flow::Result, expression);
                    return answer;
                }
                self.expression_children(expression);
                self.fresh_slots(expression.monotype, true)
            }
            ExpressionKind::Let { bindings, body } => {
                self.bindings(expression, bindings);
                self.value(body)
            }
            ExpressionKind::If { condition, then, otherwise } => {
                self.expression(condition);
                let then = self.value(then);
                let otherwise = self.value(otherwise);
                self.join_slots(&then, &otherwise);
                then
            }
            ExpressionKind::Case { scrutinees, alternatives } => {
                self.scrutinees(scrutinees, alternatives);
                let mut joined: Option<Slots> = None;
                for body in alternative_bodies(alternatives) {
                    let slots = self.value(body);
                    match &joined {
                        Some(joined) => self.join_slots(joined, &slots),
                        None => joined = Some(slots),
                    }
                }
                joined.unwrap_or_else(|| self.fresh_slots(expression.monotype, true))
            }
            ExpressionKind::Foreign { foreign, arguments } if is_fold_left(foreign, arguments) => {
                self.fold(expression, arguments)
            }
            ExpressionKind::Record(fields) => {
                let fields = fields.iter().map(|(label, value)| (label.as_str(), value));
                self.record(expression, fields)
            }
            ExpressionKind::Construct { arguments, .. }
                if is_product(self.monotypes, expression.monotype) =>
            {
                self.record(expression, PRODUCT_LABELS.iter().copied().zip(arguments))
            }
            ExpressionKind::Access { record, label } => {
                let read = self.field_of(record, label);
                let answer = self.fresh_slots(expression.monotype, false);
                self.soft(read, answer.clone(), Flow::Argument, expression);
                answer
            }
            ExpressionKind::Update { record, updates } => {
                let mut slots = self.value(record);
                self.updates(record.monotype, &mut slots, updates);
                slots
            }
            _ => {
                self.expression_children(expression);
                self.fresh_slots(expression.monotype, true)
            }
        }
    }

    /// A record built of its fields, or a product of its arguments: each map a field holds is
    /// stored in the value's slot.
    fn record(
        &mut self,
        expression: &'p Expression,
        fields: impl Iterator<Item = (&'p str, &'p Expression)>,
    ) -> Slots {
        let layout = self.layout(expression.monotype);
        let slots = self.fresh_slots(expression.monotype, false);
        for (label, value) in fields {
            match layout.field(label) {
                Some(field) => {
                    let stored = self.value(value);
                    let place = slots[field.start..field.start + field.width].to_vec();
                    self.soft(stored, place, Flow::Argument, value);
                }
                None => self.expression(value),
            }
        }
        slots
    }

    /// The slots of a record's field, read from the record.
    fn field_of(&mut self, record: &'p Expression, label: &str) -> Slots {
        let slots = self.value(record);
        let layout = self.layout(record.monotype);
        match layout.field(label) {
            Some(field) => slots[field.start..field.start + field.width].to_vec(),
            None => vec![],
        }
    }

    /// `record { label = value }`: the fields it replaces hold the maps of their values, the
    /// others those of the record.
    fn updates(&mut self, monotype: MonotypeId, slots: &mut [Node], updates: &'p [RecordUpdate]) {
        let layout = self.layout(monotype);
        for update in updates {
            match update {
                RecordUpdate::Leaf { label, value } => match layout.field(label) {
                    Some(field) => {
                        let stored = self.value(value);
                        let place = self.fresh_slots(field.monotype, false);
                        self.soft(stored, place.clone(), Flow::Argument, value);
                        slots[field.start..field.start + field.width].copy_from_slice(&place);
                    }
                    None => self.expression(value),
                },
                RecordUpdate::Branch { label, updates } => match layout.field(label) {
                    Some(field) => {
                        let range = field.start..field.start + field.width;
                        self.updates(field.monotype, &mut slots[range], updates);
                    }
                    None => {
                        let mut none: [Node; 0] = [];
                        self.updates(
                            field_type(self.monotypes, monotype, label),
                            &mut none,
                            updates,
                        );
                    }
                },
            }
        }
    }

    fn operation_value(
        &mut self,
        call: &Expression,
        function: &Expression,
        operation: MapOperation,
        arguments: &'p [Expression],
    ) -> Node {
        let node = self.operation_node(call, operation, arguments);
        if let ExpressionKind::Function(id) = function.kind {
            self.calls.push((id, node));
        }
        node
    }

    /// The node of the map a map operation works on. A map of a type that no operation of the
    /// program builds an entry of has no [`MapShape`] and is a tree.
    fn operation_node(
        &mut self,
        call: &Expression,
        operation: MapOperation,
        arguments: &'p [Expression],
    ) -> Node {
        let map = operation.map_position();
        let made = map.map_or(call.monotype, |position| arguments[position].monotype);
        let shaped = self.is_map(made);
        for (position, argument) in arguments.iter().enumerate() {
            let taken_away = operation == MapOperation::Difference && position == 1;
            if !shaped || (Some(position) != map && !taken_away) {
                self.expression(argument);
            }
        }
        if !shaped {
            return self.fresh(true);
        }
        let Some(position) = map else { return self.fresh(false) };
        let node = self.value(&arguments[position])[0];
        self.operated.push(node);
        if operation == MapOperation::Difference {
            // The keys to take away are read, as a Go map when the map is one.
            let other = &arguments[1];
            let removed = self.value(other);
            self.operated.push(removed[0]);
            self.soft(removed, vec![node], Flow::Seed, other);
        }
        node
    }

    fn arguments(&mut self, call: &Expression, id: FunctionId, arguments: &'p [Expression]) {
        let parameters = &self.program.function(id).parameters;
        let mut passed = vec![];
        let mut handed = vec![];
        for (argument, parameter) in arguments.iter().zip(parameters) {
            if argument.monotype == parameter.monotype && self.holds_maps(argument.monotype) {
                let from = self.value(argument);
                let to = self.local(parameter.id, parameter.monotype);
                passed.push(Some(from.clone()));
                handed.extend(from.iter().copied().zip(to.iter().copied()));
                self.soft(from, to, Flow::Call, argument);
            } else {
                passed.push(None);
                self.expression(argument);
            }
        }
        let call = std::ptr::from_ref(call);
        self.site_of.insert(call, self.sites.len());
        self.sites.push(CallSite { call, callee: id, arguments: passed, handed });
    }

    /// `foldl (\accumulator element -> ...) seed array`, whose accumulator holds maps.
    fn fold(&mut self, expression: &'p Expression, arguments: &'p [Expression]) -> Slots {
        let [callback, seed, array] = arguments else { unreachable!() };
        let ExpressionKind::Lambda { parameters, body } = &callback.kind else { unreachable!() };
        let fold = self.fresh_slots(expression.monotype, false);
        let seeded = self.value(seed);
        self.soft(seeded, fold.clone(), Flow::Seed, seed);
        let accumulator = self.local(parameters[0].id, parameters[0].monotype);
        self.join_slots(&accumulator, &fold);
        self.require_linear(&accumulator, &parameters[0], Scope::Expression(body));
        if self.holds_maps(parameters[1].monotype) {
            let element = self.local(parameters[1].id, parameters[1].monotype);
            self.force_trees(&element);
        }
        let stepped = self.value(body);
        self.join_slots(&stepped, &fold);
        self.expression(array);
        fold
    }

    fn bindings(&mut self, scope: &'p Expression, bindings: &'p [Binding]) {
        for binding in bindings {
            if self.holds_maps(binding.local.monotype) {
                let value = self.value(&binding.value);
                let local = self.local(binding.local.id, binding.local.monotype);
                self.join_slots(&value, &local);
                self.require_linear(&local, &binding.local, Scope::Expression(scope));
            } else {
                self.expression(&binding.value);
            }
        }
    }

    /// A map that is matched on is taken apart as a tree; a record that is matched on hands the
    /// maps of its fields to the locals its patterns bind them to.
    fn scrutinees(&mut self, scrutinees: &'p [Expression], alternatives: &'p [Alternative]) {
        for (position, scrutinee) in scrutinees.iter().enumerate() {
            let slots = if self.holds_maps(scrutinee.monotype) {
                let slots = self.value(scrutinee);
                if self.is_map(scrutinee.monotype) {
                    self.force_trees(&slots);
                    None
                } else {
                    Some(slots)
                }
            } else {
                self.expression(scrutinee);
                None
            };
            for alternative in alternatives {
                let scope = Scope::Guarded(&alternative.body);
                let pattern = &alternative.patterns[position];
                let slots = self.matched(slots.as_deref(), pattern, scrutinee.monotype);
                self.pattern(pattern, slots.as_deref(), scope);
            }
        }
        for alternative in alternatives {
            if let Guarded::Guards(branches) = &alternative.body {
                for guard in branches.iter().flat_map(|branch| &branch.guards) {
                    match guard {
                        Guard::Boolean(condition) => self.expression(condition),
                        Guard::Pattern { pattern, value } => {
                            self.expression(value);
                            self.pattern(pattern, None, Scope::Guarded(&alternative.body));
                        }
                    }
                }
            }
        }
    }

    /// The locals a pattern binds: to the slots of the value it matches where it takes apart
    /// only records, to trees elsewhere.
    fn pattern(&mut self, pattern: &'p Pattern, slots: Option<&[Node]>, scope: Scope<'p>) {
        match &pattern.kind {
            PatternKind::Wildcard | PatternKind::Literal(_) => {}
            PatternKind::Variable(local) => {
                if !self.holds_maps(local.monotype) {
                    return;
                }
                let bound = self.local(local.id, local.monotype);
                match slots {
                    Some(slots) => {
                        self.join_slots(&bound, slots);
                        self.require_linear(&bound, local, scope);
                    }
                    None => self.force_trees(&bound),
                }
            }
            PatternKind::Named { local, pattern } => {
                if let Some(slots) = slots {
                    self.force_trees(slots);
                }
                if self.holds_maps(local.monotype) {
                    let bound = self.local(local.id, local.monotype);
                    self.force_trees(&bound);
                }
                self.pattern(pattern, None, scope);
            }
            PatternKind::Record(fields) => {
                let layout = self.layout(pattern.monotype);
                for (label, field_pattern) in fields {
                    let field = slots.zip(layout.field(label)).and_then(|(slots, field)| {
                        let slots = &slots[field.start..field.start + field.width];
                        self.matched(Some(slots), field_pattern, field.monotype)
                    });
                    self.pattern(field_pattern, field.as_deref(), scope);
                }
            }
            PatternKind::Constructor { arguments, .. }
                if slots.is_some() && is_product(self.monotypes, pattern.monotype) =>
            {
                let layout = self.layout(pattern.monotype);
                for (label, argument) in PRODUCT_LABELS.iter().zip(arguments) {
                    let field = slots.zip(layout.field(label)).and_then(|(slots, field)| {
                        let slots = &slots[field.start..field.start + field.width];
                        self.matched(Some(slots), argument, field.monotype)
                    });
                    self.pattern(argument, field.as_deref(), scope);
                }
            }
            PatternKind::Array(patterns)
            | PatternKind::Constructor { arguments: patterns, .. }
            | PatternKind::Closure { captures: patterns, .. } => {
                for pattern in patterns {
                    self.pattern(pattern, None, scope);
                }
            }
        }
    }

    /// The slots of a value of type `monotype` that a pattern takes apart, when the pattern has
    /// that type; a pattern of another type, on a newtype the program sees through, makes the
    /// value's maps trees.
    fn matched(
        &mut self,
        slots: Option<&[Node]>,
        pattern: &Pattern,
        monotype: MonotypeId,
    ) -> Option<Slots> {
        let slots = slots?;
        if pattern.monotype == monotype {
            return Some(slots.to_vec());
        }
        self.force_trees(slots);
        None
    }

    /// An expression whose value, if it holds maps, goes somewhere only a tree may go.
    fn expression(&mut self, expression: &'p Expression) {
        if self.holds_maps(expression.monotype) {
            let slots = self.value(expression);
            self.escapes.push((slots, std::ptr::from_ref(expression)));
            return;
        }
        match &expression.kind {
            ExpressionKind::Function(id) => self.opaque_function(*id),
            ExpressionKind::Apply { function, arguments } => {
                if let Some(operation) = self.operation(function, arguments) {
                    self.operation_value(expression, function, operation, arguments);
                    return;
                }
                if let Some(id) = self.called(function, arguments.len()) {
                    self.arguments(expression, id, arguments);
                    return;
                }
                self.expression_children(expression);
            }
            ExpressionKind::Access { record, .. } if self.holds_maps(record.monotype) => {
                // A field that holds no map, read from a record that holds some.
                self.value(record);
            }
            ExpressionKind::Let { bindings, body } => {
                self.bindings(expression, bindings);
                self.expression(body);
            }
            ExpressionKind::Case { scrutinees, alternatives } => {
                self.scrutinees(scrutinees, alternatives);
                for body in alternative_bodies(alternatives) {
                    self.expression(body);
                }
            }
            ExpressionKind::Lambda { parameters, .. } => {
                self.bound_trees(parameters);
                self.expression_children(expression);
            }
            ExpressionKind::EffectBind { local, .. }
            | ExpressionKind::EffectEach { element: local, .. } => {
                self.bound_trees(std::slice::from_ref(local));
                self.expression_children(expression);
            }
            _ => self.expression_children(expression),
        }
    }

    fn bound_trees(&mut self, locals: &[Local]) {
        for local in locals {
            if self.holds_maps(local.monotype) {
                let slots = self.local(local.id, local.monotype);
                self.force_trees(&slots);
            }
        }
    }

    fn expression_children(&mut self, expression: &'p Expression) {
        let mut children = vec![];
        for_each_child(expression, &mut |child| children.push(child));
        if let ExpressionKind::Apply { function, .. } = &expression.kind
            && let ExpressionKind::Function(id) = function.kind
        {
            // Called with other than all its parameters.
            self.opaque_function(id);
            children.retain(|child| !std::ptr::eq(*child, function.as_ref()));
        }
        if let ExpressionKind::Case { scrutinees, alternatives } = &expression.kind {
            self.scrutinees(scrutinees, alternatives);
            for body in alternative_bodies(alternatives) {
                self.expression(body);
            }
            return;
        }
        if let ExpressionKind::Let { bindings, body } = &expression.kind {
            self.bindings(expression, bindings);
            self.expression(body);
            return;
        }
        for child in children {
            self.expression(child);
        }
    }

    /// Settles which webs are Go maps, until every local of a Go map is converted to a tree only
    /// where nothing writes or passes on the map after ([`Ordering`]).
    fn decide(mut self) -> Decided {
        loop {
            let settled = self.settle(Hope::None);
            let mut forced = vec![];
            for linear in &self.linear {
                if settled.tree[root_of(&mut self.parents, linear.node)] {
                    continue;
                }
                let mut shapes = Ordering {
                    program: self.program,
                    operations: self.operations,
                    readers: self.readers,
                    to_tree: &settled.to_tree,
                };
                if !is_linear(&mut shapes, linear.local, &linear.path, linear.scope.scope()) {
                    forced.push(linear.node);
                }
            }
            if forced.is_empty() {
                return self.decided(settled);
            }
            for node in forced {
                self.force_tree(node);
            }
        }
    }

    /// Which webs are Go maps as the facts stand: a web is a tree when it must be, or when a
    /// tree reaches a parameter or a field of it; a Go map reaching a tree's parameter or field,
    /// and every escape of one, becomes a tree there; a tree that seeds a fold that is a Go map
    /// becomes one there.
    fn settle(&mut self, hope: Hope) -> Settled {
        let mut tree: Vec<bool> = (0..self.parents.len())
            .map(|node| {
                let root = self.root(node);
                self.tree[root]
            })
            .collect();
        let handed: Vec<Vec<(Node, Node)>> = match hope {
            Hope::Results => self
                .sites
                .iter()
                .map(|site| {
                    let handed = site.handed.iter();
                    handed
                        .map(|&(from, to)| {
                            (root_of(&mut self.parents, from), root_of(&mut self.parents, to))
                        })
                        .collect()
                })
                .collect(),
            Hope::None | Hope::Calls => vec![],
        };
        // Whether a call hands a Go map to a parameter of its callee that could take one, so
        // that a variant of the callee could take it and give Go maps back.
        let hands_on_hoped_maps = |call: *const Expression, tree: &[bool]| {
            self.site_of.get(&call).is_some_and(|&site| {
                handed[site].iter().any(|&(from, to)| !tree[from] && !self.could_take[to])
            })
        };
        loop {
            let mut changed = false;
            for edge in &self.soft {
                let passes_trees = match edge.flow {
                    Flow::Argument => true,
                    Flow::Call => hope != Hope::Calls,
                    Flow::Result => match hope {
                        Hope::None => true,
                        Hope::Results => !hands_on_hoped_maps(edge.at, &tree),
                        Hope::Calls => false,
                    },
                    Flow::Seed => false,
                };
                if !passes_trees {
                    continue;
                }
                for (&from, &to) in edge.from.iter().zip(&edge.to) {
                    let from = root_of(&mut self.parents, from);
                    let to = root_of(&mut self.parents, to);
                    if tree[from] && !tree[to] {
                        tree[to] = true;
                        changed = true;
                    }
                }
            }
            if !changed {
                break;
            }
        }
        self.drop_idle_webs(&mut tree, hope);
        let mut natives = |slots: &[Node]| -> Natives {
            slots.iter().map(|&node| !tree[root_of(&mut self.parents, node)]).collect()
        };
        // An expression may both take its value from elsewhere (a call's result, a field) and
        // hand it on (an argument, a field): it converts from the first to the second.
        let mut ends: FxHashMap<*const Expression, (Option<&Slots>, Option<&Slots>, bool)> =
            FxHashMap::default();
        for edge in &self.soft {
            let own = &self.expressions[&edge.at];
            let end = ends.entry(edge.at).or_default();
            if *own == edge.to {
                end.0 = Some(&edge.from);
            } else {
                end.1 = Some(&edge.to);
            }
        }
        for (_, at) in &self.escapes {
            ends.entry(*at).or_default().2 = true;
        }
        let mut conversions: FxHashMap<*const Expression, Conversion> = FxHashMap::default();
        for (at, (from, to, escaped)) in ends {
            let own = &self.expressions[&at];
            let from = natives(from.unwrap_or(own));
            let to = if escaped { vec![false; own.len()] } else { natives(to.unwrap_or(own)) };
            if from != to {
                conversions.insert(at, Conversion { from, to });
            }
        }
        let to_tree = conversions
            .iter()
            .filter(|(_, conversion)| {
                conversion.from.iter().zip(&conversion.to).any(|(&from, &to)| from && !to)
            })
            .map(|(&at, _)| at)
            .collect();
        Settled { tree, to_tree, conversions }
    }

    fn decided(mut self, settled: Settled) -> Decided {
        let mut native_nodes = FxHashSet::default();
        for node in 0..self.parents.len() {
            let root = root_of(&mut self.parents, node);
            if !settled.tree[root] {
                native_nodes.insert(root);
            }
        }
        Decided {
            native_nodes,
            expressions: self.expressions,
            locals: self.locals,
            results: self.results,
            conversions: settled.conversions,
            parents: self.parents,
            calls: self.calls,
            sites: self.sites,
        }
    }
}

struct Settled {
    tree: Vec<bool>,
    /// The expressions where some Go map becomes a tree.
    to_tree: FxHashSet<*const Expression>,
    conversions: FxHashMap<*const Expression, Conversion>,
}

impl Webs<'_> {
    /// Keeps as trees the Go maps that no map operation reads or writes, wherever they flow:
    /// made empty and converted, they would only cost the conversion.
    ///
    /// Under a [`Hope`], a call reaches the maps of a variant its callee may have, which may be
    /// Go maps where its callee's are trees, and so every map a value flows to counts.
    fn drop_idle_webs(&mut self, tree: &mut [bool], hope: Hope) {
        let mut groups: Vec<Node> = (0..self.parents.len()).collect();
        let hoped = hope != Hope::None;
        for edge in &self.soft {
            for (&from, &to) in edge.from.iter().zip(&edge.to) {
                let from = root_of(&mut self.parents, from);
                let to = root_of(&mut self.parents, to);
                if hoped || (!tree[from] && !tree[to]) {
                    let (from, to) = (root_of(&mut groups, from), root_of(&mut groups, to));
                    groups[to] = from;
                }
            }
        }
        let mut busy = FxHashSet::default();
        for &node in &self.operated {
            let root = root_of(&mut self.parents, node);
            busy.insert(root_of(&mut groups, root));
        }
        for node in 0..self.parents.len() {
            let root = root_of(&mut self.parents, node);
            if !tree[root] && !busy.contains(&root_of(&mut groups, root)) {
                tree[root] = true;
            }
        }
    }
}

/// Whether a local uses the map it holds, by the labels that lead to it, linearly in `scope`.
fn is_linear(shapes: &mut impl Shapes, local: LocalId, path: &[SmolStr], scope: Scope<'_>) -> bool {
    if path.is_empty() {
        uniqueness::is_unique(shapes, local, &[], scope, &Forced::default())
    } else {
        uniqueness::is_unique_path(shapes, local, path, scope)
    }
}

/// The type of a record's field.
fn field_type(monotypes: &Monotypes, record: MonotypeId, label: &str) -> MonotypeId {
    match monotypes.get(record) {
        Monotype::Record(fields) => fields
            .iter()
            .find(|field| field.label == label)
            .map(|field| field.monotype)
            .expect("invariant violated: an update of a field the record lacks"),
        _ => unreachable!("invariant violated: an update of no record"),
    }
}

fn root_of(parents: &mut [Node], node: Node) -> Node {
    let mut root = node;
    while parents[root] != root {
        root = parents[root];
    }
    root
}

fn is_fold_left(foreign: &Foreign, arguments: &[Expression]) -> bool {
    let Foreign::Call { boundary, .. } = foreign else { return false };
    if boundary.iteration != Some(Iteration::FoldLeft) || arguments.len() != 3 {
        return false;
    }
    matches!(
        &arguments[0].kind,
        ExpressionKind::Lambda { parameters, .. }
            if parameters.len() == 2 && parameters[0].monotype == arguments[1].monotype
    )
}

fn alternative_bodies(alternatives: &[Alternative]) -> Vec<&Expression> {
    let mut bodies = vec![];
    for alternative in alternatives {
        match &alternative.body {
            Guarded::Unconditional(body) => bodies.push(body),
            Guarded::Guards(branches) => bodies.extend(branches.iter().map(|branch| &branch.body)),
        }
    }
    bodies
}

/// The map operation a call is, called with all its arguments: `difference` only of two maps
/// of one type.
fn map_operation(
    operations: &FxHashMap<FunctionId, MapOperation>,
    function: &Expression,
    arguments: &[Expression],
) -> Option<MapOperation> {
    let ExpressionKind::Function(id) = function.kind else { return None };
    let operation = *operations.get(&id)?;
    if operation.arity() != arguments.len() {
        return None;
    }
    if operation == MapOperation::Difference && arguments[0].monotype != arguments[1].monotype {
        return None;
    }
    Some(operation)
}

/// The map parameters that their functions only read, through map operations that read and
/// other such parameters, so that passing a map to one is a read.
fn readers(
    program: &Program,
    operations: &FxHashMap<FunctionId, MapOperation>,
    shapes: &FxHashMap<MonotypeId, MapShape>,
) -> FxHashSet<LocalId> {
    let mut readers = FxHashSet::default();
    loop {
        let mut found = vec![];
        for (index, function) in program.functions.iter().enumerate() {
            if operations.contains_key(&FunctionId(index as u32)) {
                continue;
            }
            for parameter in &function.parameters {
                if !shapes.contains_key(&parameter.monotype) || readers.contains(&parameter.id) {
                    continue;
                }
                let mut reads = Reads { program, operations, readers: &readers };
                let scope = Scope::Expression(&function.body);
                if uniqueness::is_only_read(&mut reads, parameter.id, scope) {
                    found.push(parameter.id);
                }
            }
        }
        if found.is_empty() {
            return readers;
        }
        readers.extend(found);
    }
}

/// Whether the argument is a map that a call reads and keeps nothing of: a map operation that
/// reads, the keys `difference` takes away, or a parameter that only reads.
fn read_by(
    program: &Program,
    operations: &FxHashMap<FunctionId, MapOperation>,
    readers: &FxHashSet<LocalId>,
    call: &Expression,
    argument: &Expression,
) -> bool {
    let ExpressionKind::Apply { function, arguments } = &call.kind else { return false };
    let position = arguments.iter().position(|other| std::ptr::eq(other, argument));
    let Some(position) = position else { return false };
    if let Some(operation) = map_operation(operations, function, arguments) {
        return match operation {
            MapOperation::Difference => position == 1,
            operation => operation.reads() && operation.map_position() == Some(position),
        };
    }
    let ExpressionKind::Function(id) = function.kind else { return false };
    let parameters = &program.function(id).parameters;
    parameters.len() == arguments.len() && readers.contains(&parameters[position].id)
}

/// Whether the call is an array iteration that runs a callback on the spot.
fn runs_callback_now(call: &Expression, callback: &Expression) -> bool {
    let ExpressionKind::Foreign { foreign: Foreign::Call { boundary, .. }, .. } = &call.kind else {
        return false;
    };
    boundary.iteration.is_some() && matches!(callback.kind, ExpressionKind::Lambda { .. })
}

/// The uniqueness framework's view of the map operations: those that read a map only peek at it.
struct Reads<'o> {
    program: &'o Program,
    operations: &'o FxHashMap<FunctionId, MapOperation>,
    readers: &'o FxHashSet<LocalId>,
}

impl Shapes for Reads<'_> {
    fn inspects(&mut self, call: &Expression, argument: &Expression) -> bool {
        read_by(self.program, self.operations, self.readers, call, argument)
    }

    fn is_spine(&mut self, _cell: MonotypeId, _field: MonotypeId) -> bool {
        false
    }

    fn passes_locals_last(&self) -> bool {
        true
    }

    fn runs_now(&mut self, call: &Expression, callback: &Expression) -> bool {
        runs_callback_now(call, callback)
    }

    fn effects_only_peek(&self) -> bool {
        true
    }

    fn closures_keep_what_they_read(&self) -> bool {
        true
    }
}

/// The order of a Go map's uses, once it is known where it becomes a tree: a conversion is the
/// local's consumption, every write and hand-over a peek, and every read nothing, so that a
/// local is linear exactly when nothing writes or hands on the map after it was converted.
struct Ordering<'o> {
    program: &'o Program,
    operations: &'o FxHashMap<FunctionId, MapOperation>,
    readers: &'o FxHashSet<LocalId>,
    to_tree: &'o FxHashSet<*const Expression>,
}

impl Shapes for Ordering<'_> {
    fn inspects(&mut self, call: &Expression, argument: &Expression) -> bool {
        if self.to_tree.contains(&std::ptr::from_ref(argument)) {
            return false;
        }
        matches!(call.kind, ExpressionKind::Apply { .. } | ExpressionKind::Foreign { .. })
    }

    fn ignores(&mut self, call: &Expression, argument: &Expression) -> bool {
        !self.to_tree.contains(&std::ptr::from_ref(argument))
            && read_by(self.program, self.operations, self.readers, call, argument)
    }

    fn is_spine(&mut self, _cell: MonotypeId, _field: MonotypeId) -> bool {
        false
    }

    fn passes_locals_last(&self) -> bool {
        true
    }

    fn runs_now(&mut self, call: &Expression, callback: &Expression) -> bool {
        runs_callback_now(call, callback)
    }

    fn effects_only_peek(&self) -> bool {
        true
    }

    fn closures_keep_what_they_read(&self) -> bool {
        true
    }
}
