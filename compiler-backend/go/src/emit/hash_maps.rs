//! Which `Data.Map`s are Go maps: those the program owns along their whole life and only builds,
//! updates and queries by key ([`crate::maps`]).
//!
//! A map value goes through the program as a *web*: the locals, parameters and results it is
//! bound to, the map operations that update it, the branches that choose between versions of it
//! and the folds that carry it. A web is a Go map when
//!
//! - every operation on it is one a Go map does ([`MapOperation`]), at a key whose `Ord` is
//!   Go's `==` and sort;
//! - every local it is bound to is used linearly ([`uniqueness::is_unique`]): read by those
//!   operations, then passed on at most once, so that no version is seen after the next one
//!   was made from it in place;
//! - it is made by those operations, or is a fold's seed that the fold then owns.
//!
//! Anything else a version of the map meets, a function that walks the tree or a value that
//! keeps it, takes the tree: the map's entries are sorted once by key and built into a balanced
//! tree there, a value of its own that nothing writes. Nothing writes or hands on the map after
//! it was converted ([`Ordering`]), so that it is converted at most once on its way. A fold that
//! starts from a tree turns it into a Go map first, and owns that map.

use rustc_hash::{FxHashMap, FxHashSet};
use smol_str::SmolStr;

use super::uniqueness::{self, Forced, Scope, Shapes};
use crate::foreign::{Foreign, Iteration};
use crate::maps::MapOperation;
use crate::monomorphic::traversal::for_each_child;
use crate::monomorphic::{
    Alternative, Binding, Expression, ExpressionKind, Function, FunctionId, Guard, Guarded, Local,
    LocalId, Program,
};
use crate::monotype::MonotypeId;

/// The names of the map operations that some Go map does.
pub(crate) fn operations_used(
    program: &Program,
    operations: &FxHashMap<FunctionId, MapOperation>,
) -> FxHashSet<SmolStr> {
    if operations.is_empty() || !uniqueness::enabled() {
        return FxHashSet::default();
    }
    let shapes = map_shapes(program, operations);
    let readers = readers(program, operations, &shapes);
    let mut finder = Webs::new(program, operations, &shapes, &readers);
    finder.find();
    let decided = finder.decide();
    decided
        .calls
        .iter()
        .filter(|&&(_, node)| decided.is_native(node))
        .map(|&(id, _)| program.function(id).name.clone())
        .collect()
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

/// A place a map value is bound to or made at.
type Node = usize;

#[derive(Clone, Copy, PartialEq, Eq)]
enum Flow {
    /// An argument to a function's parameter.
    Argument,
    /// A fold's seed, to the accumulator the fold owns.
    Seed,
}

struct SoftEdge {
    from: Node,
    to: Node,
    flow: Flow,
    at: *const Expression,
}

/// What the program does with its map values, as webs of nodes.
struct Webs<'p> {
    program: &'p Program,
    operations: &'p FxHashMap<FunctionId, MapOperation>,
    shapes: &'p FxHashMap<MonotypeId, MapShape>,
    readers: &'p FxHashSet<LocalId>,
    parents: Vec<Node>,
    /// Whether the node must be a tree: it is made or used in a way only the tree does.
    tree: Vec<bool>,
    locals: FxHashMap<LocalId, Node>,
    results: FxHashMap<FunctionId, Node>,
    /// The node of every map-typed expression.
    expressions: FxHashMap<*const Expression, Node>,
    /// The map-typed expressions whose value goes somewhere only a tree may go.
    escapes: Vec<(Node, *const Expression)>,
    soft: Vec<SoftEdge>,
    /// The nodes that a map operation reads or writes.
    operated: Vec<Node>,
    /// The locals a map is bound to, with the code they are used in.
    slots: Vec<(Node, LocalId, *const Expression)>,
    /// The map operations the program calls, each with the node of the map it works on.
    calls: Vec<(FunctionId, Node)>,
}

/// The webs that are Go maps, and where values change representation.
struct Decided {
    native_nodes: FxHashSet<Node>,
    expressions: FxHashMap<*const Expression, Node>,
    locals: FxHashMap<LocalId, Node>,
    results: FxHashMap<FunctionId, Node>,
    /// Map-typed expressions whose Go map becomes a tree there.
    to_tree: FxHashSet<*const Expression>,
    /// Map-typed expressions whose tree becomes a Go map there.
    from_tree: FxHashSet<*const Expression>,
    parents: Vec<Node>,
    calls: Vec<(FunctionId, Node)>,
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
}

impl<'p> Webs<'p> {
    fn new(
        program: &'p Program,
        operations: &'p FxHashMap<FunctionId, MapOperation>,
        shapes: &'p FxHashMap<MonotypeId, MapShape>,
        readers: &'p FxHashSet<LocalId>,
    ) -> Webs<'p> {
        Webs {
            program,
            operations,
            shapes,
            readers,
            parents: vec![],
            tree: vec![],
            locals: FxHashMap::default(),
            results: FxHashMap::default(),
            expressions: FxHashMap::default(),
            escapes: vec![],
            soft: vec![],
            operated: vec![],
            slots: vec![],
            calls: vec![],
        }
    }

    fn is_map(&self, monotype: MonotypeId) -> bool {
        self.shapes.contains_key(&monotype)
    }

    fn fresh(&mut self, tree: bool) -> Node {
        let node = self.parents.len();
        self.parents.push(node);
        self.tree.push(tree);
        node
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

    fn force_tree(&mut self, node: Node) {
        let root = self.root(node);
        self.tree[root] = true;
    }

    fn local(&mut self, id: LocalId) -> Node {
        if let Some(&node) = self.locals.get(&id) {
            return node;
        }
        let node = self.fresh(false);
        self.locals.insert(id, node);
        node
    }

    fn result(&mut self, id: FunctionId) -> Node {
        if let Some(&node) = self.results.get(&id) {
            return node;
        }
        let node = self.fresh(false);
        self.results.insert(id, node);
        node
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
            if self.is_map(parameter.monotype) {
                let node = self.local(parameter.id);
                self.require_linear(node, parameter.id, &function.body);
            }
        }
        if self.is_map(function.result) {
            let body = self.value(&function.body);
            let result = self.result(id);
            self.join(body, result);
            if function.parameters.is_empty() {
                // A constant is one value that every use shares.
                self.force_tree(result);
            }
        } else {
            self.expression(&function.body);
        }
    }

    fn require_linear(&mut self, node: Node, local: LocalId, scope: &'p Expression) {
        self.slots.push((node, local, std::ptr::from_ref(scope)));
        let mut shapes =
            Reads { program: self.program, operations: self.operations, readers: self.readers };
        if !uniqueness::is_unique(
            &mut shapes,
            local,
            &[],
            Scope::Expression(scope),
            &Forced::default(),
        ) {
            self.force_tree(node);
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
            if self.is_map(parameter.monotype) {
                let node = self.local(parameter.id);
                self.force_tree(node);
            }
        }
        if self.is_map(function.result) {
            let node = self.result(id);
            self.force_tree(node);
        }
    }

    /// The node of a map-typed expression's value.
    fn value(&mut self, expression: &'p Expression) -> Node {
        let node = self.value_unrecorded(expression);
        self.expressions.insert(std::ptr::from_ref(expression), node);
        node
    }

    fn value_unrecorded(&mut self, expression: &'p Expression) -> Node {
        match &expression.kind {
            ExpressionKind::Local(id) => self.local(*id),
            ExpressionKind::Function(id) => match self.operations.get(id) {
                Some(MapOperation::Empty) => {
                    let node = self.fresh(false);
                    self.calls.push((*id, node));
                    node
                }
                _ => {
                    let function = self.program.function(*id);
                    if function.parameters.is_empty() { self.result(*id) } else { self.fresh(true) }
                }
            },
            ExpressionKind::Apply { function, arguments } => {
                if let Some(operation) = self.operation(function, arguments) {
                    return self.operation_value(function, operation, arguments);
                }
                if let Some(id) = self.called(function, arguments.len()) {
                    self.arguments(id, arguments);
                    let result = self.result(id);
                    let answer = self.fresh(false);
                    let at = std::ptr::from_ref(expression);
                    self.soft.push(SoftEdge { from: result, to: answer, flow: Flow::Argument, at });
                    return answer;
                }
                self.expression_children(expression);
                self.fresh(true)
            }
            ExpressionKind::Let { bindings, body } => {
                self.bindings(expression, bindings);
                self.value(body)
            }
            ExpressionKind::If { condition, then, otherwise } => {
                self.expression(condition);
                let then = self.value(then);
                let otherwise = self.value(otherwise);
                self.join(then, otherwise)
            }
            ExpressionKind::Case { scrutinees, alternatives } => {
                self.scrutinees(scrutinees, alternatives);
                let mut joined = None;
                for body in alternative_bodies(alternatives) {
                    let node = self.value(body);
                    joined = Some(match joined {
                        Some(joined) => self.join(joined, node),
                        None => node,
                    });
                }
                joined.unwrap_or_else(|| self.fresh(true))
            }
            ExpressionKind::Foreign { foreign, arguments } if is_fold_left(foreign, arguments) => {
                self.fold(arguments)
            }
            _ => {
                self.expression_children(expression);
                self.fresh(true)
            }
        }
    }

    fn operation_value(
        &mut self,
        function: &Expression,
        operation: MapOperation,
        arguments: &'p [Expression],
    ) -> Node {
        let node = self.operation_node(operation, arguments);
        if let ExpressionKind::Function(id) = function.kind {
            self.calls.push((id, node));
        }
        node
    }

    fn operation_node(&mut self, operation: MapOperation, arguments: &'p [Expression]) -> Node {
        let map = operation.map_position();
        for (position, argument) in arguments.iter().enumerate() {
            if Some(position) != map && !(operation == MapOperation::Difference && position == 1) {
                self.expression(argument);
            }
        }
        let Some(position) = map else { return self.fresh(false) };
        let node = self.value(&arguments[position]);
        self.operated.push(node);
        if operation == MapOperation::Difference {
            // The keys to take away are read, as a Go map when the map is one.
            let other = &arguments[1];
            let removed = self.value(other);
            self.operated.push(removed);
            let at = std::ptr::from_ref(other);
            self.soft.push(SoftEdge { from: removed, to: node, flow: Flow::Seed, at });
        }
        node
    }

    fn arguments(&mut self, id: FunctionId, arguments: &'p [Expression]) {
        let parameters = &self.program.function(id).parameters;
        for (argument, parameter) in arguments.iter().zip(parameters) {
            if self.is_map(argument.monotype) && argument.monotype == parameter.monotype {
                let from = self.value(argument);
                let to = self.local(parameter.id);
                let at = std::ptr::from_ref(argument);
                self.soft.push(SoftEdge { from, to, flow: Flow::Argument, at });
            } else {
                self.expression(argument);
            }
        }
    }

    /// `foldl (\accumulator element -> ...) seed array`, whose accumulator is one map.
    fn fold(&mut self, arguments: &'p [Expression]) -> Node {
        let [callback, seed, array] = arguments else { unreachable!() };
        let ExpressionKind::Lambda { parameters, body } = &callback.kind else { unreachable!() };
        let fold = self.fresh(false);
        let seeded = self.value(seed);
        let at = std::ptr::from_ref(seed);
        self.soft.push(SoftEdge { from: seeded, to: fold, flow: Flow::Seed, at });
        let accumulator = self.local(parameters[0].id);
        self.join(accumulator, fold);
        self.require_linear(accumulator, parameters[0].id, body);
        if self.is_map(parameters[1].monotype) {
            let element = self.local(parameters[1].id);
            self.force_tree(element);
        }
        let stepped = self.value(body);
        self.join(stepped, fold);
        self.expression(array);
        fold
    }

    fn bindings(&mut self, scope: &'p Expression, bindings: &'p [Binding]) {
        for binding in bindings {
            if self.is_map(binding.local.monotype) {
                let value = self.value(&binding.value);
                let local = self.local(binding.local.id);
                self.join(value, local);
                self.require_linear(local, binding.local.id, scope);
            } else {
                self.expression(&binding.value);
            }
        }
    }

    fn scrutinees(&mut self, scrutinees: &'p [Expression], alternatives: &'p [Alternative]) {
        for scrutinee in scrutinees {
            if self.is_map(scrutinee.monotype) {
                let node = self.value(scrutinee);
                self.force_tree(node);
            } else {
                self.expression(scrutinee);
            }
        }
        for alternative in alternatives {
            let mut bound = vec![];
            alternative.for_each_local(&mut |local| bound.push(local.clone()));
            for local in bound {
                if self.is_map(local.monotype) {
                    let node = self.local(local.id);
                    self.force_tree(node);
                }
            }
            if let Guarded::Guards(branches) = &alternative.body {
                for guard in branches.iter().flat_map(|branch| &branch.guards) {
                    match guard {
                        Guard::Boolean(condition) => self.expression(condition),
                        Guard::Pattern { value, .. } => self.expression(value),
                    }
                }
            }
        }
    }

    /// An expression whose value, if it is a map, goes somewhere only a tree may go.
    fn expression(&mut self, expression: &'p Expression) {
        if self.is_map(expression.monotype) {
            let node = self.value(expression);
            self.escapes.push((node, std::ptr::from_ref(expression)));
            return;
        }
        match &expression.kind {
            ExpressionKind::Function(id) => self.opaque_function(*id),
            ExpressionKind::Apply { function, arguments } => {
                if let Some(operation) = self.operation(function, arguments) {
                    self.operation_value(function, operation, arguments);
                    return;
                }
                if let Some(id) = self.called(function, arguments.len()) {
                    self.arguments(id, arguments);
                    return;
                }
                self.expression_children(expression);
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
            if self.is_map(local.monotype) {
                let node = self.local(local.id);
                self.force_tree(node);
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
            let settled = self.settle();
            let mut forced = vec![];
            for &(node, local, scope) in &self.slots {
                let root = root_of(&mut self.parents, node);
                if settled.tree[root] {
                    continue;
                }
                let mut shapes = Ordering {
                    program: self.program,
                    operations: self.operations,
                    readers: self.readers,
                    to_tree: &settled.to_tree,
                };
                // SAFETY of the pointer: the program is borrowed for the whole analysis.
                let scope = unsafe { &*scope };
                let ordered = uniqueness::is_unique(
                    &mut shapes,
                    local,
                    &[],
                    Scope::Expression(scope),
                    &Forced::default(),
                );
                if !ordered {
                    forced.push(node);
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
    /// tree reaches a parameter of it; a Go map reaching a tree's parameter, and every escape of
    /// one, becomes a tree there; a tree that seeds a fold that is a Go map becomes one there.
    fn settle(&mut self) -> Settled {
        let mut tree: Vec<bool> = (0..self.parents.len())
            .map(|node| {
                let root = self.root(node);
                self.tree[root]
            })
            .collect();
        loop {
            let mut changed = false;
            for edge in &self.soft {
                let from = root_of(&mut self.parents, edge.from);
                let to = root_of(&mut self.parents, edge.to);
                if edge.flow == Flow::Argument && tree[from] && !tree[to] {
                    tree[to] = true;
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }
        self.drop_idle_webs(&mut tree);
        let mut to_tree = FxHashSet::default();
        let mut from_tree = FxHashSet::default();
        for &(node, at) in &self.escapes {
            let root = root_of(&mut self.parents, node);
            if !tree[root] {
                to_tree.insert(at);
            }
        }
        for edge in &self.soft {
            let from = root_of(&mut self.parents, edge.from);
            let to = root_of(&mut self.parents, edge.to);
            match (tree[from], tree[to]) {
                (false, true) => {
                    to_tree.insert(edge.at);
                }
                (true, false) => {
                    from_tree.insert(edge.at);
                }
                _ => {}
            }
        }
        Settled { tree, to_tree, from_tree }
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
            to_tree: settled.to_tree,
            from_tree: settled.from_tree,
            parents: self.parents,
            calls: self.calls,
        }
    }
}

struct Settled {
    tree: Vec<bool>,
    to_tree: FxHashSet<*const Expression>,
    from_tree: FxHashSet<*const Expression>,
}

impl Webs<'_> {
    /// Keeps as trees the Go maps that no map operation reads or writes, wherever they flow:
    /// made empty and converted, they would only cost the conversion.
    fn drop_idle_webs(&mut self, tree: &mut [bool]) {
        let mut groups: Vec<Node> = (0..self.parents.len()).collect();
        for edge in &self.soft {
            let from = root_of(&mut self.parents, edge.from);
            let to = root_of(&mut self.parents, edge.to);
            if !tree[from] && !tree[to] {
                let (from, to) = (root_of(&mut groups, from), root_of(&mut groups, to));
                groups[to] = from;
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
}
