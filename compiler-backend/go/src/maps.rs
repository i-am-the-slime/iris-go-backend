//! The operations of `Data.Map` that a Go map does as well as the persistent tree, at the key
//! types whose `Ord` agrees with Go's `==`.
//!
//! A `Map k v` that the program owns along its whole life and only builds, updates and queries
//! by key can be a Go `map[K]V` instead of the balanced tree ([`crate::emit`] decides which ones
//! are). The tree's ordered walks are then a sort of the keys away. These operations are called
//! as functions until then, rather than copied into their callers, so that every use of a map
//! still says what it does.

use checking::TypeId;
use checking::core::Type;
use rustc_hash::{FxHashMap, FxHashSet};
use smol_str::SmolStr;

use crate::context::Context;
use crate::modules::Modules;
use crate::monomorphic::traversal::visit;
use crate::monomorphic::{
    ExpressionKind, FunctionId, FunctionSpelling, Guard, Guarded, Pattern, PatternKind, Program,
};
use crate::monotype::{DataType, Monotype, MonotypeId, Monotypes};

/// A `Data.Map.Internal` function that a Go map does by hashing the key.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum MapOperation {
    Empty,
    Singleton,
    Insert,
    InsertWith,
    Delete,
    Lookup,
    Member,
    Alter,
    Update,
    Size,
    IsEmpty,
    /// `difference m other`: `m` without the keys of `other`, a map of the same type.
    Difference,
}

impl MapOperation {
    fn named(name: &str) -> Option<MapOperation> {
        Some(match name {
            "empty" => MapOperation::Empty,
            "singleton" => MapOperation::Singleton,
            "insert" => MapOperation::Insert,
            "insertWith" => MapOperation::InsertWith,
            "delete" => MapOperation::Delete,
            "lookup" => MapOperation::Lookup,
            "member" => MapOperation::Member,
            "alter" => MapOperation::Alter,
            "update" => MapOperation::Update,
            "size" => MapOperation::Size,
            "isEmpty" => MapOperation::IsEmpty,
            "difference" => MapOperation::Difference,
            _ => return None,
        })
    }

    /// The position of the map among the operation's parameters, once it takes them all.
    pub fn map_position(self) -> Option<usize> {
        match self {
            MapOperation::Empty | MapOperation::Singleton => None,
            MapOperation::Size | MapOperation::IsEmpty | MapOperation::Difference => Some(0),
            MapOperation::Lookup | MapOperation::Member | MapOperation::Delete => Some(1),
            MapOperation::Insert | MapOperation::Alter | MapOperation::Update => Some(2),
            MapOperation::InsertWith => Some(3),
        }
    }

    /// The number of parameters the operation takes.
    pub fn arity(self) -> usize {
        match self {
            MapOperation::Empty => 0,
            MapOperation::Singleton | MapOperation::Difference => 2,
            operation => operation.map_position().map_or(0, |position| position + 1),
        }
    }

    /// Whether the operation only reads the map it is given.
    pub fn reads(self) -> bool {
        matches!(
            self,
            MapOperation::Lookup
                | MapOperation::Member
                | MapOperation::Size
                | MapOperation::IsEmpty
        )
    }
}

/// The functions of the program that are [`MapOperation`]s at a key type Go compares as
/// PureScript does.
pub fn hash_operations<Q>(
    program: &Program,
    monotypes: &Monotypes,
    modules: &Modules,
    context: &mut Context<'_, Q>,
) -> FxHashMap<FunctionId, MapOperation>
where
    Q: checking::ExternalQueries,
{
    let shaped = shaped_maps(program, monotypes, modules, context);
    let celled = celled_maps(monotypes);
    let mut operations = FxHashMap::default();
    for (index, function) in program.functions.iter().enumerate() {
        let Some(origin) = function.origin else { continue };
        let Some(module) = modules.index(origin) else { continue };
        if modules.name(module) != MAP_MODULE {
            continue;
        }
        let Some(FunctionSpelling::Specialized { name, types, .. }) =
            monotypes.function_spellings.get(&function.name)
        else {
            continue;
        };
        let Some(operation) = MapOperation::named(name) else { continue };
        let Some(&key) = types.first() else { continue };
        if !is_hashable_key(context, key) {
            continue;
        }
        // Unsimplified, the operation may take its arguments one at a time.
        let mut arguments: Vec<MonotypeId> =
            function.parameters.iter().map(|parameter| parameter.monotype).collect();
        let mut result = function.result;
        while let Some((argument, rest)) = monotypes.function_parts(result) {
            arguments.push(argument);
            result = rest;
        }
        let map = match operation.map_position() {
            Some(position) => arguments.get(position).copied().unwrap_or(result),
            None => result,
        };
        if matches!(monotypes.get(map), Monotype::Data(data) if shaped.contains(data))
            || celled.contains(&map)
        {
            continue;
        }
        operations.insert(FunctionId(index as u32), operation);
    }
    operations
}

/// The map types that the program keeps in mutable cells. Every read of a cell shares its map,
/// so none of them is a Go map, and keeping their operations as calls would only cost a second
/// simplification.
fn celled_maps(monotypes: &Monotypes) -> FxHashSet<MonotypeId> {
    monotypes
        .ids()
        .filter_map(|id| match monotypes.get(id) {
            Monotype::Reference(held) | Monotype::MutableArray(held) => Some(*held),
            _ => None,
        })
        .collect()
}

/// The map types whose trees the program builds or takes apart itself, outside
/// `Data.Map.Internal`, or shows as trees: a tree that a Go map is turned back into is balanced
/// its own way, which only they could tell.
fn shaped_maps<Q>(
    program: &Program,
    monotypes: &Monotypes,
    modules: &Modules,
    context: &mut Context<'_, Q>,
) -> FxHashSet<DataType>
where
    Q: checking::ExternalQueries,
{
    let mut shaped = FxHashSet::default();
    let Some(map_module) = modules.indices().find(|&module| modules.name(module) == MAP_MODULE)
    else {
        return shaped;
    };
    let map_file = modules.file(map_module);
    let mut is_map = |data: &DataType| {
        data.file_id == map_file
            && context.type_name(data.file_id, data.item).is_ok_and(|name| name == "Map")
    };
    for function in &program.functions {
        let inside = function.origin == Some(map_file);
        let shows_tree = inside
            && matches!(
                monotypes.function_spellings.get(&function.name),
                Some(FunctionSpelling::Specialized { name, .. }) if name == "showTree"
            );
        if shows_tree {
            for parameter in &function.parameters {
                if let Monotype::Data(data) = monotypes.get(parameter.monotype)
                    && is_map(data)
                {
                    shaped.insert(data.clone());
                }
            }
            continue;
        }
        if inside {
            continue;
        }
        let mut found = vec![];
        visit(&function.body, &mut |expression| match &expression.kind {
            ExpressionKind::Construct { data, .. } => found.push(data.clone()),
            ExpressionKind::Case { alternatives, .. } => {
                for alternative in alternatives {
                    for pattern in &alternative.patterns {
                        pattern_data(pattern, &mut found);
                    }
                    if let Guarded::Guards(branches) = &alternative.body {
                        for guard in branches.iter().flat_map(|branch| &branch.guards) {
                            if let Guard::Pattern { pattern, .. } = guard {
                                pattern_data(pattern, &mut found);
                            }
                        }
                    }
                }
            }
            _ => {}
        });
        shaped.extend(found.into_iter().filter(|data| is_map(data)));
    }
    shaped
}

fn pattern_data(pattern: &Pattern, found: &mut Vec<DataType>) {
    match &pattern.kind {
        PatternKind::Constructor { data, arguments, .. } => {
            found.push(data.clone());
            arguments.iter().for_each(|argument| pattern_data(argument, found));
        }
        PatternKind::Named { pattern, .. } => pattern_data(pattern, found),
        PatternKind::Array(patterns) | PatternKind::Closure { captures: patterns, .. } => {
            patterns.iter().for_each(|pattern| pattern_data(pattern, found));
        }
        PatternKind::Record(fields) => {
            fields.iter().for_each(|(_, pattern)| pattern_data(pattern, found));
        }
        PatternKind::Wildcard | PatternKind::Variable(_) | PatternKind::Literal(_) => {}
    }
}

/// Whether Go's `==` on the key's Go type is the key's `Eq`, and sorting by its `Ord` is a sort
/// Go can do: `Int`, `Char` and `String`.
fn is_hashable_key<Q>(context: &mut Context<'_, Q>, key: TypeId) -> bool
where
    Q: checking::ExternalQueries,
{
    let key = context.types.strip_annotations(key);
    let Type::Constructor(file_id, item) = context.types.lookup(key).clone() else {
        return false;
    };
    if file_id != context.queries.prim_id() {
        return false;
    }
    let Ok(name) = context.type_name(file_id, item) else { return false };
    matches!(name.as_str(), "Int" | "Char" | "String")
}

/// What a Go map does for a [`MapOperation`] of a map in that representation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum HashMapOperation {
    /// `make(map[K]V, n)`, of the number of entries it is made for.
    New,
    /// `map[K]V{k: v}`, of the key and the value.
    Singleton,
    /// `m[k] = v`, of the key, the value and the map, which it answers.
    Insert,
    /// `delete(m, k)`, of the key and the map, which it answers.
    Delete,
    /// `m[k]` as a `Maybe`, of the key and the map.
    Lookup,
    /// Whether the map holds the key, of the key and the map.
    Member,
    /// `len(m)`.
    Size,
    /// `len(m) == 0`.
    IsEmpty,
    /// `m[k]` of a key the map holds, of the key and the map.
    Get,
    /// `for k := range other { delete(m, k) }`, of the map and the other, which it answers.
    Difference,
}

impl HashMapOperation {
    pub fn arity(self) -> usize {
        match self {
            HashMapOperation::New | HashMapOperation::Size | HashMapOperation::IsEmpty => 1,
            HashMapOperation::Singleton
            | HashMapOperation::Delete
            | HashMapOperation::Lookup
            | HashMapOperation::Member
            | HashMapOperation::Get
            | HashMapOperation::Difference => 2,
            HashMapOperation::Insert => 3,
        }
    }
}

/// The map operations of a program by their names, which survive simplification's renumbering
/// of the functions.
#[derive(Default)]
pub struct KeptOperations {
    names: FxHashMap<SmolStr, MapOperation>,
}

impl KeptOperations {
    pub fn new(program: &Program, operations: &FxHashMap<FunctionId, MapOperation>) -> Self {
        let names = operations
            .iter()
            .map(|(&id, &operation)| (program.function(id).name.clone(), operation))
            .collect();
        KeptOperations { names }
    }

    pub fn is_empty(&self) -> bool {
        self.names.is_empty()
    }

    /// Keeps only the operations of the given functions.
    pub fn retain(&mut self, names: &rustc_hash::FxHashSet<SmolStr>) {
        self.names.retain(|name, _| names.contains(name));
    }

    pub fn keeps(&self, name: &str) -> bool {
        self.names.contains_key(name)
    }

    /// The map operations among the functions of the program, as it stands now.
    pub fn find(
        &self,
        program: &Program,
        modules: &Modules,
    ) -> FxHashMap<FunctionId, MapOperation> {
        let mut operations = FxHashMap::default();
        if self.names.is_empty() {
            return operations;
        }
        for (index, function) in program.functions.iter().enumerate() {
            let Some(&operation) = self.names.get(&function.name) else { continue };
            let Some(module) = function.origin.and_then(|origin| modules.index(origin)) else {
                continue;
            };
            if modules.name(module) == MAP_MODULE {
                operations.insert(FunctionId(index as u32), operation);
            }
        }
        operations
    }
}

const MAP_MODULE: &str = "Data.Map.Internal";
