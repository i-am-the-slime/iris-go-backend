//! Rendering of the simplified monomorphic tree as Go.
//! Values of type `Effect a` are Go `func() A`, and a function `a -> Effect b` is a
//! Go `func(A) B` that performs its effects when called. Effectful code is emitted
//! in perform mode, where binds become statements and `pure x` becomes `x`; an
//! effect only turns into a closure where it is used as a first-class value.

mod application;
mod blocks;
mod buffers;
mod cases;
mod chunks;
mod closures;
mod coerce;
mod conventions;
mod constructors;
mod deduplicate;
mod diverging;
mod fusion;
mod groups;
mod instantiations;
mod iteration;
mod layout;
mod lengths;
mod locals;
mod names;
mod ownership;
mod packages;
mod ranges;
mod reference_equality;
mod reuse;
mod types;
mod unreferenced;
mod views;

use std::collections::BTreeSet;

use rustc_hash::{FxHashMap, FxHashSet};

use files::FileId;
use indexing::TermItemId;

use self::application::Callable;
use self::packages::Spelling;
use crate::arity::Arities;
use crate::context::Context;
use crate::error::{GoError, GoResult};
use crate::foreign::{
    Boundary, Comparison, Constructed, Foreign, ForeignPackages, GoFunction, GoPackage, Operator,
};
use crate::modules::{ModuleIndex, Modules};
use crate::mono::{
    Binding, Expression, ExpressionKind, Function, FunctionId, Guard, Guarded,
    Literal, Local, LocalId, Pattern, PatternKind, Program, RecordUpdate,
};
use crate::monotype::{DataType, Monotype, MonotypeId, Monotypes};
use crate::naming::{capitalise, exported, identifier, numbered};
use crate::graph::{on_cycles, strongly_connected};
use crate::simplify::{reference_graph, visit};
use crate::syntax::{
    GoCase, GoDeclaration, GoExpression, GoStatement, GoType, Name, statements_names,
};
use crate::timing::timed;

pub(crate) use self::closures::Eliminators;
pub use self::packages::GoSourceFile;

pub fn emit_program<Q>(
    mut program: Program,
    monotypes: &mut Monotypes,
    eliminators: &Eliminators,
    queries: &Q,
    foreign_packages: &ForeignPackages,
    modules: &Modules,
    module_path: &str,
) -> GoResult<Vec<GoSourceFile>>
where
    Q: checking::ExternalQueries,
{
    let arities = crate::arity::choose(&program, monotypes);
    let closure_sets = timed("closures", || {
        closures::defunctionalize(&mut program, monotypes, queries, &arities, eliminators)
    })?;
    let program = &program;
    let reused = timed("reuse", || {
        let mut probe =
            Emitter::new(program, monotypes, queries, foreign_packages, arities.clone());
        reuse::reuse_cells(program, &mut probe)
    });
    let program = &reused.program;
    let mut emitter = Emitter::new(program, monotypes, queries, foreign_packages, arities);
    emitter.materialized = reused.materialized;
    emitter.closure_sets = closure_sets;
    emitter.assign_function_names();
    let groups = timed("groups", || {
        groups::tail_call_groups(program, emitter.monotypes, &emitter.lazy_constants)
    });
    emitter.name_tail_groups(groups);
    let entry_origin = program.function(program.entry).origin;
    let declarations = timed("functions", || {
        let mut declarations = vec![];
        for index in 0..program.functions.len() {
            let id = FunctionId(index as u32);
            let emitted = emitter.function(id)?;
            emitter.note_homes(&emitted, program.function(id).origin);
            declarations.extend(emitted);
        }
        while let Some((id, position)) = emitter.pending_owning_variants.pop() {
            let emitted = emitter.owning_variant(id, position)?;
            emitter.note_homes(&emitted, program.function(id).origin);
            declarations.extend(emitted);
        }
        let main = emitter.main()?;
        emitter.note_homes(main.as_slice(), entry_origin);
        declarations.extend(main);
        GoResult::Ok(declarations)
    });
    let mut declarations = declarations?;
    let unused = emitter.unused_tail_group_entries();
    if !unused.is_empty() {
        declarations.retain(|declaration| declaration.name().is_none_or(|n| !unused.contains(n)));
    }
    if emitter.entry_performs_effects() {
        emitter.imports.insert(GoPackage::Exception.path().into());
        report_uncaught_exceptions(&mut declarations);
    }
    if emitter.imports.contains(GoPackage::Aff.path()) {
        await_fibers(&mut declarations);
    }
    timed("ranges", || ranges::read_elements_in_place(&mut declarations));
    let taken =
        |name: &str| emitter.global_names.contains(name) || IMPORTED_PACKAGES.contains(&name);
    timed("lengths", || lengths::count_lengths_up_to_comparisons(&mut declarations));
    timed("invariant lengths", || lengths::hoist_loop_invariant_lengths(&mut declarations, &taken));
    let chunked =
        timed("chunks", || chunks::allocate_linked_cells_in_chunks(&mut declarations, &taken));
    if chunked {
        emitter.imports.insert(GoPackage::Alloc.path().into());
    }
    timed("blocks", || blocks::allocate_nested_cells_together(&mut declarations, &taken));
    timed("divergence", || diverging::end_blocks_at_divergence(&mut declarations));
    timed("unreferenced", || unreferenced::drop_unreferenced_definitions(&mut declarations));
    let mut homes: FxHashMap<String, ModuleIndex> = std::mem::take(&mut emitter.homes)
        .into_iter()
        .filter_map(|(name, file)| Some((name, modules.index(file)?)))
        .collect();
    // The homes of the declarations each declaration stands for.
    let mut merged: FxHashMap<String, Vec<Option<ModuleIndex>>> = FxHashMap::default();
    let declarations = timed("deduplicate", || {
        deduplicate::merge_identical_declarations(declarations, &mut |from, into| {
            let from_homes = merged.remove(from).unwrap_or_else(|| vec![homes.get(from).copied()]);
            merged
                .entry(into.to_string())
                .or_insert_with(|| vec![homes.get(into).copied()])
                .extend(from_homes);
        })
    });
    for (name, merged_homes) in merged {
        match modules.common_home(&merged_homes) {
            Some(home) => homes.insert(name, home),
            None => homes.remove(&name),
        };
    }
    let home = |declaration: &GoDeclaration| {
        let name = match declaration {
            GoDeclaration::Constants { names, .. } => names.first().map(String::as_str),
            declaration => declaration.name(),
        };
        name.and_then(|name| homes.get(name)).copied()
    };
    emitter.settle_round_trips();
    let mut all = std::mem::take(&mut emitter.type_declarations);
    all.extend(declarations);
    let all: Vec<(GoDeclaration, Option<ModuleIndex>)> = all
        .into_iter()
        .map(|declaration| {
            let home = home(&declaration);
            (declaration, home)
        })
        .collect();
    let declared: FxHashSet<String> = all
        .iter()
        .flat_map(|(declaration, _)| match declaration {
            GoDeclaration::Constants { names, .. } => names.clone(),
            declaration => declaration.name().map(str::to_string).into_iter().collect(),
        })
        .collect();
    timed("names", || emitter.spell_pending(modules, &declared))?;
    let typed_records: Vec<Option<String>> = emitter
        .typed_records
        .iter()
        .map(|monotype| emitter.record_names.get(monotype).cloned())
        .collect();
    let packaging = packages::Packaging {
        modules,
        module_path,
        spellings: &emitter.spellings,
        imports: &emitter.imports,
        typed_records: &typed_records,
    };
    let files = timed("packages", || packaging.split(all))?;
    if std::env::var_os("IRIS_GO_ANY_CENSUS").is_some() {
        let mut census = crate::erasure::Census::default();
        let mut textual = 0;
        for file in &files {
            let (source, file_census) = file.file.render_with_census();
            census.absorb(file_census);
            let identifier = |c: char| c.is_alphanumeric() || c == '_';
            textual += source
                .match_indices("any")
                .filter(|&(at, _)| {
                    !source[..at].chars().next_back().is_some_and(identifier)
                        && !source[at + 3..].chars().next().is_some_and(identifier)
                })
                .count();
        }
        eprint!("{census}");
        eprintln!("  ({textual} `any` in the source text)");
    }
    Ok(files)
}

impl<Q> Emitter<'_, '_, '_, Q>
where
    Q: checking::ExternalQueries,
{
    /// Records that the declarations emitted for a function belong to its origin.
    fn note_homes(&mut self, declarations: &[GoDeclaration], origin: Option<FileId>) {
        let Some(origin) = origin else { return };
        for declaration in declarations {
            if let Some(name) = declaration.name() {
                self.homes.insert(name.to_string(), origin);
            }
        }
    }
}

impl<'p, 'm, 'q, Q> Emitter<'p, 'm, 'q, Q>
where
    Q: checking::ExternalQueries,
{
    fn new(
        program: &'p Program,
        monotypes: &'m mut Monotypes,
        queries: &'q Q,
        foreign_packages: &'p ForeignPackages,
        arities: Arities,
    ) -> Emitter<'p, 'm, 'q, Q> {
        let lazy_constants = recursive_constants(program, monotypes);
        Emitter {
            program,
            foreign_packages,
            monotypes,
            context: Context::new(queries),
            imports: BTreeSet::new(),
            function_names: vec![],
            global_names: FxHashSet::default(),
            record_names: FxHashMap::default(),
            data_layouts: FxHashMap::default(),
            closure_sets: FxHashMap::default(),
            closure_layouts: FxHashMap::default(),
            converters: FxHashMap::default(),
            round_trips: vec![],
            recursive_names: FxHashMap::default(),
            type_aliases: FxHashMap::default(),
            type_declarations: vec![],
            reference_declared: false,
            range_name: None,
            homes: FxHashMap::default(),
            spellings: FxHashMap::default(),
            pending_spellings: vec![],
            locals: FxHashMap::default(),
            local_names: FxHashSet::default(),
            typed_records: vec![],
            tail_loop: None,
            tail_groups: vec![],
            tail_group_of: FxHashMap::default(),
            referenced: Default::default(),
            owned_snocs: FxHashSet::default(),
            byte_buffers: FxHashMap::default(),
            owning_variants: FxHashMap::default(),
            pending_owning_variants: vec![],
            inline_shapes: FxHashMap::default(),
            shared_nullaries: FxHashMap::default(),
            constructor_functions: FxHashMap::default(),
            cell_types: FxHashMap::default(),
            reaching: FxHashMap::default(),
            retaining: FxHashMap::default(),
            erasing: FxHashMap::default(),
            erasing_layouts: FxHashMap::default(),
            materialized: FxHashSet::default(),
            uninitialized_locals: FxHashSet::default(),
            current: None,
            lazy_constants,
            arities,
        }
    }
}

impl<Q> reuse::Cells for Emitter<'_, '_, '_, Q>
where
    Q: checking::ExternalQueries,
{
    fn cell(&mut self, monotype: MonotypeId) -> Option<DataType> {
        let Monotype::Data(data) = self.monotypes.get(monotype).clone() else { return None };
        if let Some(&cell) = self.cell_types.get(&data) {
            return cell.then_some(data);
        }
        let cell = self.is_cell(&data);
        self.cell_types.insert(data.clone(), cell);
        cell.then_some(data)
    }

    fn is_spine(&mut self, cell: &DataType, field: MonotypeId) -> bool {
        let Some(child) = reuse::Cells::cell(self, field) else { return false };
        let key = (child.clone(), cell.clone());
        if let Some(&reaches) = self.reaching.get(&key) {
            return reaches;
        }
        let reaches = self.reaches(&child, cell).unwrap_or(false);
        self.reaching.insert(key, reaches);
        reaches
    }

    fn is_effect(&self, monotype: MonotypeId) -> bool {
        self.monotypes.effect_result(monotype).is_some()
    }

    fn is_suspended(&self, monotype: MonotypeId) -> bool {
        matches!(self.monotypes.get(monotype), Monotype::Lazy(_) | Monotype::Effect(_))
    }

    fn erases(&mut self, monotype: MonotypeId) -> bool {
        if let Some(&erases) = self.erasing.get(&monotype) {
            return erases;
        }
        self.erasing.insert(monotype, false);
        let erases = match self.monotypes.get(monotype).clone() {
            Monotype::Erased(_) | Monotype::Recursive(_) => true,
            Monotype::Data(data) => self.erases_arguments(&data).unwrap_or(true),
            Monotype::Function(argument, result) => {
                reuse::Cells::erases(self, argument) || reuse::Cells::erases(self, result)
            }
            Monotype::Array(element)
            | Monotype::Effect(element)
            | Monotype::Reference(element)
            | Monotype::MutableArray(element)
            | Monotype::Object(element)
            | Monotype::Nullable(element)
            | Monotype::Lazy(element) => reuse::Cells::erases(self, element),
            Monotype::Record(fields) => {
                fields.iter().any(|field| reuse::Cells::erases(self, field.monotype))
            }
            _ => false,
        };
        self.erasing.insert(monotype, erases);
        erases
    }

    fn retains(&mut self, monotype: MonotypeId) -> bool {
        if let Some(&retains) = self.retaining.get(&monotype) {
            return retains;
        }
        self.retaining.insert(monotype, true);
        let retains = match self.monotypes.get(monotype).clone() {
            Monotype::Int
            | Monotype::Number
            | Monotype::Boolean
            | Monotype::Char
            | Monotype::String
            | Monotype::Unit
            | Monotype::BigInt
            | Monotype::Regex => false,
            Monotype::Array(element) => reuse::Cells::retains(self, element),
            Monotype::Record(fields) => {
                fields.iter().any(|field| reuse::Cells::retains(self, field.monotype))
            }
            Monotype::Data(data) => {
                reuse::Cells::cell(self, monotype).is_some()
                    || self.constructor_fields(&data).map_or(true, |fields| {
                        fields.into_iter().any(|field| reuse::Cells::retains(self, field))
                    })
            }
            _ => true,
        };
        self.retaining.insert(monotype, retains);
        retains
    }

    fn function_type(&mut self, parameters: &[MonotypeId], result: MonotypeId) -> MonotypeId {
        parameters
            .iter()
            .rev()
            .fold(result, |result, &parameter| self.monotypes.function(parameter, result))
    }
}

/// The constants (parameterless, effect-free definitions) that belong to a
/// reference cycle, found as strongly connected components (Tarjan).
fn recursive_constants(program: &Program, monotypes: &Monotypes) -> FxHashSet<FunctionId> {
    let edges = reference_graph(&program.functions);
    let recursive = on_cycles(&edges, &strongly_connected(&edges));
    let mut constants = FxHashSet::default();
    for (position, function) in program.functions.iter().enumerate() {
        let constant =
            function.parameters.is_empty() && monotypes.effect_result(function.result).is_none();
        if recursive[position] && constant {
            constants.insert(FunctionId(position as u32));
        }
    }
    constants
}

/// An exception that escapes `main` ends the program as it ends a JS one: its stack on stderr and
/// exit status 1. Fibers awaited later report their own failures.
fn report_uncaught_exceptions(declarations: &mut [GoDeclaration]) {
    for declaration in declarations {
        if let GoDeclaration::Function { name, body, .. } = declaration
            && name == "main"
        {
            let report = GoExpression::Qualified {
                package: "exception".into(),
                name: "ReportUncaught".into(),
            };
            body.insert(0, GoStatement::Defer(call(report, vec![])));
        }
    }
}

fn await_fibers(declarations: &mut [GoDeclaration]) {
    for declaration in declarations {
        if let GoDeclaration::Function { name, body, .. } = declaration
            && name == "main"
        {
            let await_ = GoExpression::Qualified { package: "aff".into(), name: "Await".into() };
            // os.Exit skips deferred calls, so an exiting main awaits first.
            if let Some(GoStatement::Expression(GoExpression::Call { function, .. })) = body.last()
                && let GoExpression::Qualified { package, name } = function.as_ref()
                && package == "os"
                && name == "Exit"
            {
                let at = body.len() - 1;
                body.insert(at, GoStatement::Expression(call(await_, vec![])));
                continue;
            }
            body.insert(0, GoStatement::Defer(call(await_, vec![])));
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Mode {
    Value,
    Perform,
}

#[derive(Clone)]
enum Sink {
    Return,
    Assign(String),
    Define(String),
    Discard,
}

enum Exit {
    Return,
    Break { sink: Sink, label: String },
}

#[derive(Clone, Copy)]
struct GuardChain<'e> {
    mode: Mode,
    exit: &'e Exit,
    tested: bool,
}

/// The loop around a function body, or around a group's bodies, that a tail call jumps back to.
struct TailLoop {
    /// Every variable that a jump reassigns.
    parameters: Vec<String>,
    /// The functions whose saturated tail calls jump, with their parameters' variables.
    targets: Vec<LoopTarget>,
    /// The function whose body is being emitted.
    current: FunctionId,
    /// The variable selecting the member a group's loop runs next.
    step: Option<String>,
}

#[derive(Clone)]
struct LoopTarget {
    function: FunctionId,
    parameters: Vec<String>,
    /// The value of the group's step variable that runs this function.
    step: Option<GoExpression>,
}

#[derive(Clone)]
struct DataLayout {
    name: String,
    kind: DataKind,
    constructors: Vec<ConstructorLayout>,
    /// Whether the layout erases type arguments. Such a value, converted from
    /// a fully typed one, remembers it in an `Origin` field (added once a
    /// conversion needs it), so converting back returns the original instead
    /// of wrapping its closures once more.
    erases_arguments: bool,
    boxed: bool,
    /// The position of the struct's declaration in `type_declarations`.
    declaration: Option<usize>,
    /// The position of the `Origin` field among the struct's fields: after the
    /// last that holds pointers, so the collector scans no further.
    origin_position: usize,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum DataKind {
    Enumeration,
    Tagged,
    Product,
}

#[derive(Clone)]
struct ConstructorLayout {
    tag: String,
    fields: Vec<(String, MonotypeId)>,
}

struct Emitter<'p, 'm, 'q, Q> {
    program: &'p Program,
    foreign_packages: &'p ForeignPackages,
    monotypes: &'m mut Monotypes,
    context: Context<'q, Q>,
    imports: BTreeSet<String>,
    function_names: Vec<String>,
    global_names: FxHashSet<String>,
    /// Constants that refer back to themselves through other definitions; Go
    /// rejects such package-level initializers, so they are computed on first use.
    lazy_constants: FxHashSet<FunctionId>,
    record_names: FxHashMap<MonotypeId, String>,
    data_layouts: FxHashMap<DataType, DataLayout>,
    /// The closed function types that are cells, and their structs.
    closure_sets: FxHashMap<MonotypeId, closures::ClosureSet>,
    closure_layouts: FxHashMap<MonotypeId, DataLayout>,
    converters: FxHashMap<(MonotypeId, MonotypeId), String>,
    /// The function each constructor used as a value at a function type is.
    constructor_functions: FxHashMap<(DataType, usize, MonotypeId), String>,
    round_trips: Vec<coerce::RoundTrip>,
    recursive_names: FxHashMap<DataType, String>,
    /// The type each recursive newtype's alias spells.
    type_aliases: FxHashMap<String, GoType>,
    type_declarations: Vec<GoDeclaration>,
    reference_declared: bool,
    /// The name of the support function `Foreign::Range` calls, once declared.
    range_name: Option<String>,
    /// The module each declaration belongs to, where it has one of its own:
    /// a function's is its origin, a data type's the module defining it.
    homes: FxHashMap<String, FileId>,
    /// How each global name was formed, so that a package can spell it anew.
    spellings: FxHashMap<String, Spelling>,
    /// Globals whose spelling waits until every record has its name.
    pending_spellings: Vec<(String, names::PendingSpelling)>,
    locals: FxHashMap<LocalId, GoExpression>,
    local_names: FxHashSet<String>,
    /// The records whose Go names name values, by their tokens' indices.
    typed_records: Vec<MonotypeId>,
    tail_loop: Option<TailLoop>,
    tail_groups: Vec<groups::TailGroup>,
    tail_group_of: FxHashMap<FunctionId, usize>,
    /// The functions that emitted code names, so that an unused group entry can be dropped.
    referenced: std::cell::RefCell<FxHashSet<FunctionId>>,
    current: Option<FunctionId>,
    owned_snocs: FxHashSet<*const Expression>,
    /// The string parameters of the tail loop being emitted that it builds in a `[]byte`, with
    /// the buffer's name; the parameter itself reads `string(buffer)`.
    byte_buffers: FxHashMap<LocalId, String>,
    owning_variants: FxHashMap<(FunctionId, usize), String>,
    pending_owning_variants: Vec<(FunctionId, usize)>,
    inline_shapes: FxHashMap<DataType, Option<layout::Shape>>,
    shared_nullaries: FxHashMap<String, String>,
    cell_types: FxHashMap<DataType, bool>,
    reaching: FxHashMap<(DataType, DataType), bool>,
    retaining: FxHashMap<MonotypeId, bool>,
    erasing: FxHashMap<MonotypeId, bool>,
    erasing_layouts: FxHashMap<DataType, bool>,
    materialized: FxHashSet<(FunctionId, LocalId)>,
    /// The locals of the recursive bindings being assigned, which still hold
    /// Go's zero value.
    uninitialized_locals: FxHashSet<LocalId>,
    arities: Arities,
}

const INLINE_DATA_LIMIT: usize = 128;

impl DataLayout {
    fn go_type(&self) -> GoType {
        let named = GoType::Named(self.name.clone());
        if self.boxed { GoType::Pointer(Box::new(named)) } else { named }
    }
}

/// A record field's Go name: exported, since the record's type may live in
/// another package than the code that builds or reads it.
fn field_name(label: &str) -> String {
    let sanitized: String = label
        .chars()
        .map(|character| if character.is_alphanumeric() { character } else { '_' })
        .collect();
    exported(&sanitized)
}

/// Package names generated code may import.
const IMPORTED_PACKAGES: &[&str] = &[
    "prim",
    "array",
    "direct",
    "object",
    "nullable",
    "exception",
    "aff",
    "promise",
    "foreignvalue",
    "tauri",
    "regex",
    "alloc",
    "fmt",
    "math",
    "os",
    "sync",
    "strconv",
    "strings",
    "big",
    "slices",
];

impl<Q> Emitter<'_, '_, '_, Q>
where
    Q: checking::ExternalQueries,
{
    /// A fresh global name, remembering how it was formed.
    fn global_name(&mut self, spelling: Spelling) -> String {
        let name = unique(spelling.text(), &mut self.global_names);
        self.spellings.insert(name.clone(), spelling);
        name
    }
}

fn unique(base: String, taken: &mut FxHashSet<String>) -> String {
    numbered(&base, |name| !taken.insert(name.to_string()))
}

fn call(function: GoExpression, arguments: Vec<GoExpression>) -> GoExpression {
    GoExpression::Call { function: Box::new(function), arguments }
}

fn length(array: GoExpression) -> GoExpression {
    call(identifier_expression("len"), vec![array])
}

fn identifier_expression(name: &str) -> GoExpression {
    GoExpression::Identifier(name.to_string())
}

fn field(value: GoExpression, name: &str) -> GoExpression {
    GoExpression::Field { value: Box::new(value), name: name.to_string() }
}

fn binary(operator: &'static str, left: GoExpression, right: GoExpression) -> GoExpression {
    GoExpression::Binary { operator, left: Box::new(left), right: Box::new(right) }
}

fn unit_value() -> GoExpression {
    GoExpression::Composite { type_: GoType::EmptyStruct, fields: vec![] }
}

fn panic_statement(message: &str) -> GoStatement {
    GoStatement::Expression(call(
        identifier_expression("panic"),
        vec![GoExpression::String(message.to_string())],
    ))
}

fn conjunction(tests: Vec<GoExpression>) -> Option<GoExpression> {
    tests.into_iter().reduce(|left, right| binary("&&", left, right))
}

fn is_simple(expression: &GoExpression) -> bool {
    if let GoExpression::Composite { fields, .. } = expression {
        return fields.is_empty();
    }
    matches!(
        expression,
        GoExpression::Identifier(_)
            | GoExpression::Integer(_)
            | GoExpression::Float(_)
            | GoExpression::String(_)
            | GoExpression::Rune(_)
            | GoExpression::Boolean(_)
    ) || matches!(expression, GoExpression::Field { value, .. } if is_simple(value))
}

fn is_effectful_call(expression: &GoExpression) -> bool {
    match expression {
        GoExpression::Call { function, .. } => {
            !matches!(function.as_ref(), GoExpression::Identifier(name) if name == "len")
        }
        GoExpression::Conversion { value, .. } => is_effectful_call(value),
        _ => false,
    }
}

#[derive(Clone, Copy)]
enum Direction {
    ToConvention,
    FromConvention,
}

fn returning(value: GoExpression, has_result: bool) -> GoStatement {
    if has_result { GoStatement::Return(Some(value)) } else { GoStatement::Expression(value) }
}

fn discarded(value: GoExpression) -> GoStatement {
    match value {
        GoExpression::Conversion { value, .. } => discarded(*value),
        value => GoStatement::Expression(value),
    }
}

fn statements_reference(statements: &mut [GoStatement], name: &str) -> bool {
    let mut found = false;
    statements_names(statements, &mut |reference| {
        if let Name::Reference(used) | Name::Written(used) = reference {
            found |= used == name;
        }
    });
    found
}

/// Performs the action that defines `name` without keeping its result, when that definition is
/// the last statement: the action is a call, and its result has no use.
fn discard_definition(statements: &mut [GoStatement], name: &str) {
    let Some(last) = statements.last_mut() else { return };
    let GoStatement::Define { names, values } = last else { return };
    if names.as_slice() != [name] || values.len() != 1 || !is_effectful_call(&values[0]) {
        return;
    }
    let value = values.pop().expect("a definition with one name has one value");
    *last = discarded(value);
}

fn uses_local(expression: &Expression, local: LocalId) -> bool {
    let mut found = false;
    visit(expression, &mut |node| {
        if let ExpressionKind::Local(id) = node.kind
            && id == local
        {
            found = true;
        }
    });
    found
}

fn path_root(path: &GoExpression) -> Option<&String> {
    match path {
        GoExpression::Identifier(name) => Some(name),
        GoExpression::Field { value, .. } => path_root(value),
        _ => None,
    }
}

fn local_uses(expression: &Expression, local: LocalId) -> usize {
    let mut uses = 0;
    visit(expression, &mut |node| {
        if let ExpressionKind::Local(id) = node.kind
            && id == local
        {
            uses += 1;
        }
    });
    uses
}

fn guarded_local_uses(guarded: &Guarded, local: LocalId) -> usize {
    match guarded {
        Guarded::Unconditional(body) => local_uses(body, local),
        Guarded::Guards(branches) => branches
            .iter()
            .map(|branch| {
                let guards: usize = branch
                    .guards
                    .iter()
                    .map(|guard| match guard {
                        Guard::Boolean(condition) => local_uses(condition, local),
                        Guard::Pattern { value, .. } => local_uses(value, local),
                    })
                    .sum();
                guards + local_uses(&branch.body, local)
            })
            .sum(),
    }
}

impl<'q, Q> Emitter<'_, '_, 'q, Q>
where
    Q: checking::ExternalQueries,
{
    fn assign_function_names(&mut self) {
        let entry = self.program.entry;
        let entry_function = self.program.function(entry);
        let entry_is_procedure = entry_function.parameters.is_empty()
            && matches!(self.monotypes.get(entry_function.result), Monotype::Effect(result)
                if matches!(self.monotypes.get(*result), Monotype::Unit));
        for (index, function) in self.program.functions.iter().enumerate() {
            let name = if FunctionId(index as u32) == entry && entry_is_procedure {
                self.global_names.insert("main".into());
                "main".to_string()
            } else {
                let full = identifier(&function.name);
                match self.function_parts(&function.name) {
                    Ok(Some(parts)) => {
                        self.pending_global(full, names::PendingSpelling::Parts(parts))
                    }
                    Ok(None) | Err(_) => self.global_name(Spelling::Base(full)),
                }
            };
            self.function_names.push(name);
        }
    }

    fn entry_performs_effects(&self) -> bool {
        let function = self.program.function(self.program.entry);
        function.parameters.is_empty() && self.monotypes.effect_result(function.result).is_some()
    }

    fn main(&mut self) -> GoResult<Option<GoDeclaration>> {
        let entry = self.program.entry;
        let name = self.function_names[entry.0 as usize].clone();
        if name == "main" {
            return Ok(None);
        }
        let function = self.program.function(entry);
        let status = self.monotypes.effect_result(function.result);
        let body = if function.parameters.is_empty()
            && let Some(status) = status
            && let Monotype::Int = self.monotypes.get(status)
        {
            // Like an embedded host running an `Effect Int`, the program's
            // result is its exit status.
            self.imports.insert("os".into());
            let exit = GoExpression::Qualified { package: "os".into(), name: "Exit".into() };
            let status = GoExpression::Conversion {
                type_: GoType::Int,
                value: Box::new(identifier_expression("exitStatus")),
            };
            vec![
                GoStatement::Define {
                    names: vec!["exitStatus".into()],
                    values: vec![call(identifier_expression(&name), vec![])],
                },
                GoStatement::Expression(call(exit, vec![status])),
            ]
        } else if function.parameters.is_empty()
            && let Monotype::Effect(_) = self.monotypes.get(function.result)
        {
            vec![GoStatement::Expression(call(identifier_expression(&name), vec![]))]
        } else {
            self.imports.insert("fmt".into());
            let value = identifier_expression(&name);
            let print = GoExpression::Qualified { package: "fmt".into(), name: "Println".into() };
            vec![GoStatement::Expression(call(print, vec![value]))]
        };
        Ok(Some(GoDeclaration::Function {
            name: "main".into(),
            parameters: vec![],
            result: None,
            body,
        }))
    }

    fn function(&mut self, id: FunctionId) -> GoResult<Vec<GoDeclaration>> {
        if let Some(&group) = self.tail_group_of.get(&id) {
            return self.tail_group_member(id, group);
        }
        let name = self.function_names[id.0 as usize].clone();
        self.function_named(id, name, vec![])
    }

    fn owning_variant(&mut self, id: FunctionId, position: usize) -> GoResult<Vec<GoDeclaration>> {
        let name = self.owning_variants[&(id, position)].clone();
        let function: &Function = self.program.function(id);
        let owned = self
            .owned_parameter_snocs(function, position)
            .into_iter()
            .flat_map(|(_, nodes)| nodes.into_iter().map(std::ptr::from_ref))
            .collect();
        self.function_named(id, name, owned)
    }

    fn function_named(
        &mut self,
        id: FunctionId,
        name: String,
        owned_parameters: Vec<*const Expression>,
    ) -> GoResult<Vec<GoDeclaration>> {
        let function: &Function = self.program.function(id);
        self.current = Some(id);
        self.locals.clear();
        self.local_names.clear();
        self.tail_loop = None;
        self.byte_buffers.clear();
        let mut parameters = vec![];
        for parameter in &function.parameters {
            let parameter_name = self.bind_local(parameter);
            let parameter_type = self.go_type(parameter.monotype)?;
            parameters.push((parameter_name, parameter_type));
        }
        let effect_result = self.monotypes.effect_result(function.result);
        let mode = if effect_result.is_some() { Mode::Perform } else { Mode::Value };
        if function.parameters.is_empty() && mode == Mode::Value {
            if self.lazy_constants.contains(&id) {
                return self.lazy_constant(&name, function);
            }
            return self.constant(&name, function);
        }
        let result = self.go_result(effect_result.unwrap_or(function.result))?;
        let loops = !function.parameters.is_empty()
            && has_tail_call(&function.body, id, function.parameters.len(), mode);
        let captured: Vec<usize> = if loops {
            (0..function.parameters.len())
                .filter(|&position| {
                    let parameter = std::slice::from_ref(&function.parameters[position]);
                    captures_parameters(&function.body, parameter, mode, self.monotypes)
                })
                .collect()
        } else {
            vec![]
        };
        // A string parameter that the loop only appends to grows in a `[]byte` of its own.
        let strings = if loops && mode == Mode::Value {
            self.owned_loop_strings(id, function, &captured)
        } else {
            vec![]
        };
        let mut buffers = vec![];
        for (position, _) in &strings {
            let parameter = &parameters[*position].0;
            let buffer = self.local_name(format!("{parameter}Bytes"));
            let local = function.parameters[*position].id;
            self.locals.insert(local, buffers::to_string(identifier_expression(&buffer)));
            self.byte_buffers.insert(local, buffer.clone());
            buffers.push((*position, buffer));
        }
        if loops {
            let mut parameter_names: Vec<String> =
                parameters.iter().map(|(name, _)| name.clone()).collect();
            for (position, buffer) in &buffers {
                parameter_names[*position] = buffer.clone();
            }
            let target =
                LoopTarget { function: id, parameters: parameter_names.clone(), step: None };
            self.tail_loop = Some(TailLoop {
                parameters: parameter_names,
                targets: vec![target],
                current: id,
                step: None,
            });
        }
        let mut iteration_copies = vec![];
        for &position in &captured {
            let copy = self.local_name(format!("{}Captured", parameters[position].0));
            self.locals.insert(function.parameters[position].id, identifier_expression(&copy));
            iteration_copies.push(GoStatement::Define {
                names: vec![copy],
                values: vec![identifier_expression(&parameters[position].0)],
            });
        }
        let owned = if loops && mode == Mode::Value {
            let mut owned = self.owned_loop_arrays(id, function);
            owned.retain(|(position, _, _)| !captured.contains(position));
            owned
        } else {
            vec![]
        };
        let mut owned_nodes: Vec<*const Expression> =
            owned.iter().flat_map(|(_, _, nodes)| nodes.iter().copied()).collect();
        owned_nodes.extend(strings.into_iter().flat_map(|(_, nodes)| nodes));
        owned_nodes.extend(owned_parameters);
        self.owned_snocs.extend(owned_nodes.iter().copied());
        let mut body = vec![];
        let emitted = self.sink(&function.body, mode, Sink::Return, &mut body);
        for node in &owned_nodes {
            self.owned_snocs.remove(node);
        }
        emitted?;
        if loops {
            if let Some(GoStatement::Continue) = body.last() {
                body.pop();
            }
            iteration_copies.append(&mut body);
            body = iteration_copies;
            let mut clipped: Vec<GoStatement> = owned
                .iter()
                .map(|(position, place, _)| self.clip(&parameters[*position].0, place))
                .collect();
            for (position, buffer) in &buffers {
                let parameter = identifier_expression(&parameters[*position].0);
                clipped.push(GoStatement::Define {
                    names: vec![buffer.clone()],
                    values: vec![buffers::to_bytes(parameter)],
                });
            }
            clipped.push(GoStatement::Loop(body));
            body = clipped;
        }
        if let Some(GoStatement::Return(None)) = body.last() {
            body.pop();
        }
        self.tail_loop = None;
        self.byte_buffers.clear();
        Ok(vec![GoDeclaration::Function { name, parameters, result, body }])
    }

    pub(super) fn owned_parameter_snocs<'e>(
        &mut self,
        function: &'e Function,
        position: usize,
    ) -> Vec<(ownership::Place, Vec<&'e Expression>)> {
        let parameter = &function.parameters[position];
        self.carried_places(parameter.monotype)
            .into_iter()
            .filter_map(|place| {
                let carried = ownership::Carried::new(parameter.id, &place);
                let nodes = ownership::owned_snocs(carried, &function.body)?;
                (!nodes.is_empty()).then_some((place, nodes))
            })
            .collect()
    }

    pub(super) fn owning_variant_name(&mut self, id: FunctionId, position: usize) -> String {
        if let Some(name) = self.owning_variants.get(&(id, position)) {
            return name.clone();
        }
        let function_name = self.function_names[id.0 as usize].clone();
        let name = self.global_name(Spelling::derived("", function_name, "Owning"));
        self.owning_variants.insert((id, position), name.clone());
        self.pending_owning_variants.push((id, position));
        name
    }

    fn owned_loop_arrays(
        &mut self,
        id: FunctionId,
        function: &Function,
    ) -> Vec<(usize, ownership::Place, Vec<*const Expression>)> {
        let arity = function.parameters.len();
        let mut owned = vec![];
        for (position, parameter) in function.parameters.iter().enumerate() {
            let tail_call = ownership::TailCall { function: id, arity, position };
            for place in self.carried_places(parameter.monotype) {
                let carried = ownership::Carried::new(parameter.id, &place);
                let Some(nodes) = ownership::owned_loop_snocs(carried, &function.body, tail_call)
                else {
                    continue;
                };
                if nodes.is_empty() {
                    continue;
                }
                let nodes = nodes.into_iter().map(std::ptr::from_ref).collect();
                owned.push((position, place, nodes));
            }
        }
        owned
    }

    /// A recursive constant: `name()` computes the value once, on first use, as
    /// JavaScript's lazily initialised recursive bindings do.
    fn lazy_constant(&mut self, name: &str, function: &Function) -> GoResult<Vec<GoDeclaration>> {
        let type_ = self.go_type(function.result)?;
        let mut statements = vec![];
        let value = self.value(&function.body, &mut statements)?;
        let cell = self.global_name(Spelling::derived("", name.into(), "Value"));
        let ready = self.global_name(Spelling::derived("", name.into(), "Ready"));
        statements.push(GoStatement::Assign {
            targets: vec![identifier_expression(&cell)],
            values: vec![value],
        });
        statements.push(GoStatement::Assign {
            targets: vec![identifier_expression(&ready)],
            values: vec![identifier_expression("true")],
        });
        let compute = GoStatement::If {
            condition: GoExpression::Unary {
                operator: "!",
                operand: Box::new(identifier_expression(&ready)),
            },
            then: statements,
            otherwise: vec![],
        };
        Ok(vec![
            GoDeclaration::Declared { name: cell.clone(), type_: type_.clone() },
            GoDeclaration::Declared { name: ready, type_: GoType::Bool },
            GoDeclaration::Function {
                name: name.into(),
                parameters: vec![],
                result: Some(type_),
                body: vec![compute, GoStatement::Return(Some(identifier_expression(&cell)))],
            },
        ])
    }

    fn constant(&mut self, name: &str, function: &Function) -> GoResult<Vec<GoDeclaration>> {
        let type_ = self.go_type(function.result)?;
        let mut statements = vec![];
        let value = self.value(&function.body, &mut statements)?;
        if statements.is_empty() {
            return Ok(vec![GoDeclaration::Variable {
                name: name.into(),
                type_: Some(type_),
                value,
            }]);
        }
        let initializer = self.global_name(Spelling::derived("initialize", name.into(), ""));
        statements.push(GoStatement::Return(Some(value)));
        let result = self.go_result(function.result)?;
        Ok(vec![
            GoDeclaration::Variable {
                name: name.into(),
                type_: None,
                value: call(identifier_expression(&initializer), vec![]),
            },
            GoDeclaration::Function {
                name: initializer,
                parameters: vec![],
                result,
                body: statements,
            },
        ])
    }

    fn current_definition(&self) -> String {
        match self.current {
            Some(id) => format!("code generation of {}", self.program.function(id).name),
            None => "code generation".into(),
        }
    }

    fn is_total(&mut self, pattern: &Pattern) -> bool {
        match &pattern.kind {
            PatternKind::Wildcard | PatternKind::Variable(_) => true,
            PatternKind::Named { pattern, .. } => self.is_total(pattern),
            PatternKind::Record(fields) => fields.iter().all(|(_, field)| self.is_total(field)),
            PatternKind::Constructor { data, arguments, .. } => {
                let product =
                    self.data_layout(data).is_ok_and(|layout| layout.kind == DataKind::Product);
                product && arguments.iter().all(|argument| self.is_total(argument))
            }
            PatternKind::Closure { captures, .. } => {
                let product = self
                    .closure_layout(pattern.monotype)
                    .is_ok_and(|layout| layout.kind == DataKind::Product);
                product && captures.iter().all(|capture| self.is_total(capture))
            }
            PatternKind::Literal(_) | PatternKind::Array(_) => false,
        }
    }

    /// Binds each local the pattern binds and `uses_of` says is used.
    fn bind_pattern_locals(
        &mut self,
        bindings: &[(Local, GoExpression)],
        uses_of: impl Fn(LocalId) -> usize,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<()> {
        for (local, path) in bindings {
            let uses = uses_of(local.id);
            if uses > 0 {
                self.bind_pattern_local(local, path, uses, out)?;
            }
        }
        Ok(())
    }

    fn bind_pattern_local(
        &mut self,
        local: &Local,
        path: &GoExpression,
        uses: usize,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<()> {
        let reassigned = |name: &String| {
            self.tail_loop.as_ref().is_some_and(|tail_loop| tail_loop.parameters.contains(name))
        };
        let materialized =
            self.current.is_some_and(|function| self.materialized.contains(&(function, local.id)));
        let aliased = match path_root(path) {
            Some(root) if !reassigned(root) => {
                matches!(path, GoExpression::Identifier(_)) || (uses == 1 && !materialized)
            }
            _ => false,
        };
        if aliased {
            self.locals.insert(local.id, path.clone());
            return Ok(());
        }
        // A Unit field carries no information; its uses read the unit value.
        if self.is_unit(local.monotype) {
            self.locals.insert(local.id, unit_value());
            return Ok(());
        }
        let name = self.bind_local(local);
        out.push(self.define(name, path.clone(), local.monotype)?);
        Ok(())
    }

    fn bind_local(&mut self, local: &Local) -> String {
        let base = self.local_base(&local.name, local.monotype);
        let name = self.local_name(base);
        self.locals.insert(local.id, identifier_expression(&name));
        name
    }

    /// The Go spelling a local's name starts from: a record value's is a
    /// token for its record, which the record's Go name replaces once
    /// packaging has chosen it.
    fn local_base(&mut self, name: &str, monotype: MonotypeId) -> String {
        match name.strip_prefix(crate::naming::RECORD_VALUE) {
            Some("") => self.value_base(monotype),
            Some(rest) => identifier(&crate::naming::lower_camel(rest)),
            // A name from the type alone is the first to give way.
            None if name == self.monotypes.value_name(monotype) => {
                format!("{}{}", identifier(name), locals::NUMBERED)
            }
            None => identifier(name),
        }
    }

    /// The Go spelling of a value that only its type names.
    fn value_base(&mut self, monotype: MonotypeId) -> String {
        if !matches!(self.monotypes.get(monotype), Monotype::Record(_)) {
            return format!(
                "{}{}",
                identifier(&self.monotypes.value_name(monotype)),
                locals::NUMBERED
            );
        }
        let index = match self.typed_records.iter().position(|&known| known == monotype) {
            Some(index) => index,
            None => {
                self.typed_records.push(monotype);
                self.typed_records.len() - 1
            }
        };
        locals::record_token(index)
    }

    fn temporary(&mut self, base: &str) -> String {
        self.local_name(base.to_string())
    }

    /// A fresh local that shadows no global function or type, nor an imported
    /// package, any of which the function body may still need to refer to.
    /// A number it needs follows a mark, so that once the local's Go scope is
    /// known it can lose the number where nothing there clashes with it.
    fn local_name(&mut self, base: String) -> String {
        let taken = |emitter: &Self, candidate: &String| {
            emitter.local_names.contains(candidate)
                || emitter.global_names.contains(candidate)
                || IMPORTED_PACKAGES.contains(&candidate.as_str())
        };
        // A name that ends in the mark yields to any it clashes with once
        // settled. So does a package's name, which is free for a local where
        // the code does not use the package, as only the settled scope shows.
        let soft = base.ends_with(locals::NUMBERED);
        let base = base.trim_end_matches(locals::NUMBERED).to_string();
        let (base, soft) = match base.strip_suffix('_') {
            Some(stem) if IMPORTED_PACKAGES.contains(&stem) => (stem.to_string(), true),
            _ => (base, soft),
        };
        let mut candidate = if soft { format!("{base}{}", locals::NUMBERED) } else { base.clone() };
        let mut counter = 2;
        while taken(self, &candidate) {
            candidate = format!("{base}{}{counter}", locals::NUMBERED);
            counter += 1;
        }
        self.local_names.insert(candidate.clone());
        candidate
    }

    fn local(&self, id: LocalId) -> GoResult<GoExpression> {
        self.locals.get(&id).cloned().ok_or_else(|| GoError::Unsupported {
            definition: self.current_definition(),
            state: crate::error::UnsupportedState::Construct { construct: "unbound local" },
        })
    }

    fn sink(
        &mut self,
        expression: &Expression,
        mode: Mode,
        sink: Sink,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<()> {
        match &expression.kind {
            ExpressionKind::Let { bindings, body } => {
                self.bindings(bindings, out)?;
                self.sink(body, mode, sink, out)
            }
            ExpressionKind::If { condition, then, otherwise } => {
                let condition = self.value(condition, out)?;
                let sink = self.prepare_branching_sink(sink, expression, mode, out)?;
                let mut then_statements = vec![];
                self.sink(then, mode, sink.clone(), &mut then_statements)?;
                let mut otherwise_statements = vec![];
                self.sink(otherwise, mode, sink.clone(), &mut otherwise_statements)?;
                if let Sink::Return = sink
                    && ends_in_jump(&then_statements)
                {
                    out.push(GoStatement::If {
                        condition,
                        then: then_statements,
                        otherwise: vec![],
                    });
                    out.extend(otherwise_statements);
                } else {
                    out.push(GoStatement::If {
                        condition,
                        then: then_statements,
                        otherwise: otherwise_statements,
                    });
                }
                Ok(())
            }
            ExpressionKind::Case { scrutinees, alternatives } => {
                self.case(expression, scrutinees, alternatives, mode, sink, out)
            }
            ExpressionKind::Fail(message) => {
                out.push(panic_statement(message));
                Ok(())
            }
            ExpressionKind::Apply { function, arguments } if matches!(sink, Sink::Return) => {
                if let ExpressionKind::Function(id) = function.kind
                    && let Some(tail_loop) = &self.tail_loop
                    && let Some(target) = tail_loop.targets.iter().find(|target| {
                        target.function == id && target.parameters.len() == arguments.len()
                    })
                {
                    let step = match (&tail_loop.step, &target.step) {
                        (Some(variable), Some(value)) if id != tail_loop.current => {
                            Some((variable.clone(), value.clone()))
                        }
                        _ => None,
                    };
                    let parameters = target.parameters.clone();
                    return self.tail_call(&parameters, arguments, step, out);
                }
                self.leaf(expression, mode, sink, out)
            }
            _ => self.leaf(expression, mode, sink, out),
        }
    }

    fn tail_call(
        &mut self,
        parameters: &[String],
        arguments: &[Expression],
        step: Option<(String, GoExpression)>,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<()> {
        let mut targets = vec![];
        let mut values = vec![];
        if let Some((variable, value)) = step {
            targets.push(identifier_expression(&variable));
            values.push(value);
        }
        for (parameter, argument) in parameters.iter().zip(arguments) {
            if let ExpressionKind::Local(id) = argument.kind
                && self.byte_buffers.get(&id) == Some(parameter)
            {
                continue;
            }
            let value = self.value(argument, out)?;
            if let GoExpression::Identifier(name) = &value
                && name == parameter
            {
                continue;
            }
            targets.push(identifier_expression(parameter));
            values.push(value);
        }
        if !targets.is_empty() {
            out.push(GoStatement::Assign { targets, values });
        }
        out.push(GoStatement::Continue);
        Ok(())
    }

    fn prepare_branching_sink(
        &mut self,
        sink: Sink,
        expression: &Expression,
        mode: Mode,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<Sink> {
        let Sink::Define(name) = sink else { return Ok(sink) };
        let monotype = match mode {
            Mode::Perform => {
                self.monotypes.effect_result(expression.monotype).unwrap_or(expression.monotype)
            }
            Mode::Value => expression.monotype,
        };
        if self.is_unit(monotype) {
            return Ok(Sink::Discard);
        }
        let type_ = self.go_type(monotype)?;
        out.push(GoStatement::Variable { name: name.clone(), type_, value: None });
        Ok(Sink::Assign(name))
    }

    fn leaf(
        &mut self,
        expression: &Expression,
        mode: Mode,
        sink: Sink,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<()> {
        if mode == Mode::Value {
            let value = self.value(expression, out)?;
            return self.deliver(value, expression.monotype, sink, out);
        }
        let result =
            self.monotypes.effect_result(expression.monotype).unwrap_or(expression.monotype);
        match &expression.kind {
            ExpressionKind::EffectPure(value) => {
                let value = self.value(value, out)?;
                self.deliver(value, result, sink, out)
            }
            ExpressionKind::EffectBind { action, local, body } => {
                if !uses_local(body, local.id) || self.is_unit(local.monotype) {
                    self.locals.insert(local.id, unit_value());
                    self.sink(action, Mode::Perform, Sink::Discard, out)?;
                    return self.sink(body, Mode::Perform, sink, out);
                }
                let name = self.bind_local(local);
                self.sink(action, Mode::Perform, Sink::Define(name.clone()), out)?;
                let performed = out.len();
                self.sink(body, Mode::Perform, sink, out)?;
                // The body can mention the local only in a value it then discards, such as an
                // unsubscriber nobody keeps; Go rejects the definition that is left without a use.
                if !statements_reference(&mut out[performed..], &name) {
                    discard_definition(&mut out[..performed], &name);
                }
                Ok(())
            }
            ExpressionKind::EffectEach { array, element, body } => {
                let array = self.value(array, out)?;
                let saved = self.tail_loop.take();
                let element_name = if uses_local(body, element.id) {
                    self.bind_local(element)
                } else {
                    "_".to_string()
                };
                let mut statements = vec![];
                self.sink(body, Mode::Perform, Sink::Discard, &mut statements)?;
                self.tail_loop = saved;
                out.push(GoStatement::Range {
                    index: None,
                    element: element_name,
                    iterable: array,
                    body: statements,
                });
                self.deliver(unit_value(), result, sink, out)
            }
            ExpressionKind::Foreign { foreign, arguments } if foreign.is_effectful() => {
                self.perform_foreign(*foreign, arguments, result, sink, out)
            }
            ExpressionKind::Apply { function, arguments } => {
                let performed = self.perform_application(function, arguments, out)?;
                self.deliver(performed, result, sink, out)
            }
            _ => {
                let action = self.value(expression, out)?;
                self.deliver(call(action, vec![]), result, sink, out)
            }
        }
    }

    fn perform_application(
        &mut self,
        function: &Expression,
        arguments: &[Expression],
        out: &mut Vec<GoStatement>,
    ) -> GoResult<GoExpression> {
        if let ExpressionKind::Function(id) = function.kind {
            let arity = self.program.function(id).parameters.len();
            if arity == arguments.len() {
                let values = self.values(arguments, out)?;
                return Ok(call(identifier_expression(self.function_reference(id)), values));
            }
        }
        self.application_value(function, arguments, out)
    }

    fn perform_foreign(
        &mut self,
        foreign: Foreign,
        arguments: &[Expression],
        result: MonotypeId,
        sink: Sink,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<()> {
        match foreign {
            Foreign::EffectWhile | Foreign::EffectUntil => {
                return self.effect_loop(foreign, arguments, result, sink, out);
            }
            Foreign::EffectFor => return self.effect_for(arguments, result, sink, out),
            Foreign::WithMutex => return self.with_mutex(arguments, result, sink, out),
            Foreign::MutexNew => {
                self.imports.insert("sync".into());
                let mutex = call(
                    identifier_expression("new"),
                    vec![GoExpression::Type(GoType::Named("sync.Mutex".into()))],
                );
                return self.deliver(mutex, result, sink, out);
            }
            Foreign::MakeAff => {
                let performed = self.make_aff(arguments, out)?;
                return self.deliver(performed, result, sink, out);
            }
            Foreign::ForkFiber | Foreign::NewFiber => {
                let action = self.value(&arguments[1], out)?;
                let action = self.unit_valued(action, arguments[1].monotype, out)?;
                let handle = match foreign {
                    Foreign::ForkFiber => {
                        let immediate = self.value(&arguments[0], out)?;
                        let fork = GoFunction { package: GoPackage::Aff, name: "ForkFiber" };
                        call(self.go_function(fork), vec![immediate, action])
                    }
                    _ => {
                        let new = GoFunction { package: GoPackage::Aff, name: "NewFiber" };
                        call(self.go_function(new), vec![action])
                    }
                };
                if let Sink::Discard = sink {
                    out.push(GoStatement::Expression(handle));
                    return Ok(());
                }
                let handle = self.hoist(handle, "fiber", out);
                let record = self.fiber_record(handle, result, out)?;
                return self.deliver(record, result, sink, out);
            }
            Foreign::NewSupervisedFiber => {
                let action = self.value(&arguments[1], out)?;
                let action = self.unit_valued(action, arguments[1].monotype, out)?;
                let new = GoFunction { package: GoPackage::Aff, name: "NewSupervisedFiber" };
                let handle = self.temporary("fiber");
                let supervisor = self.temporary("supervisor");
                out.push(GoStatement::Define {
                    names: vec![handle.clone(), supervisor.clone()],
                    values: vec![call(self.go_function(new), vec![action])],
                });
                let fiber = self.record_field_monotype(result, "fiber");
                let fiber = self.fiber_record(identifier_expression(&handle), fiber, out)?;
                let supervised = GoExpression::Composite {
                    type_: GoType::Named(self.record_name(result)?),
                    fields: vec![
                        (Some(field_name("fiber")), fiber),
                        (Some(field_name("supervisor")), identifier_expression(&supervisor)),
                    ],
                };
                return self.deliver(supervised, result, sink, out);
            }
            Foreign::AssocArray => {
                let array = self.value(&arguments[0], out)?;
                let associated = self.associated_elements(result)?;
                let map = GoFunction { package: GoPackage::Direct, name: "MapWithIndex" };
                let elements = GoExpression::Unary { operator: "*", operand: Box::new(array) };
                let associated = call(self.go_function(map), vec![associated, elements]);
                return self.deliver(associated, result, sink, out);
            }
            Foreign::Project { file_id, term, .. } => {
                let thunk = self.project_call(file_id, term, arguments, result, out)?;
                let performed = self.out_of_convention(call(thunk, vec![]), result, out)?;
                return self.deliver(performed, result, sink, out);
            }
            Foreign::Perform { function, boundary, .. } => {
                let values = self.boundary_arguments(arguments, boundary, result, false, out)?;
                let function = self.boundary_function(function, boundary, result)?;
                let mut performed = call(function, values);
                if boundary.thunk {
                    performed = call(performed, vec![]);
                }
                if boundary.record_result {
                    let record = self.record_from_results(performed, result, out)?;
                    return self.deliver(record, result, sink, out);
                }
                return self.deliver(performed, result, sink, out);
            }
            _ => {}
        }
        let mut values = self.values(arguments, out)?;
        match foreign {
            Foreign::Print => {
                self.imports.insert("fmt".into());
                let print =
                    GoExpression::Qualified { package: "fmt".into(), name: "Println".into() };
                out.push(GoStatement::Expression(call(print, values)));
                self.deliver(unit_value(), result, sink, out)
            }
            Foreign::ReferenceNew => {
                let value_type = self.go_type(arguments[0].monotype)?;
                self.declare_reference();
                let reference = GoExpression::Address(Box::new(GoExpression::Composite {
                    type_: reference_type(value_type),
                    fields: vec![(Some("Value".into()), values.remove(0))],
                }));
                self.deliver(reference, result, sink, out)
            }
            Foreign::ReferenceRead => {
                let value = field(values.remove(0), "Value");
                self.deliver(value, result, sink, out)
            }
            Foreign::ReferenceWrite => {
                let value = values.remove(0);
                let reference = values.remove(0);
                out.push(GoStatement::Assign {
                    targets: vec![field(reference, "Value")],
                    values: vec![value],
                });
                self.deliver(unit_value(), result, sink, out)
            }
            Foreign::ReferenceModify => {
                let reference = values.remove(1);
                let reference = self.hoist(reference, "reference", out);
                let modified = self.temporary("modified");
                if let ExpressionKind::Lambda { parameters, body } = &arguments[0].kind
                    && let [state] = parameters.as_slice()
                {
                    let name = self.bind_local(state);
                    out.push(GoStatement::Define {
                        names: vec![name],
                        values: vec![field(reference.clone(), "Value")],
                    });
                    self.sink(body, Mode::Value, Sink::Define(modified.clone()), out)?;
                } else {
                    let update = values.remove(0);
                    out.push(GoStatement::Define {
                        names: vec![modified.clone()],
                        values: vec![call(update, vec![field(reference.clone(), "Value")])],
                    });
                }
                out.push(GoStatement::Assign {
                    targets: vec![field(reference, "Value")],
                    values: vec![field(identifier_expression(&modified), &field_name("state"))],
                });
                let value = field(identifier_expression(&modified), &field_name("value"));
                self.deliver(value, result, sink, out)
            }
            Foreign::Throw => {
                out.push(GoStatement::Expression(call(
                    identifier_expression("panic"),
                    vec![values.remove(0)],
                )));
                if let Sink::Define(name) = sink
                    && !self.is_unit(result)
                {
                    let type_ = self.go_type(result)?;
                    out.push(GoStatement::Variable { name, type_, value: None });
                }
                Ok(())
            }
            Foreign::MutableArrayNew => {
                let array_type = self.go_type(result)?;
                let GoType::Pointer(slice) = array_type else {
                    unreachable!("invariant violated: a mutable array is a slice pointer")
                };
                let empty = GoExpression::Composite { type_: *slice, fields: vec![] };
                self.deliver(GoExpression::Address(Box::new(empty)), result, sink, out)
            }
            Foreign::ReferenceWriteThrough => {
                let value = self.hoist(values.remove(0), "written", out);
                let reference = values.remove(0);
                out.push(GoStatement::Assign {
                    targets: vec![field(reference, "Value")],
                    values: vec![value.clone()],
                });
                self.deliver(value, result, sink, out)
            }
            Foreign::EffectPure => self.deliver(values.remove(0), result, sink, out),
            _ => Err(GoError::Unsupported {
                definition: self.current_definition(),
                state: crate::error::UnsupportedState::Construct {
                    construct: "unsaturated effect primitives",
                },
            }),
        }
    }

    /// A call of a project's Go foreign. A foreign without arguments whose
    /// result is one of the package's generic types is instantiated at the
    /// result's type arguments, which nothing else would tell Go.
    fn project_call(
        &mut self,
        file_id: FileId,
        term: TermItemId,
        arguments: &[Expression],
        result: MonotypeId,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<GoExpression> {
        let module_name = self.context.module(file_id)?.name.clone();
        let name = self.context.term_name(file_id, term)?;
        self.imports.insert(self.foreign_packages.import_path(&module_name));
        let function = GoExpression::Qualified {
            package: ForeignPackages::package_name(&module_name),
            name: capitalise(&name),
        };
        if arguments.is_empty() {
            if let Monotype::ForeignData(data) = self.monotypes.get(result).clone()
                && let GoType::Generic { arguments, .. } = self.foreign_data_type(&data)?
            {
                return Ok(GoExpression::Instantiation { function: Box::new(function), arguments });
            }
            return Ok(function);
        }
        let mut values = vec![];
        for argument in arguments {
            let value = self.value(argument, out)?;
            values.push(self.in_convention(value, argument.monotype, out)?);
        }
        Ok(call(function, values))
    }

    fn utility_constructor(
        &mut self,
        constructed: Constructed,
        arguments: &[Expression],
        result: MonotypeId,
    ) -> GoResult<GoExpression> {
        let (data, name) = match constructed {
            Constructed::Result(name) => (result, name),
            Constructed::CallbackParameter(position, name) => {
                let (parameter, _) = self
                    .monotypes
                    .function_parts(arguments[position].monotype)
                    .expect("invariant violated: a utility callback is a function");
                (parameter, name)
            }
        };
        let (data_type, index) = self.constructor_named(data, name)?;
        if self.data_layout(&data_type)?.constructors[index].fields.is_empty() {
            return self.construct(&data_type, index, vec![]);
        }
        self.constructor_function(data, name)
    }

    fn mentioned_maybe(&mut self, monotype: MonotypeId) -> GoResult<Option<MonotypeId>> {
        match self.monotypes.get(monotype).clone() {
            Monotype::Data(data) => {
                if self.context.type_name(data.file_id, data.item)? == "Maybe" {
                    return Ok(Some(monotype));
                }
                Ok(None)
            }
            Monotype::Array(element) => self.mentioned_maybe(element),
            Monotype::Function(argument, result) => match self.mentioned_maybe(argument)? {
                Some(maybe) => Ok(Some(maybe)),
                None => self.mentioned_maybe(result),
            },
            _ => Ok(None),
        }
    }

    fn typed_constant(
        &mut self,
        value: GoExpression,
        monotype: MonotypeId,
    ) -> GoResult<GoExpression> {
        if !is_untyped_constant(&value) {
            return Ok(value);
        }
        let type_ = self.go_type(monotype)?;
        Ok(GoExpression::Conversion { type_, value: Box::new(value) })
    }

    fn record_from_results(
        &mut self,
        results: GoExpression,
        monotype: MonotypeId,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<GoExpression> {
        let Monotype::Record(fields) = self.monotypes.get(monotype).clone() else {
            unreachable!("invariant violated: a record result has a record type")
        };
        let names: Vec<String> =
            fields.iter().map(|field| self.temporary(&identifier(&field.label))).collect();
        out.push(GoStatement::Define { names: names.clone(), values: vec![results] });
        let values = fields
            .iter()
            .zip(names)
            .map(|(field, name)| (field.label.clone(), identifier_expression(&name)))
            .collect();
        self.record_value(monotype, values)
    }

    fn unit_valued(
        &mut self,
        value: GoExpression,
        monotype: MonotypeId,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<GoExpression> {
        if !self.has_unit_result(monotype) {
            return Ok(value);
        }
        let value = match value {
            GoExpression::Function { .. } => value,
            value => self.shared(value, "function", out),
        };
        let (parameter, result) = self.callable_parts(monotype);
        let mut parameters = vec![];
        let mut arguments = vec![];
        if let Some(parameter) = parameter {
            let base = self.value_base(parameter);
            let name = self.temporary(&base);
            parameters.push((name.clone(), self.go_type(parameter)?));
            arguments.push(identifier_expression(&name));
        }
        let mut body = vec![];
        let applied = match parameter {
            Some(_) => {
                let callable = self.value_callable(value, monotype);
                self.apply_arguments(callable, arguments, &mut body)?
            }
            None => call(value, arguments),
        };
        if self.is_unit(result) {
            body.push(GoStatement::Expression(applied));
            body.push(GoStatement::Return(Some(unit_value())));
        } else {
            let adapted = self.unit_valued(applied, result, &mut body)?;
            body.push(GoStatement::Return(Some(adapted)));
        }
        let result = self.unit_valued_type(result)?;
        Ok(GoExpression::Function { parameters, result: Some(result), body })
    }

    fn callable_parts(&self, monotype: MonotypeId) -> (Option<MonotypeId>, MonotypeId) {
        match self.monotypes.get(monotype) {
            Monotype::Function(argument, result) => {
                (Some(*argument), self.monotypes.effect_result(*result).unwrap_or(*result))
            }
            Monotype::Effect(result) => (None, *result),
            _ => unreachable!("invariant violated: only functions and effects are callable"),
        }
    }

    /// Whether a function's result after `arrows` applications is an effect,
    /// which direct style performs on application instead of returning it.
    fn effect_after(&self, monotype: MonotypeId, arrows: usize) -> bool {
        match self.monotypes.get(monotype) {
            Monotype::Function(_, result) if arrows == 1 => {
                matches!(self.monotypes.get(*result), Monotype::Effect(_))
            }
            Monotype::Function(_, result) => self.effect_after(*result, arrows - 1),
            _ => false,
        }
    }

    /// The type of a callback as a generic go-support helper sees it: after
    /// `arrows` applications it returns the effect as a value.
    fn uniform_type(&mut self, monotype: MonotypeId, arrows: usize) -> GoResult<GoType> {
        let Monotype::Function(argument, result) = self.monotypes.get(monotype).clone() else {
            return self.go_type(monotype);
        };
        let parameter = self.go_type(argument)?;
        let result = if arrows == 1 {
            self.go_type(result)?
        } else {
            self.uniform_type(result, arrows - 1)?
        };
        Ok(GoType::Function { parameters: vec![parameter], result: Some(Box::new(result)) })
    }

    /// Adapts a direct-style callback to `uniform_type`, delaying its effect.
    fn uniform_function(
        &mut self,
        function: GoExpression,
        monotype: MonotypeId,
        arrows: usize,
    ) -> GoResult<GoExpression> {
        let Monotype::Function(argument, result) = self.monotypes.get(monotype).clone() else {
            return Ok(function);
        };
        let base = self.value_base(argument);
        let parameter = self.temporary(&base);
        let parameter_type = self.go_type(argument)?;
        let mut body = vec![];
        let callable = self.value_callable(function, monotype);
        let applied =
            self.apply_arguments(callable, vec![identifier_expression(&parameter)], &mut body)?;
        let tail = if arrows == 1 {
            let Monotype::Effect(inner) = self.monotypes.get(result).clone() else {
                unreachable!("invariant violated: a uniform callback ends in an effect")
            };
            let performed = if self.is_unit(inner) {
                vec![GoStatement::Expression(applied)]
            } else {
                vec![GoStatement::Return(Some(applied))]
            };
            let action = GoExpression::Function {
                parameters: vec![],
                result: self.go_result(inner)?,
                body: performed,
            };
            vec![GoStatement::Return(Some(action))]
        } else {
            let partial = self.temporary("partial");
            let adapted =
                self.uniform_function(identifier_expression(&partial), result, arrows - 1)?;
            vec![
                GoStatement::Define { names: vec![partial], values: vec![applied] },
                GoStatement::Return(Some(adapted)),
            ]
        };
        body.extend(tail);
        Ok(GoExpression::Function {
            parameters: vec![(parameter, parameter_type)],
            result: Some(self.uniform_type(result, arrows - 1)?),
            body,
        })
    }

    fn has_unit_result(&self, monotype: MonotypeId) -> bool {
        if !matches!(self.monotypes.get(monotype), Monotype::Function(..) | Monotype::Effect(_)) {
            return false;
        }
        let (_, result) = self.callable_parts(monotype);
        self.is_unit(result) || self.has_unit_result(result)
    }

    fn unit_valued_type(&mut self, monotype: MonotypeId) -> GoResult<GoType> {
        if self.is_unit(monotype) {
            return Ok(GoType::EmptyStruct);
        }
        if !self.has_unit_result(monotype) {
            return self.go_type(monotype);
        }
        let (parameter, result) = self.callable_parts(monotype);
        let parameters = match parameter {
            Some(parameter) => vec![self.go_type(parameter)?],
            None => vec![],
        };
        let result = self.unit_valued_type(result)?;
        Ok(GoType::Function { parameters, result: Some(Box::new(result)) })
    }

    fn just_function(&mut self, maybe: MonotypeId) -> GoResult<GoExpression> {
        self.constructor_function(maybe, "Just")
    }

    fn nothing_value(&mut self, maybe: MonotypeId) -> GoResult<GoExpression> {
        let (data, nothing) = self.constructor_named(maybe, "Nothing")?;
        self.construct(&data, nothing, vec![])
    }

    /// The `Maybe b` of a `Maybe (Array (Maybe b))`.
    fn array_payload_maybe(&mut self, maybe: MonotypeId) -> GoResult<MonotypeId> {
        let (data, just) = self.constructor_named(maybe, "Just")?;
        let layout = self.data_layout(&data)?;
        let [(_, payload)] = &layout.constructors[just].fields[..] else {
            unreachable!("invariant violated: Just has one field")
        };
        let Monotype::Array(element) = self.monotypes.get(*payload).clone() else {
            unreachable!("invariant violated: the Maybe holds an array")
        };
        Ok(element)
    }

    fn is_just_function(&mut self, maybe: MonotypeId) -> GoResult<GoExpression> {
        let (data, just) = self.constructor_named(maybe, "Just")?;
        let layout = self.data_layout(&data)?;
        let parameter = self.temporary("maybe");
        let tag = field(identifier_expression(&parameter), "Tag");
        let is_just = binary("==", tag, identifier_expression(&layout.constructors[just].tag));
        Ok(GoExpression::Function {
            parameters: vec![(parameter, self.go_type(maybe)?)],
            result: Some(GoType::Bool),
            body: vec![GoStatement::Return(Some(is_just))],
        })
    }

    fn just_value_function(&mut self, maybe: MonotypeId) -> GoResult<GoExpression> {
        let (data, just) = self.constructor_named(maybe, "Just")?;
        let layout = self.data_layout(&data)?;
        let constructor = &layout.constructors[just];
        let [(payload, payload_monotype)] = &constructor.fields[..] else {
            unreachable!("invariant violated: Just has one field")
        };
        let parameter = self.temporary("maybe");
        let value = identifier_expression(&parameter);
        let is_just =
            binary("==", field(value.clone(), "Tag"), identifier_expression(&constructor.tag));
        let payload = GoExpression::Address(Box::new(field(value, payload)));
        let payload_type = self.go_type(*payload_monotype)?;
        Ok(GoExpression::Function {
            parameters: vec![(parameter, self.go_type(maybe)?)],
            result: Some(GoType::Pointer(Box::new(payload_type))),
            body: vec![
                GoStatement::If {
                    condition: is_just,
                    then: vec![GoStatement::Return(Some(payload))],
                    otherwise: vec![],
                },
                GoStatement::Return(Some(identifier_expression("nil"))),
            ],
        })
    }

    fn associated_elements(&mut self, associated: MonotypeId) -> GoResult<GoExpression> {
        let Monotype::Array(record) = self.monotypes.get(associated).clone() else {
            unreachable!("invariant violated: toAssocArray returns an array")
        };
        let element = self.record_field_monotype(record, "value");
        let index = self.temporary("index");
        let value = self.temporary("value");
        let record_type = GoType::Named(self.record_name(record)?);
        let associate = GoExpression::Composite {
            type_: record_type.clone(),
            fields: vec![
                (Some(field_name("index")), identifier_expression(&index)),
                (Some(field_name("value")), identifier_expression(&value)),
            ],
        };
        let element_type = self.go_type(element)?;
        Ok(GoExpression::Function {
            parameters: vec![(index, GoType::Named("int32".into())), (value, element_type)],
            result: Some(record_type),
            body: vec![GoStatement::Return(Some(associate))],
        })
    }

    fn constructor_function(
        &mut self,
        monotype: MonotypeId,
        constructor: &str,
    ) -> GoResult<GoExpression> {
        let (data, index) = self.constructor_named(monotype, constructor)?;
        let payload = self.constructor_field_monotype(monotype, constructor, 0)?;
        let parameter = self.temporary("payload");
        let parameter_type = self.go_type(payload)?;
        let constructed = self.construct(&data, index, vec![identifier_expression(&parameter)])?;
        let result = self.go_type(monotype)?;
        Ok(GoExpression::Function {
            parameters: vec![(parameter, parameter_type)],
            result: Some(result),
            body: vec![GoStatement::Return(Some(constructed))],
        })
    }

    fn record_field_projection(
        &mut self,
        record: MonotypeId,
        label: &str,
    ) -> GoResult<GoExpression> {
        let Monotype::Record(fields) = self.monotypes.get(record).clone() else {
            unreachable!("invariant violated: a field projection has a record type")
        };
        let field_monotype = fields
            .iter()
            .find(|record_field| record_field.label == label)
            .expect("invariant violated: a projected field exists")
            .monotype;
        let body = self.read_field(identifier_expression("value"), record, label);
        Ok(GoExpression::Function {
            parameters: vec![("value".into(), self.go_type(record)?)],
            result: self.go_result(field_monotype)?,
            body: vec![GoStatement::Return(Some(body))],
        })
    }

    fn record_field_monotype(&self, record: MonotypeId, label: &str) -> MonotypeId {
        let Monotype::Record(fields) = self.monotypes.get(record) else {
            unreachable!("invariant violated: a record field of a non-record")
        };
        fields
            .iter()
            .find(|record_field| record_field.label == label)
            .expect("invariant violated: the record field exists")
            .monotype
    }

    fn make_aff(
        &mut self,
        arguments: &[Expression],
        out: &mut Vec<GoStatement>,
    ) -> GoResult<GoExpression> {
        let register = &arguments[0];
        let (callback, _) = self
            .monotypes
            .function_parts(register.monotype)
            .expect("invariant violated: makeAff registers a function");
        let (either, _) = self
            .monotypes
            .function_parts(callback)
            .expect("invariant violated: makeAff's callback is a function");
        let is_left = self.projection(either, "Left", None)?;
        let from_left = self.projection(either, "Left", Some(0))?;
        let from_right = self.projection(either, "Right", Some(0))?;
        let register = self.value(register, out)?;
        let function =
            self.go_function(GoFunction { package: GoPackage::Aff, name: "MakeAffDirect" });
        Ok(call(function, vec![is_left, from_left, from_right, register]))
    }

    fn fiber_record(
        &mut self,
        handle: GoExpression,
        record: MonotypeId,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<GoExpression> {
        let join = self.record_field_monotype(record, "join");
        let (callback, _) =
            self.monotypes.function_parts(join).expect("invariant violated: join takes a callback");
        let (either, _) = self
            .monotypes
            .function_parts(callback)
            .expect("invariant violated: join's callback is a function");
        let kill = self.record_field_monotype(record, "kill");
        let killing = self.monotypes.result_after(kill, 1);
        let (kill_callback, _) = self
            .monotypes
            .function_parts(killing)
            .expect("invariant violated: kill takes a callback");
        let (unit_either, _) = self
            .monotypes
            .function_parts(kill_callback)
            .expect("invariant violated: kill's callback is a function");
        let on_complete = self.record_field_monotype(record, "onComplete");
        let (completion, _) = self
            .monotypes
            .function_parts(on_complete)
            .expect("invariant violated: onComplete takes a record");
        let left = self.constructor_function(either, "Left")?;
        let right = self.constructor_function(either, "Right")?;
        let (unit_data, unit_right) = self.constructor_named(unit_either, "Right")?;
        let unit_right = self.construct(&unit_data, unit_right, vec![unit_value()])?;
        let handler = self.record_field_projection(completion, "handler")?;
        let function =
            self.go_function(GoFunction { package: GoPackage::Aff, name: "FiberFields" });
        let fields = call(function, vec![handle, left, right, unit_right, handler]);
        self.record_from_results(fields, record, out)
    }

    fn unfoldr(
        &mut self,
        foreign: Foreign,
        arguments: &[Expression],
        out: &mut Vec<GoStatement>,
    ) -> GoResult<GoExpression> {
        let producer = &arguments[4];
        let produced = self.monotypes.result_after(producer.monotype, 1);
        let (maybe, tuple) = match foreign {
            Foreign::Unfoldr => (produced, self.constructor_field_monotype(produced, "Just", 0)?),
            _ => (self.constructor_field_monotype(produced, "Tuple", 1)?, produced),
        };
        let is_nothing = self.projection(maybe, "Nothing", None)?;
        let from_just = self.projection(maybe, "Just", Some(0))?;
        let first = self.projection(tuple, "Tuple", Some(0))?;
        let second = self.projection(tuple, "Tuple", Some(1))?;
        let producer = self.value(producer, out)?;
        let seed = self.value(&arguments[5], out)?;
        let name = match foreign {
            Foreign::Unfoldr => "Unfoldr",
            _ => "Unfoldr1",
        };
        let function = self.go_function(GoFunction { package: GoPackage::Array, name });
        Ok(call(function, vec![is_nothing, from_just, first, second, producer, seed]))
    }

    fn constructor_field_monotype(
        &mut self,
        monotype: MonotypeId,
        constructor: &str,
        position: usize,
    ) -> GoResult<MonotypeId> {
        let (data, index) = self.constructor_named(monotype, constructor)?;
        let layout = self.data_layout(&data)?;
        Ok(layout.constructors[index].fields[position].1)
    }

    fn projection(
        &mut self,
        monotype: MonotypeId,
        constructor: &str,
        position: Option<usize>,
    ) -> GoResult<GoExpression> {
        let (data, index) = self.constructor_named(monotype, constructor)?;
        let layout = self.data_layout(&data)?;
        let parameter = identifier_expression("value");
        let constructor_layout = &layout.constructors[index];
        let (result, body) = match position {
            Some(position) => {
                let (field_name, field_monotype) = &constructor_layout.fields[position];
                (self.go_type(*field_monotype)?, field(parameter, field_name))
            }
            None => {
                let tag = identifier_expression(&constructor_layout.tag);
                let test = match layout.kind {
                    DataKind::Enumeration => binary("==", parameter, tag),
                    DataKind::Tagged => binary("==", field(parameter, "Tag"), tag),
                    DataKind::Product => GoExpression::Boolean(true),
                };
                (GoType::Bool, test)
            }
        };
        Ok(GoExpression::Function {
            parameters: vec![("value".into(), self.go_type(monotype)?)],
            result: Some(result),
            body: vec![GoStatement::Return(Some(body))],
        })
    }

    fn effect_loop(
        &mut self,
        foreign: Foreign,
        arguments: &[Expression],
        result: MonotypeId,
        sink: Sink,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<()> {
        let saved = self.tail_loop.take();
        let mut body = vec![];
        let condition = self.temporary("continuing");
        let (test, action) = match foreign {
            Foreign::EffectWhile => (&arguments[0], Some(&arguments[1])),
            _ => (&arguments[0], None),
        };
        self.sink(test, Mode::Perform, Sink::Define(condition.clone()), &mut body)?;
        let condition = identifier_expression(&condition);
        let stop = match foreign {
            Foreign::EffectWhile => {
                GoExpression::Unary { operator: "!", operand: Box::new(condition) }
            }
            _ => condition,
        };
        body.push(GoStatement::If {
            condition: stop,
            then: vec![GoStatement::Break],
            otherwise: vec![],
        });
        if let Some(action) = action {
            self.sink(action, Mode::Perform, Sink::Discard, &mut body)?;
        }
        self.tail_loop = saved;
        out.push(GoStatement::Loop(body));
        self.deliver(unit_value(), result, sink, out)
    }

    /// `withMutex mutex action` holds the lock while the action runs and releases
    /// it even when the action throws. As the last action of a Go function the lock
    /// is released by `defer`; elsewhere the critical section is its own closure.
    fn with_mutex(
        &mut self,
        arguments: &[Expression],
        result: MonotypeId,
        sink: Sink,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<()> {
        let mutex = self.value(&arguments[0], out)?;
        let mutex = self.hoist(mutex, "mutex", out);
        let lock = call(field(mutex.clone(), "Lock"), vec![]);
        let unlock = call(field(mutex, "Unlock"), vec![]);
        let saved = self.tail_loop.take();
        let outcome = if let Sink::Return = sink {
            out.push(GoStatement::Expression(lock));
            out.push(GoStatement::Defer(unlock));
            self.sink(&arguments[1], Mode::Perform, Sink::Return, out)
        } else {
            let mut body = vec![GoStatement::Expression(lock), GoStatement::Defer(unlock)];
            self.sink(&arguments[1], Mode::Perform, Sink::Return, &mut body).and_then(|()| {
                if let Some(GoStatement::Return(None)) = body.last() {
                    body.pop();
                }
                let result_type = self.go_result(result)?;
                let section =
                    GoExpression::Function { parameters: vec![], result: result_type, body };
                self.deliver(call(section, vec![]), result, sink, out)
            })
        };
        self.tail_loop = saved;
        outcome
    }

    fn lazy_defer(&mut self, thunk: &Expression, lazy: MonotypeId) -> GoResult<GoExpression> {
        let Monotype::Lazy(value) = *self.monotypes.get(lazy) else {
            unreachable!("invariant violated: defer returns a Lazy")
        };
        let unit = self.is_unit(value);
        let sink = move || if unit { Sink::Discard } else { Sink::Return };
        let saved = self.tail_loop.take();
        let mut body = vec![];
        let outcome = match &thunk.kind {
            ExpressionKind::Lambda { parameters, body: lambda_body } if parameters.len() == 1 => {
                self.locals.insert(parameters[0].id, unit_value());
                self.sink(lambda_body, Mode::Value, sink(), &mut body)
            }
            _ => self.value(thunk, &mut body).and_then(|function| {
                let callable = self.value_callable(function, thunk.monotype);
                let forced = self.apply_arguments(callable, vec![unit_value()], &mut body)?;
                self.deliver(forced, value, sink(), &mut body)
            }),
        };
        self.tail_loop = saved;
        outcome?;
        self.lazy_cell(value, body)
    }

    /// Whether a deferred body is a value already. Evaluating it when the
    /// cell is made costs less than the closure that would suspend it, and
    /// cannot fail, so no program can tell the difference. `does_no_work`
    /// is not enough: it admits a `Fail`, which must wait to be forced, and a
    /// constant, whose first use computes it. A local that a recursive binding
    /// is still assigning, as in `ones = defer \_ -> Cons 1 ones`, has no value
    /// yet; a lambda may capture it, since Go captures the variable.
    fn is_already_a_value(&self, expression: &Expression) -> bool {
        match &expression.kind {
            ExpressionKind::Literal(_) | ExpressionKind::Unit | ExpressionKind::Lambda { .. } => {
                true
            }
            ExpressionKind::Local(id) => !self.uninitialized_locals.contains(id),
            ExpressionKind::Function(id) => !self.program.function(*id).parameters.is_empty(),
            ExpressionKind::Construct { arguments, .. }
            | ExpressionKind::Array(arguments)
            | ExpressionKind::Closure { captures: arguments, .. } => {
                arguments.iter().all(|argument| self.is_already_a_value(argument))
            }
            ExpressionKind::Record(fields) => {
                fields.iter().all(|(_, value)| self.is_already_a_value(value))
            }
            ExpressionKind::Coerce(value) | ExpressionKind::Access { record: value, .. } => {
                self.is_already_a_value(value)
            }
            _ => false,
        }
    }

    pub(super) fn lazy_cell(
        &mut self,
        value: MonotypeId,
        mut body: Vec<GoStatement>,
    ) -> GoResult<GoExpression> {
        if self.is_unit(value) {
            body.push(GoStatement::Return(Some(unit_value())));
        }
        let result = Some(self.go_type(value)?);
        let thunk = GoExpression::Function { parameters: vec![], result, body };
        self.imports.insert(GoPackage::Lazy.path().into());
        let defer = GoExpression::Qualified { package: "lazy".into(), name: "Defer".into() };
        Ok(call(defer, vec![thunk]))
    }

    fn effect_for(
        &mut self,
        arguments: &[Expression],
        result: MonotypeId,
        sink: Sink,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<()> {
        let start = self.value(&arguments[0], out)?;
        // `index := 0` would be a Go int; the counter is a PureScript Int.
        let start = self.typed_constant(start, arguments[0].monotype)?;
        let end = self.value(&arguments[1], out)?;
        let end = self.hoist(end, "end", out);
        let saved = self.tail_loop.take();
        let mut body = vec![];
        let variable = if let ExpressionKind::Lambda { parameters, body: lambda_body } =
            &arguments[2].kind
            && let [parameter] = parameters.as_slice()
        {
            let variable = self.bind_local(parameter);
            self.sink(lambda_body, Mode::Perform, Sink::Discard, &mut body)?;
            variable
        } else {
            let action = self.value(&arguments[2], out)?;
            let action = self.hoist(action, "action", out);
            let variable = self.temporary("index");
            let performed = call(action, vec![identifier_expression(&variable)]);
            body.push(GoStatement::Expression(performed));
            variable
        };
        self.tail_loop = saved;
        out.push(GoStatement::Counting { variable, start, end, body });
        self.deliver(unit_value(), result, sink, out)
    }

    fn hoist(
        &mut self,
        value: GoExpression,
        base: &str,
        out: &mut Vec<GoStatement>,
    ) -> GoExpression {
        if is_simple(&value) {
            return value;
        }
        let name = self.temporary(base);
        out.push(GoStatement::Define { names: vec![name.clone()], values: vec![value] });
        identifier_expression(&name)
    }

    fn deliver(
        &mut self,
        value: GoExpression,
        monotype: MonotypeId,
        sink: Sink,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<()> {
        let unit = self.is_unit(monotype);
        match sink {
            Sink::Return => {
                if unit {
                    if is_effectful_call(&value) {
                        out.push(discarded(value));
                    }
                    out.push(GoStatement::Return(None));
                } else {
                    out.push(GoStatement::Return(Some(value)));
                }
            }
            Sink::Assign(name) => {
                if unit {
                    if is_effectful_call(&value) {
                        out.push(discarded(value));
                    }
                } else {
                    out.push(GoStatement::Assign {
                        targets: vec![identifier_expression(&name)],
                        values: vec![value],
                    });
                }
            }
            Sink::Define(name) => {
                if unit {
                    if is_effectful_call(&value) {
                        out.push(discarded(value));
                    }
                } else {
                    out.push(self.define(name, value, monotype)?);
                }
            }
            Sink::Discard => {
                if is_effectful_call(&value) {
                    out.push(discarded(value));
                }
            }
        }
        Ok(())
    }

    /// `x := 4` would give `x` Go's default `int`; constants need their declared type.
    fn define(
        &mut self,
        name: String,
        value: GoExpression,
        monotype: MonotypeId,
    ) -> GoResult<GoStatement> {
        if is_untyped_constant(&value)
            && !matches!(self.monotypes.get(monotype), Monotype::String | Monotype::Boolean)
        {
            let type_ = self.go_type(monotype)?;
            return Ok(GoStatement::Variable { name, type_, value: Some(value) });
        }
        Ok(GoStatement::Define { names: vec![name], values: vec![value] })
    }

    fn bindings(&mut self, bindings: &[Binding], out: &mut Vec<GoStatement>) -> GoResult<()> {
        let recursive = bindings
            .iter()
            .any(|binding| bindings.iter().any(|other| uses_local(&binding.value, other.local.id)));
        if recursive {
            let mut names = vec![];
            for binding in bindings {
                let name = self.bind_local(&binding.local);
                let type_ = self.go_type(binding.local.monotype)?;
                out.push(GoStatement::Variable { name: name.clone(), type_, value: None });
                names.push(name);
            }
            let group: Vec<LocalId> = bindings.iter().map(|binding| binding.local.id).collect();
            self.uninitialized_locals.extend(group.iter().copied());
            let mut outcome = Ok(());
            for (binding, name) in bindings.iter().zip(names) {
                let value = match self.value(&binding.value, out) {
                    Ok(value) => value,
                    Err(error) => {
                        outcome = Err(error);
                        break;
                    }
                };
                out.push(GoStatement::Assign {
                    targets: vec![identifier_expression(&name)],
                    values: vec![value],
                });
            }
            for local in group {
                self.uninitialized_locals.remove(&local);
            }
            return outcome;
        }
        for binding in bindings {
            if self.is_unit(binding.local.monotype) {
                let value = self.value(&binding.value, out)?;
                if is_effectful_call(&value) {
                    out.push(GoStatement::Expression(value));
                }
                self.locals.insert(binding.local.id, unit_value());
                continue;
            }
            let mut statements = vec![];
            let name = self.bind_local(&binding.local);
            self.sink(&binding.value, Mode::Value, Sink::Define(name), &mut statements)?;
            out.extend(statements);
        }
        Ok(())
    }

    fn values(
        &mut self,
        expressions: &[Expression],
        out: &mut Vec<GoStatement>,
    ) -> GoResult<Vec<GoExpression>> {
        expressions.iter().map(|expression| self.value(expression, out)).collect()
    }

    fn value(
        &mut self,
        expression: &Expression,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<GoExpression> {
        if self.monotypes.effect_result(expression.monotype).is_some() && is_effect_node(expression)
        {
            return self.thunk(expression);
        }
        Ok(match &expression.kind {
            ExpressionKind::Literal(literal) => self.literal(literal, expression.monotype),
            ExpressionKind::Unit => unit_value(),
            ExpressionKind::Array(elements) => {
                let type_ = self.go_type(expression.monotype)?;
                let mut fields = vec![];
                for element in elements {
                    fields.push((None, self.value(element, out)?));
                }
                GoExpression::Composite { type_, fields }
            }
            ExpressionKind::Record(fields) => {
                let mut values = vec![];
                for (label, value) in fields {
                    values.push((label.clone(), self.value(value, out)?));
                }
                self.record_value(expression.monotype, values)?
            }
            ExpressionKind::Access { record, label } => {
                let value = self.value(record, out)?;
                self.read_field(value, record.monotype, label)
            }
            ExpressionKind::Update { record: source, updates }
                if source.monotype != expression.monotype =>
            {
                let value = self.value(source, out)?;
                let value = self.hoist(value, "record", out);
                self.rebuilt_record(value, source.monotype, expression.monotype, updates, out)?
            }
            ExpressionKind::Update { record, updates } => {
                let record = self.value(record, out)?;
                let name = self.temporary("updated");
                out.push(GoStatement::Define { names: vec![name.clone()], values: vec![record] });
                let updated = identifier_expression(&name);
                self.updates(updated, expression.monotype, updates, out)?;
                identifier_expression(&name)
            }
            ExpressionKind::Local(id) => self.local(*id)?,
            ExpressionKind::Function(id) => self.function_value(*id, expression.monotype)?,
            ExpressionKind::Construct { data, constructor, arguments } => {
                let values = self.values(arguments, out)?;
                self.construct(data, *constructor, values)?
            }
            ExpressionKind::Reuse { cell, data, constructor, arguments } => {
                let values = self.values(arguments, out)?;
                let cell = self.value(cell, out)?;
                let layout = self.data_layout(data)?;
                let composite = self.composite(&layout, *constructor, values);
                let target = GoExpression::Unary { operator: "*", operand: Box::new(cell.clone()) };
                out.push(GoStatement::Assign { targets: vec![target], values: vec![composite] });
                cell
            }
            ExpressionKind::Foreign { foreign, arguments } => {
                self.foreign_value(*foreign, arguments, expression.monotype, out)?
            }
            ExpressionKind::Apply { function, arguments } => {
                let applied = self.application_value(function, arguments, out)?;
                if self.is_unit(expression.monotype) && is_effectful_call(&applied) {
                    out.push(GoStatement::Expression(applied));
                    return Ok(unit_value());
                }
                applied
            }
            ExpressionKind::Lambda { parameters, body } => {
                match self.constructor_as_value(expression.monotype, parameters, body)? {
                    Some(function) => function,
                    None => self.lambda(expression.monotype, parameters, body)?,
                }
            }
            ExpressionKind::Closure { tag, captures } => {
                let values = self.values(captures, out)?;
                self.closure_value(expression.monotype, *tag, values)?
            }
            ExpressionKind::Coerce(value) => {
                let coerced = self.value(value, out)?;
                self.coerce(coerced, value.monotype, expression.monotype, out)?
            }
            ExpressionKind::Let { bindings, body } => {
                self.bindings(bindings, out)?;
                self.value(body, out)?
            }
            ExpressionKind::Case { scrutinees, alternatives }
                if alternatives.first().is_some_and(|first| {
                    matches!(first.body, Guarded::Unconditional(_))
                        && first.patterns.iter().all(|pattern| self.is_total(pattern))
                }) =>
            {
                let first = &alternatives[0];
                let mut paths = vec![];
                for (scrutinee, pattern) in scrutinees.iter().zip(&first.patterns) {
                    if let PatternKind::Wildcard = pattern.kind {
                        paths.push(unit_value());
                        continue;
                    }
                    let value = self.value(scrutinee, out)?;
                    paths.push(self.hoist(value, "scrutinee", out));
                }
                let Guarded::Unconditional(body) = &first.body else { unreachable!() };
                let (_, bindings) = self.alternative_tests(&paths, &first.patterns)?;
                self.bind_pattern_locals(&bindings, |local| local_uses(body, local), out)?;
                self.value(body, out)?
            }
            ExpressionKind::If { .. } | ExpressionKind::Case { .. } => {
                if self.is_unit(expression.monotype) {
                    self.sink(expression, Mode::Value, Sink::Discard, out)?;
                    return Ok(unit_value());
                }
                let name = self.temporary("result");
                self.sink(expression, Mode::Value, Sink::Define(name.clone()), out)?;
                identifier_expression(&name)
            }
            ExpressionKind::Fail(message) => {
                out.push(panic_statement(message));
                let type_ = self.go_type(expression.monotype)?;
                let name = self.temporary("unreachable");
                out.push(GoStatement::Variable { name: name.clone(), type_, value: None });
                identifier_expression(&name)
            }
            ExpressionKind::EffectPure(_)
            | ExpressionKind::EffectBind { .. }
            | ExpressionKind::EffectEach { .. } => self.thunk(expression)?,
        })
    }

    fn construct(
        &mut self,
        data: &DataType,
        constructor: usize,
        values: Vec<GoExpression>,
    ) -> GoResult<GoExpression> {
        let layout = self.data_layout(data)?;
        let constructor_layout = layout.constructors[constructor].clone();
        Ok(match layout.kind {
            DataKind::Enumeration => identifier_expression(&constructor_layout.tag),
            DataKind::Tagged
                if layout.boxed
                    && !layout.erases_arguments
                    && constructor_layout.fields.is_empty() =>
            {
                self.shared_nullary(&layout.name, &constructor_layout.tag)
            }
            DataKind::Tagged | DataKind::Product => {
                let composite = self.composite(&layout, constructor, values);
                if layout.boxed { GoExpression::Address(Box::new(composite)) } else { composite }
            }
        })
    }

    fn composite(
        &self,
        layout: &DataLayout,
        constructor: usize,
        values: Vec<GoExpression>,
    ) -> GoExpression {
        let constructor_layout = &layout.constructors[constructor];
        let mut fields = vec![];
        if layout.kind == DataKind::Tagged {
            fields.push((Some("Tag".to_string()), identifier_expression(&constructor_layout.tag)));
        }
        for ((field_name, _), value) in constructor_layout.fields.iter().zip(values) {
            fields.push((Some(field_name.clone()), value));
        }
        GoExpression::Composite { type_: GoType::Named(layout.name.clone()), fields }
    }

    fn shared_nullary(&mut self, type_name: &str, tag: &str) -> GoExpression {
        if let Some(name) = self.shared_nullaries.get(tag) {
            return identifier_expression(name);
        }
        let name = self.global_name(Spelling::derived("shared", tag.into(), ""));
        let fields = vec![(Some("Tag".to_string()), identifier_expression(tag))];
        let composite = GoExpression::Composite { type_: GoType::Named(type_name.into()), fields };
        self.type_declarations.push(GoDeclaration::Variable {
            name: name.clone(),
            type_: None,
            value: GoExpression::Address(Box::new(composite)),
        });
        self.shared_nullaries.insert(tag.to_string(), name.clone());
        identifier_expression(&name)
    }

    fn constructor_named(
        &mut self,
        monotype: MonotypeId,
        name: &str,
    ) -> GoResult<(DataType, usize)> {
        let Monotype::Data(data) = self.monotypes.get(monotype).clone() else {
            return Err(GoError::Unsupported {
                definition: self.current_definition(),
                state: crate::error::UnsupportedState::Construct {
                    construct: "Maybe results of a non-Maybe type",
                },
            });
        };
        let constructors = self
            .monotypes
            .constructors(&mut self.context, &data)
            .map_err(|failure| failure.at(&self.current_definition()))?;
        let index =
            constructors.iter().position(|constructor| constructor.name == name).unwrap_or(0);
        Ok((data, index))
    }

    /// `xs !! i` as a bounds check rather than a call through Just and Nothing closures.
    fn maybe_index(
        &mut self,
        arguments: &[Expression],
        monotype: MonotypeId,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<GoExpression> {
        let (data, just) = self.constructor_named(monotype, "Just")?;
        let (_, nothing) = self.constructor_named(monotype, "Nothing")?;
        // Go rejects a constant negative index even in a branch that cannot run.
        if let ExpressionKind::Literal(Literal::Int(index)) = arguments[3].kind
            && index < 0
        {
            return self.construct(&data, nothing, vec![]);
        }
        let elements = self.value(&arguments[2], out)?;
        let elements = self.hoist(elements, "elements", out);
        let index = self.value(&arguments[3], out)?;
        let index = self.hoist(index, "index", out);
        let element = GoExpression::Index {
            value: Box::new(elements.clone()),
            index: Box::new(index.clone()),
        };
        let found = self.construct(&data, just, vec![element])?;
        let missing = self.construct(&data, nothing, vec![])?;
        let name = self.temporary("element");
        let type_ = self.go_type(monotype)?;
        out.push(GoStatement::Variable { name: name.clone(), type_, value: None });
        let length = call(identifier_expression("len"), vec![elements]);
        let widened =
            GoExpression::Conversion { type_: GoType::Int, value: Box::new(index.clone()) };
        let condition = binary(
            "&&",
            binary(">=", index, GoExpression::Integer(0)),
            binary("<", widened, length),
        );
        let target = vec![identifier_expression(&name)];
        out.push(GoStatement::If {
            condition,
            then: vec![GoStatement::Assign { targets: target.clone(), values: vec![found] }],
            otherwise: vec![GoStatement::Assign { targets: target, values: vec![missing] }],
        });
        Ok(identifier_expression(&name))
    }

    fn int_from_number(
        &mut self,
        number: &Expression,
        monotype: MonotypeId,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<GoExpression> {
        let number = self.value(number, out)?;
        let (data, just) = self.constructor_named(monotype, "Just")?;
        let (_, nothing) = self.constructor_named(monotype, "Nothing")?;
        // Go rejects `int32(c)` for a constant `c` that is not an int32, so a literal is decided here.
        if let Some(constant) = float_constant(&number) {
            let fits = constant.trunc() == constant
                && constant >= f64::from(i32::MIN)
                && constant <= f64::from(i32::MAX);
            if fits {
                return self.construct(&data, just, vec![GoExpression::Integer(constant as i64)]);
            }
            return self.construct(&data, nothing, vec![]);
        }
        let number = self.hoist(number, "number", out);
        let integer = GoExpression::Conversion {
            type_: GoType::Named("int32".into()),
            value: Box::new(number.clone()),
        };
        let found = self.construct(&data, just, vec![integer])?;
        let missing = self.construct(&data, nothing, vec![])?;
        self.imports.insert("math".into());
        let math =
            |name: &str| GoExpression::Qualified { package: "math".into(), name: name.into() };
        let whole = binary("==", call(math("Trunc"), vec![number.clone()]), number.clone());
        let condition = binary(
            "&&",
            whole,
            binary(
                "&&",
                binary(">=", number.clone(), math("MinInt32")),
                binary("<=", number, math("MaxInt32")),
            ),
        );
        let name = self.temporary("integer");
        let type_ = self.go_type(monotype)?;
        out.push(GoStatement::Variable { name: name.clone(), type_, value: None });
        let target = vec![identifier_expression(&name)];
        out.push(GoStatement::If {
            condition,
            then: vec![GoStatement::Assign { targets: target.clone(), values: vec![found] }],
            otherwise: vec![GoStatement::Assign { targets: target, values: vec![missing] }],
        });
        Ok(identifier_expression(&name))
    }

    /// A record update that changes field types (`r { f = g r.f }` at a new
    /// type) builds the result anew instead of copying the source's struct.
    fn rebuilt_record(
        &mut self,
        source: GoExpression,
        source_record: MonotypeId,
        target: MonotypeId,
        updates: &[RecordUpdate],
        out: &mut Vec<GoStatement>,
    ) -> GoResult<GoExpression> {
        let Monotype::Record(fields) = self.monotypes.get(target).clone() else {
            unreachable!("invariant violated: a record update produces a record")
        };
        let mut values = Vec::with_capacity(fields.len());
        for record_field in fields.iter() {
            let label = &record_field.label;
            let update = updates.iter().find(|update| match update {
                RecordUpdate::Leaf { label: updated, .. }
                | RecordUpdate::Branch { label: updated, .. } => updated == label,
            });
            let read = self.read_field(source.clone(), source_record, label);
            let value = match update {
                Some(RecordUpdate::Leaf { value, .. }) => self.value(value, out)?,
                Some(RecordUpdate::Branch { updates, .. }) => {
                    let nested = self.hoist(read, "record", out);
                    let nested_record = self.record_field_monotype(source_record, label);
                    let target = record_field.monotype;
                    self.rebuilt_record(nested, nested_record, target, updates, out)?
                }
                None => read,
            };
            values.push((label.clone(), value));
        }
        self.record_value(target, values)
    }

    fn updates(
        &mut self,
        target: GoExpression,
        record: MonotypeId,
        updates: &[RecordUpdate],
        out: &mut Vec<GoStatement>,
    ) -> GoResult<()> {
        for update in updates {
            match update {
                RecordUpdate::Leaf { label, value } => {
                    let value = self.value(value, out)?;
                    out.push(GoStatement::Assign {
                        targets: vec![self.read_field(target.clone(), record, label)],
                        values: vec![value],
                    });
                }
                RecordUpdate::Branch { label, updates } => {
                    let nested = self.read_field(target.clone(), record, label);
                    let nested_record = self.record_field_monotype(record, label);
                    self.updates(nested, nested_record, updates, out)?;
                }
            }
        }
        Ok(())
    }

    fn literal(&mut self, literal: &Literal, monotype: MonotypeId) -> GoExpression {
        match literal {
            Literal::Int(value) => GoExpression::Integer(*value),
            Literal::Number(value) => {
                // Folding leaves -0, NaN and the infinities, which Go spells
                // as calls.
                if let Ok(number) = value.parse::<f64>()
                    && (!number.is_finite() || (number == 0.0 && number.is_sign_negative()))
                {
                    return self.number_constant(number);
                }
                let mut value = value.to_string();
                if !value.contains(['.', 'e', 'E'])
                    && matches!(self.monotypes.get(monotype), Monotype::Number)
                {
                    value.push_str(".0");
                }
                GoExpression::Float(value)
            }
            Literal::String(value) => GoExpression::String(value.clone()),
            Literal::Char(value) => GoExpression::Rune(*value),
            Literal::Boolean(value) => GoExpression::Boolean(*value),
        }
    }

    /// A first-class effect: the only place an `Effect` becomes a Go closure.
    fn thunk(&mut self, expression: &Expression) -> GoResult<GoExpression> {
        let result =
            self.monotypes.effect_result(expression.monotype).unwrap_or(expression.monotype);
        let result_type = self.go_result(result)?;
        let saved = self.tail_loop.take();
        let mut body = vec![];
        self.sink(expression, Mode::Perform, Sink::Return, &mut body)?;
        self.tail_loop = saved;
        if let Some(GoStatement::Return(None)) = body.last() {
            body.pop();
        }
        Ok(GoExpression::Function { parameters: vec![], result: result_type, body })
    }

    fn application_value(
        &mut self,
        function: &Expression,
        arguments: &[Expression],
        out: &mut Vec<GoStatement>,
    ) -> GoResult<GoExpression> {
        let (callable, values) = self.application(function, arguments, 0, out)?;
        self.apply_arguments(callable, values, out)
    }

    fn application(
        &mut self,
        function: &Expression,
        arguments: &[Expression],
        extra: usize,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<(Callable, Vec<GoExpression>)> {
        let known = match function.kind {
            ExpressionKind::Function(id) if !self.program.function(id).parameters.is_empty() => {
                Some(self.known_callable(id, function.monotype))
            }
            _ => None,
        };
        let captured_by = known.as_ref().filter(|callee| callee.arity > arguments.len() + extra);
        let captured_by = captured_by.map(|callee| callee.names.clone());
        let mut values = vec![];
        for (position, argument) in arguments.iter().enumerate() {
            let value = self.value(argument, out)?;
            let value = match (&captured_by, value) {
                (_, value @ GoExpression::Function { .. }) | (None, value) => value,
                (Some(names), value) => self.shared(value, &names[position], out),
            };
            values.push(value);
        }
        let callable = match known {
            Some(callable) => callable,
            None => {
                let value = self.value(function, out)?;
                self.value_callable(value, function.monotype)
            }
        };
        Ok((callable, values))
    }

    fn foreign_value(
        &mut self,
        foreign: Foreign,
        arguments: &[Expression],
        monotype: MonotypeId,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<GoExpression> {
        if foreign.is_effectful() {
            let expression = Expression::new(
                ExpressionKind::Foreign { foreign, arguments: arguments.to_vec() },
                monotype,
            );
            return self.thunk(&expression);
        }
        if let Foreign::Range = foreign {
            let range = match &self.range_name {
                Some(name) => name.clone(),
                None => {
                    let name = self.global_name(Spelling::Base("rangeInt32".into()));
                    self.type_declarations
                        .push(GoDeclaration::Source { name: name.clone(), template: RANGE_SOURCE });
                    self.range_name = Some(name.clone());
                    name
                }
            };
            let values = self.values(arguments, out)?;
            return Ok(call(identifier_expression(&range), values));
        }
        if let Foreign::MaybeIndex = foreign {
            return self.maybe_index(arguments, monotype, out);
        }
        if let Foreign::IntFromNumber = foreign {
            return self.int_from_number(&arguments[2], monotype, out);
        }
        if let Foreign::Operator(Operator::StringAppend) = foreign
            && self.owned_snocs.contains(&std::ptr::from_ref(&arguments[0]))
        {
            return self.append_to_buffer(arguments, out);
        }
        if foreign.calls(crate::foreign::ARRAY_APPEND)
            && self.owned_snocs.contains(&std::ptr::from_ref(&arguments[0]))
            && let ExpressionKind::Array(elements) = &arguments[1].kind
        {
            let mut values = vec![self.value(&arguments[0], out)?];
            for element in elements {
                let value = self.value(element, out)?;
                values.push(self.typed_constant(value, element.monotype)?);
            }
            return Ok(call(identifier_expression("append"), values));
        }
        if let Foreign::Snoc = foreign {
            let array = self.value(&arguments[0], out)?;
            let element = self.value(&arguments[1], out)?;
            let element = self.typed_constant(element, arguments[1].monotype)?;
            if self.owned_snocs.contains(&std::ptr::from_ref(&arguments[0])) {
                return Ok(call(identifier_expression("append"), vec![array, element]));
            }
            let snoc = GoFunction { package: GoPackage::Array, name: "Snoc" };
            return Ok(call(self.go_function(snoc), vec![array, element]));
        }
        if let Foreign::LazyDefer = foreign {
            if let ExpressionKind::Lambda { parameters, body } = &arguments[0].kind
                && let [parameter] = parameters.as_slice()
                && self.is_already_a_value(body)
            {
                self.locals.insert(parameter.id, unit_value());
                let value = self.value(body, out)?;
                let value = self.typed_constant(value, body.monotype)?;
                self.imports.insert(GoPackage::Lazy.path().into());
                let mut evaluated =
                    GoExpression::Qualified { package: "lazy".into(), name: "Evaluated".into() };
                let type_ = self.go_type(body.monotype)?;
                if matches!(type_, GoType::Any | GoType::Erased(_)) {
                    // Go would infer the dynamic type of the value instead.
                    let function = Box::new(evaluated);
                    evaluated = GoExpression::Instantiation { function, arguments: vec![type_] };
                }
                return Ok(call(evaluated, vec![value]));
            }
            return self.lazy_defer(&arguments[0], monotype);
        }
        if let Foreign::LazyForce = foreign {
            if let ExpressionKind::Foreign { foreign: Foreign::LazyDefer, arguments: deferred } =
                &arguments[0].kind
                && let ExpressionKind::Lambda { parameters, body } = &deferred[0].kind
                && let [parameter] = parameters.as_slice()
            {
                self.locals.insert(parameter.id, unit_value());
                return self.value(body, out);
            }
            let lazy = self.value(&arguments[0], out)?;
            return Ok(call(field(lazy, "Force"), vec![]));
        }
        if let Foreign::RunEffect = foreign {
            if self.is_unit(monotype) {
                self.sink(&arguments[0], Mode::Perform, Sink::Discard, out)?;
                return Ok(unit_value());
            }
            let name = self.temporary("performed");
            self.sink(&arguments[0], Mode::Perform, Sink::Define(name.clone()), out)?;
            return Ok(identifier_expression(&name));
        }
        if let Foreign::RecordGet = foreign {
            let ExpressionKind::Literal(Literal::String(label)) = &arguments[0].kind else {
                return self.record_get_by_label(arguments, monotype, out);
            };
            let record = self.value(&arguments[1], out)?;
            return Ok(self.read_field(record, arguments[1].monotype, label));
        }
        if let Foreign::RecordHas = foreign {
            return Err(GoError::unsupported_construct("a label test on a value whose record type is not closed"));
        }
        if let Foreign::Record(_) = foreign {
            return Err(GoError::unsupported_construct("record builders with labels unknown at compile time"));
        }
        if let Foreign::Crash = foreign {
            let message = self.value(&arguments[0], out)?;
            out.push(GoStatement::Expression(call(identifier_expression("panic"), vec![message])));
            let type_ = self.go_type(monotype)?;
            let name = self.temporary("unreachable");
            out.push(GoStatement::Variable { name: name.clone(), type_, value: None });
            return Ok(identifier_expression(&name));
        }
        if let Foreign::Unfoldr | Foreign::Unfoldr1 = foreign {
            return self.unfoldr(foreign, arguments, out);
        }
        if let Foreign::Project { file_id, term, .. } = foreign {
            let called = self.project_call(file_id, term, arguments, monotype, out)?;
            return self.out_of_convention(called, monotype, out);
        }
        if let Foreign::Operator(Operator::ArrayLength) = foreign
            && self.is_fusible(&arguments[0], fusion::Demand::FORWARD)
        {
            return self.fused_length(&arguments[0], monotype, out);
        }
        if let Foreign::Call { boundary: Boundary { iteration: Some(iteration), .. }, .. } = foreign
            && let Some(iterated) = self.iteration(iteration, arguments, monotype, out)?
        {
            return Ok(iterated);
        }
        if let Foreign::Call { function, boundary, .. } = foreign {
            let values = self.boundary_arguments(arguments, boundary, monotype, true, out)?;
            let function = self.boundary_function(function, boundary, monotype)?;
            let result = call(function, values);
            if boundary.record_result {
                return self.record_from_results(result, monotype, out);
            }
            return Ok(result);
        }
        if let Foreign::ReferenceEqual = foreign {
            return self.reference_equal(&arguments[0], &arguments[1], out);
        }
        let mut values = self.values(arguments, out)?;
        Ok(match foreign {
            Foreign::Operator(Operator::Compare(comparison))
                if !matches!(comparison, Comparison::Equal | Comparison::NotEqual)
                    && matches!(self.monotypes.get(arguments[0].monotype), Monotype::String) =>
            {
                self.string_ordering(comparison, values)
            }
            Foreign::Operator(operator) => self.operator(operator, values),
            Foreign::Constant(function) => {
                self.imports.insert(function.package.path().into());
                let constant = GoExpression::Qualified {
                    package: function.package.name().into(),
                    name: function.name.into(),
                };
                self.narrow(constant, monotype)
            }
            Foreign::Unit => unit_value(),
            Foreign::UnsafeCoerce => {
                self.coerce(values.remove(0), arguments[0].monotype, monotype, out)?
            }
            Foreign::Identity => values.remove(0),
            _ => unreachable!("invariant violated: effectful foreign reached value conversion"),
        })
    }

    /// `unsafeGet label record` with a label known only at run time, over a
    /// record whose fields the specialised type fixes: a switch over the
    /// labels of the fields that can stand at the requested type. A field
    /// whose type has a different shape cannot be the one read, since the
    /// caller uses the result at its own type; `Data.Variant` reads its
    /// handlers this way after asking `unsafeHas`.
    fn record_get_by_label(
        &mut self,
        arguments: &[Expression],
        monotype: MonotypeId,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<GoExpression> {
        let Monotype::Record(fields) = self.monotypes.get(arguments[1].monotype).clone() else {
            return Err(GoError::unsupported_construct("record access through a run-time label into a value that is not a closed record"));
        };
        let label = self.value(&arguments[0], out)?;
        let record = self.value(&arguments[1], out)?;
        let record = self.shared(record, "record", out);
        let chosen = self.temporary("field");
        let mut cases = Vec::with_capacity(fields.len());
        for record_field in fields.iter() {
            let mut body = vec![];
            let read = self.read_field(record.clone(), arguments[1].monotype, &record_field.label);
            let value = match self.coerce(read, record_field.monotype, monotype, &mut body) {
                Ok(value) => value,
                Err(GoError::Unsupported {
                    state: crate::error::UnsupportedState::Construct { construct },
                    ..
                }) if construct == coerce::UNRELATED_TYPES => continue,
                Err(error) => return Err(error),
            };
            body.push(GoStatement::Assign {
                targets: vec![identifier_expression(&chosen)],
                values: vec![value],
            });
            let label = GoExpression::String(record_field.label.to_string());
            cases.push(GoCase { values: vec![label], body });
        }
        if cases.is_empty() {
            return Err(GoError::unsupported_construct("record access through a run-time label where no field has the requested type"));
        }
        let type_ = self.go_type(monotype)?;
        out.push(GoStatement::Variable { name: chosen.clone(), type_, value: None });
        out.push(GoStatement::Switch { value: Some(label), cases, default: None });
        Ok(identifier_expression(&chosen))
    }

    /// go-support represents PureScript `Int` as Go `int`; generated code uses
    /// `int32`, whose overflow wraps exactly like JavaScript's `| 0`.
    fn narrow(&mut self, value: GoExpression, monotype: MonotypeId) -> GoExpression {
        if let Monotype::Int = self.monotypes.get(monotype) {
            return GoExpression::Conversion {
                type_: GoType::Named("int32".into()),
                value: Box::new(value),
            };
        }
        value
    }

    fn fold_number(
        &mut self,
        operator: Operator,
        left: &GoExpression,
        right: &GoExpression,
    ) -> Option<GoExpression> {
        let fold: fn(f64, f64) -> f64 = match operator {
            Operator::NumberAdd => |left, right| left + right,
            Operator::NumberSubtract => |left, right| left - right,
            Operator::NumberMultiply => |left, right| left * right,
            Operator::NumberDivide => |left, right| left / right,
            _ => return None,
        };
        let folded = fold(float_constant(left)?, float_constant(right)?);
        Some(self.number_constant(folded))
    }

    fn number_constant(&mut self, value: f64) -> GoExpression {
        let math =
            |name: &str| GoExpression::Qualified { package: "math".into(), name: name.into() };
        if value.is_nan() {
            self.imports.insert("math".into());
            return call(math("NaN"), vec![]);
        }
        if value.is_infinite() {
            self.imports.insert("math".into());
            let sign = if value < 0.0 { -1 } else { 1 };
            return call(math("Inf"), vec![GoExpression::Integer(sign)]);
        }
        if value == 0.0 && value.is_sign_negative() {
            self.imports.insert("math".into());
            let zero = GoExpression::Integer(0);
            return call(math("Copysign"), vec![zero, GoExpression::Integer(-1)]);
        }
        GoExpression::Float(format!("{value:?}"))
    }

    fn string_ordering(
        &mut self,
        comparison: Comparison,
        values: Vec<GoExpression>,
    ) -> GoExpression {
        let package = GoPackage::Prim;
        self.imports.insert(package.path().into());
        let function = GoExpression::Qualified {
            package: package.name().into(),
            name: "CompareString".into(),
        };
        let ordering = call(function, values);
        let zero = GoExpression::Integer(0);
        self.operator(Operator::Compare(comparison), vec![ordering, zero])
    }

    fn operator(&mut self, operator: Operator, mut values: Vec<GoExpression>) -> GoExpression {
        let unary = |operator: &'static str, values: &mut Vec<GoExpression>| GoExpression::Unary {
            operator,
            operand: Box::new(values.remove(0)),
        };
        if operator.arity() == 1 {
            return match operator {
                Operator::NumberNegate => match float_constant(&values[0]) {
                    Some(value) => self.number_constant(-value),
                    None => unary("-", &mut values),
                },
                Operator::IntNegate => unary("-", &mut values),
                Operator::BooleanNot => unary("!", &mut values),
                Operator::ArrayLength => GoExpression::Conversion {
                    type_: GoType::Named("int32".into()),
                    value: Box::new(call(identifier_expression("len"), values)),
                },
                Operator::IntToNumber => GoExpression::Conversion {
                    type_: GoType::Float64,
                    value: Box::new(values.remove(0)),
                },
                Operator::IntComplement => unary("^", &mut values),
                _ => unreachable!(),
            };
        }
        let right = values.pop().expect("invariant violated: binary operator arity");
        let left = values.pop().expect("invariant violated: binary operator arity");
        if let Operator::ArrayIndex = operator {
            return GoExpression::Index { value: Box::new(left), index: Box::new(right) };
        }
        if let Some(bitwise) = bitwise(operator, left.clone(), right.clone()) {
            return bitwise;
        }
        if let Operator::IntMultiply = operator {
            let multiply = GoFunction { package: GoPackage::Prim, name: "MultiplyInt32" };
            return call(self.go_function(multiply), vec![left, right]);
        }
        if let Some(folded) = self.fold_number(operator, &left, &right) {
            return folded;
        }
        if let Operator::NumberDivide = operator
            && is_untyped_constant(&left)
            && is_untyped_constant(&right)
        {
            let left = GoExpression::Conversion { type_: GoType::Float64, value: Box::new(left) };
            return binary("/", left, right);
        }
        // Go folds untyped constants exactly; JavaScript rounds every step.
        let left = match operator {
            Operator::NumberAdd | Operator::NumberSubtract | Operator::NumberMultiply
                if is_untyped_constant(&left) && is_untyped_constant(&right) =>
            {
                GoExpression::Conversion { type_: GoType::Float64, value: Box::new(left) }
            }
            _ => left,
        };
        if let Operator::NumberMultiply = operator
            && !(is_untyped_constant(&left) && is_untyped_constant(&right))
        {
            // Go may fuse `a*b + c` into one rounding (FMA on arm64); JavaScript
            // rounds the product first. An explicit conversion forces that.
            let product = binary("*", left, right);
            return GoExpression::Conversion { type_: GoType::Float64, value: Box::new(product) };
        }
        let symbol = match operator {
            Operator::IntAdd | Operator::NumberAdd | Operator::StringAppend => "+",
            Operator::IntSubtract | Operator::NumberSubtract => "-",
            Operator::NumberMultiply => "*",
            Operator::NumberDivide => "/",
            Operator::BooleanAnd => "&&",
            Operator::BooleanOr => "||",
            Operator::Compare(comparison) => match comparison {
                Comparison::Equal => "==",
                Comparison::NotEqual => "!=",
                Comparison::LessThan => "<",
                Comparison::LessThanOrEqual => "<=",
                Comparison::GreaterThan => ">",
                Comparison::GreaterThanOrEqual => ">=",
            },
            _ => unreachable!(),
        };
        binary(symbol, left, right)
    }

}

const RANGE_SOURCE: &str = "func {name}(start int32, end int32) []int32 {
\tstep := int32(1)
\tif start > end {
\t\tstep = -1
\t}
\telements := []int32{start}
\tfor value := start; value != end; {
\t\tvalue += step
\t\telements = append(elements, value)
\t}
\treturn elements
}
";

/// The Data.Int.Bits operators, which follow JavaScript: operands are int32 and
/// shift counts are taken modulo 32. Constant operands are folded so that Go never
/// sees an untyped constant overflow int32 or uint32.
fn bitwise(operator: Operator, left: GoExpression, right: GoExpression) -> Option<GoExpression> {
    let symbol = match operator {
        Operator::IntAnd => "&",
        Operator::IntOr => "|",
        Operator::IntXor => "^",
        Operator::IntShiftLeft => "<<",
        Operator::IntShiftRight | Operator::IntZeroFillShiftRight => ">>",
        _ => return None,
    };
    if let (Some(x), Some(y)) = (int32_constant(&left), int32_constant(&right)) {
        return Some(GoExpression::Integer(fold_bitwise(operator, x, y)));
    }
    let shifts = !matches!(operator, Operator::IntAnd | Operator::IntOr | Operator::IntXor);
    if !shifts {
        return Some(binary(symbol, left, right));
    }
    let count = match int32_constant(&right) {
        Some(count) => GoExpression::Integer(i64::from(count & 31)),
        None => binary("&", right, GoExpression::Integer(31)),
    };
    let int32 = || GoType::Named("int32".into());
    if let Operator::IntZeroFillShiftRight = operator {
        let unsigned = match int32_constant(&left) {
            Some(x) => GoExpression::Integer(i64::from(x as u32)),
            None => left,
        };
        let unsigned = GoExpression::Conversion {
            type_: GoType::Named("uint32".into()),
            value: Box::new(unsigned),
        };
        return Some(GoExpression::Conversion {
            type_: int32(),
            value: Box::new(binary(symbol, unsigned, count)),
        });
    }
    let left = match is_untyped_constant(&left) {
        true => GoExpression::Conversion { type_: int32(), value: Box::new(left) },
        false => left,
    };
    Some(binary(symbol, left, count))
}

fn float_constant(expression: &GoExpression) -> Option<f64> {
    match expression {
        GoExpression::Integer(value) => Some(*value as f64),
        GoExpression::Float(value) => value.parse().ok(),
        GoExpression::Unary { operator: "-", operand } => {
            float_constant(operand).map(|value| -value)
        }
        _ => None,
    }
}

fn int32_constant(expression: &GoExpression) -> Option<i32> {
    match expression {
        GoExpression::Integer(value) => i32::try_from(*value).ok(),
        GoExpression::Unary { operator: "-", operand } => match operand.as_ref() {
            GoExpression::Integer(value) => i32::try_from(-*value).ok(),
            _ => None,
        },
        _ => None,
    }
}

pub(crate) fn fold_bitwise(operator: Operator, x: i32, y: i32) -> i64 {
    let count = (y & 31) as u32;
    i64::from(match operator {
        Operator::IntAnd => x & y,
        Operator::IntOr => x | y,
        Operator::IntXor => x ^ y,
        Operator::IntShiftLeft => x.wrapping_shl(count),
        Operator::IntShiftRight => x >> count,
        _ => ((x as u32) >> count) as i32,
    })
}

fn is_untyped_constant(expression: &GoExpression) -> bool {
    match expression {
        GoExpression::Integer(_) | GoExpression::Float(_) | GoExpression::Rune(_) => true,
        GoExpression::Unary { operand, .. } => is_untyped_constant(operand),
        GoExpression::Binary { left, right, .. } => {
            is_untyped_constant(left) && is_untyped_constant(right)
        }
        _ => false,
    }
}

fn is_effect_node(expression: &Expression) -> bool {
    matches!(
        expression.kind,
        ExpressionKind::EffectPure(_)
            | ExpressionKind::EffectBind { .. }
            | ExpressionKind::EffectEach { .. }
    ) || matches!(&expression.kind, ExpressionKind::Foreign { foreign, .. } if foreign.is_effectful())
        || matches!(&expression.kind, ExpressionKind::Apply { .. })
}

fn ends_in_panic(statements: &[GoStatement]) -> bool {
    statements.last().is_some_and(GoStatement::is_panic)
}

fn breaks_to(statements: &[GoStatement], label: &str) -> bool {
    statements.iter().any(|statement| match statement {
        GoStatement::BreakTo(target) => target == label,
        GoStatement::If { then, otherwise, .. } => {
            breaks_to(then, label) || breaks_to(otherwise, label)
        }
        GoStatement::Switch { cases, default, .. } => {
            cases.iter().any(|case| breaks_to(&case.body, label))
                || default.as_ref().is_some_and(|default| breaks_to(&default.body, label))
        }
        GoStatement::IfAssert { then, .. } => breaks_to(then, label),
        GoStatement::Loop(body)
        | GoStatement::LabeledLoop { body, .. }
        | GoStatement::Range { body, .. }
        | GoStatement::Counting { body, .. }
        | GoStatement::CountingDown { body, .. } => breaks_to(body, label),
        _ => false,
    })
}

fn ends_in_jump(statements: &[GoStatement]) -> bool {
    matches!(statements.last(), Some(GoStatement::Return(_) | GoStatement::Continue))
        || ends_in_panic(statements)
}

fn has_tail_call(expression: &Expression, function: FunctionId, arity: usize, mode: Mode) -> bool {
    match &expression.kind {
        ExpressionKind::Apply { function: callee, arguments } => {
            matches!(callee.kind, ExpressionKind::Function(id) if id == function)
                && arguments.len() == arity
        }
        ExpressionKind::Let { body, .. } => has_tail_call(body, function, arity, mode),
        ExpressionKind::If { then, otherwise, .. } => {
            has_tail_call(then, function, arity, mode)
                || has_tail_call(otherwise, function, arity, mode)
        }
        ExpressionKind::Case { alternatives, .. } => {
            alternatives.iter().any(|alternative| match &alternative.body {
                Guarded::Unconditional(body) => has_tail_call(body, function, arity, mode),
                Guarded::Guards(branches) => {
                    branches.iter().any(|branch| has_tail_call(&branch.body, function, arity, mode))
                }
            })
        }
        ExpressionKind::EffectBind { body, .. } if mode == Mode::Perform => {
            has_tail_call(body, function, arity, mode)
        }
        _ => false,
    }
}

fn captures_parameters(
    expression: &Expression,
    parameters: &[Local],
    mode: Mode,
    monotypes: &Monotypes,
) -> bool {
    let uses_parameter = |expression: &Expression| {
        parameters.iter().any(|parameter| uses_local(expression, parameter.id))
    };
    let captures = |expression: &Expression, mode: Mode| {
        captures_parameters(expression, parameters, mode, monotypes)
    };
    if mode == Mode::Value
        && is_effect_node(expression)
        && monotypes.effect_result(expression.monotype).is_some()
    {
        return uses_parameter(expression);
    }
    match &expression.kind {
        ExpressionKind::Lambda { body, .. } => uses_parameter(body),
        ExpressionKind::EffectPure(value) if mode == Mode::Perform => captures(value, Mode::Value),
        ExpressionKind::EffectBind { action, body, .. } if mode == Mode::Perform => {
            captures(action, Mode::Perform) || captures(body, Mode::Perform)
        }
        ExpressionKind::EffectPure(_)
        | ExpressionKind::EffectBind { .. }
        | ExpressionKind::EffectEach { .. } => uses_parameter(expression),
        ExpressionKind::Let { bindings, body } => {
            bindings.iter().any(|binding| captures(&binding.value, Mode::Value))
                || captures(body, mode)
        }
        ExpressionKind::If { condition, then, otherwise } => {
            captures(condition, Mode::Value) || captures(then, mode) || captures(otherwise, mode)
        }
        ExpressionKind::Case { scrutinees, alternatives } => {
            scrutinees.iter().any(|scrutinee| captures(scrutinee, Mode::Value))
                || alternatives.iter().any(|alternative| match &alternative.body {
                    Guarded::Unconditional(body) => captures(body, mode),
                    Guarded::Guards(branches) => branches.iter().any(|branch| {
                        branch.guards.iter().any(|guard| match guard {
                            Guard::Boolean(condition) => captures(condition, Mode::Value),
                            Guard::Pattern { value, .. } => captures(value, Mode::Value),
                        }) || captures(&branch.body, mode)
                    }),
                })
        }
        _ => {
            let mut captured = false;
            crate::simplify::for_each_child(expression, &mut |child| {
                captured = captured || captures(child, Mode::Value);
            });
            captured
        }
    }
}

/// The type of a `Ref` cell holding values of the given type.
fn reference_type(value: GoType) -> GoType {
    GoType::Generic { name: "Ref".into(), arguments: vec![value] }
}
