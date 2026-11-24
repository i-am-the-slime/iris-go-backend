//! Rendering of the simplified monomorphic tree as Go.
//! Values of type `Effect a` are Go `func() A`, and a function `a -> Effect b` is a
//! Go `func(A) B` that performs its effects when called. Effectful code is emitted
//! in perform mode, where binds become statements and `pure x` becomes `x`; an
//! effect only turns into a closure where it is used as a first-class value.

mod aliases;
mod application;
mod blocks;
mod boxing;
mod buffers;
mod build;
mod cases;
mod cells;
mod chunks;
mod closures;
mod coerce;
mod composites;
mod conditions;
mod constructors;
mod conventions;
mod declarations;
mod deduplicate;
mod diverging;
mod divisions;
mod effects;
mod equality;
mod existential;
mod field_reads;
mod foreign_data;
mod foreign_values;
mod forwarders;
mod found;
mod fresh;
mod from_list;
mod fusion;
mod groups;
mod guards;
mod headers;
mod immediate;
mod inlining;
mod inspection;
mod instantiations;
mod int64;
mod intervals;
mod invariants;
mod iteration;
mod joins;
mod json;
mod kept;
mod known;
mod labelled;
mod layout;
mod lengths;
mod lines;
mod loads;
mod locals;
mod loop_state;
mod maybe;
mod merging;
mod mutable;
mod names;
mod operators;
mod overwrite;
mod ownership;
mod packages;
mod printing;
mod project;
mod ranges;
mod recycling;
mod reference_equality;
mod references;
mod reuse;
mod scalars;
mod shorthands;
mod sorting;
mod standard;
mod strings;
mod swaps;
mod text;
mod types;
mod unreferenced;
mod unzip;
mod updates;
mod vector;
mod views;
mod wrappers;

use std::collections::BTreeSet;
use std::sync::Arc;

use rustc_hash::{FxHashMap, FxHashSet};

use files::FileId;

use self::application::Callable;
use self::build::*;
use self::declarations::{await_fibers, recursive_constants};
use self::operators::is_untyped_constant;
use self::overwrite::with_unique_mask;
use self::packages::Spelling;
use crate::arity::Arities;
use crate::context::Context;
use crate::error::{GoError, GoResult};
use crate::foreign::{Constructed, ForeignPackages, GoFunction, GoPackage};
use crate::modules::{ModuleIndex, Modules};
use crate::monomorphic::traversal::visit;
use crate::monomorphic::{
    Binding, Expression, ExpressionKind, FunctionId, Guarded, Literal, Local, LocalId, Pattern,
    PatternKind, Program, RecordUpdate, Results,
};
use crate::monotype::{DataType, Monotype, MonotypeId, Monotypes};
use crate::naming::identifier;
use crate::syntax::{
    DeclarationNames, GoDeclaration, GoExpression, GoStatement, GoType, Name, SourceLine,
    statements_names,
};
use crate::timing::timed;

pub(crate) use self::closures::Eliminators;
pub use self::packages::GoSourceFile;
pub use self::vector::{KERNEL_FILE_SUFFIXES, is_kernel_file};

pub fn emit_program<Q>(
    mut program: Program,
    monotypes: &mut Monotypes,
    eliminators: &Eliminators,
    queries: &Q,
    foreign_packages: &ForeignPackages,
    modules: &Modules,
    module_path: &str,
) -> GoResult<(Vec<GoSourceFile>, Vec<String>)>
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
        probe.copied_by_containers = probe.data_copied_by_containers()?;
        let reused = reuse::reuse_cells(program, &mut probe);
        GoResult::Ok((reused, probe.copied_by_containers))
    });
    let (reused, copied_by_containers) = reused?;
    let program = &reused.program;
    let mut emitter = Emitter::new(program, monotypes, queries, foreign_packages, arities);
    emitter.copied_by_containers = copied_by_containers;
    emitter.materialized = reused.materialized;
    emitter.candidates = reused.candidates;
    emitter.closure_sets = closure_sets;
    emitter.vector_kernels = vector::Kernels::new(program);
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
        emitter.pending_variants(&mut declarations)?;
        let main = emitter.main()?;
        emitter.note_homes(main.as_slice(), entry_origin);
        declarations.extend(main);
        emitter.pending_variants(&mut declarations)?;
        emitter.delegate_to_writers(&mut declarations);
        // First, so that a top-level value that reads one finds it registered.
        let registrations = emitter.foreign_data_registrations()?;
        declarations.splice(0..0, registrations);
        GoResult::Ok(declarations)
    });
    let mut declarations = declarations?;
    let unused = emitter.unused_tail_group_entries();
    if !unused.is_empty() {
        declarations
            .retain(|declaration| declaration.name().is_none_or(|name| !unused.contains(name)));
    }
    let every_line = emitter
        .foreign_packages
        .line_directives
        .as_ref()
        .is_some_and(|directives| directives.coverage == crate::foreign::LineCoverage::Every);
    if emitter.imports.contains(GoPackage::Aff.path())
        || emitter.foreign_packages.imports_event_loop(&emitter.imports)
    {
        let await_ = GoFunction { package: GoPackage::EventLoop, name: "Await" };
        let await_ = emitter.performing(await_);
        await_fibers(&mut declarations, await_, every_line);
    }
    let lines_aside = every_line.then(|| lines::set_aside(&mut declarations));
    timed("wrappers", || wrappers::inline_wrappers(&mut declarations));
    let structs = scalars::structs_of(&emitter.type_declarations);
    timed("equality", || equality::compare_structs_whole(&mut declarations, &structs));
    timed("labelled", || labelled::unlabel_blocks(&mut declarations));
    timed("known", || known::drop_known_tests(&mut declarations));
    timed("merging", || merging::merge_identical_branches(&mut declarations));
    timed("fresh", || fresh::drop_clips_of_fresh_slices(&mut declarations));
    timed("references", || references::promote_references(&mut declarations));
    timed("composites", || composites::take_composites_apart(&mut declarations));
    timed("immediate", || immediate::reduce_immediate_calls(&mut declarations));
    timed("conditions", || conditions::assign_conditions(&mut declarations));
    timed("aliases", || aliases::substitute_aliases(&mut declarations));
    timed("updates", || updates::update_in_place(&mut declarations));
    timed("scalars", || scalars::split_struct_locals(&mut declarations, &structs));
    timed("stores", || scalars::store_fields_in_place(&mut declarations, &structs));
    timed("aliases", || aliases::substitute_aliases(&mut declarations));
    timed("inlining", || {
        inlining::inline_called_cell_loops(&mut declarations, &structs);
        inlining::inline_cell_constructors(&mut declarations);
    });
    timed("forwarding", || {
        cells::forward_constructed_fields(&mut declarations);
        cells::substitute_cell_aliases(&mut declarations);
    });
    timed("aliases", || aliases::substitute_aliases(&mut declarations));
    timed("references", || references::promote_references(&mut declarations));
    let helpers: FxHashSet<String> = emitter.support_functions.values().cloned().collect();
    let never_recovering = emitter.foreign_packages.packages_that_never_recover();
    timed("cells", || {
        cells::keep_parameter_cells_in_locals(
            &mut declarations,
            &helpers,
            &emitter.effects,
            &never_recovering,
        )
    });
    timed("joins", || joins::join_shared_updates(&mut declarations));
    timed("ranges", || ranges::read_elements_in_place(&mut declarations));
    timed("swaps", || swaps::swap_crosswise_pokes(&mut declarations));
    let effects = std::mem::take(&mut emitter.effects);
    timed("headers", || headers::read_headers_once(&mut declarations, &effects));
    timed("bounds", || headers::drop_repeated_bounds_tests(&mut declarations, &effects));
    timed("guards", || guards::guard_accesses_together(&mut declarations, &effects));
    timed("intervals", || intervals::prove_bounds(&mut declarations, &effects));
    timed("divisions", || divisions::reduce_constant_divisions(&mut declarations));
    timed("shorthands", || shorthands::use_shorthands(&mut declarations));
    let taken =
        |name: &str| emitter.global_names.contains(name) || IMPORTED_PACKAGES.contains(&name);
    timed("lengths", || lengths::count_lengths_up_to_comparisons(&mut declarations));
    let mut names: Vec<DeclarationNames> = timed("names used", || {
        declarations.iter_mut().map(GoDeclaration::declared_names).collect()
    });
    timed("invariant lengths", || {
        lengths::hoist_loop_invariant_lengths(&mut declarations, &mut names, &taken)
    });
    timed("invariants", || {
        invariants::hoist_loop_invariants(&mut declarations, &mut names, &taken)
    });
    let chunked = timed("chunks", || {
        chunks::allocate_linked_cells_in_chunks(&mut declarations, &mut names, &taken)
    });
    if chunked {
        emitter.imports.insert(GoPackage::Alloc.path().into());
    }
    timed("blocks", || {
        blocks::allocate_nested_cells_together(&mut declarations, &mut names, &taken)
    });
    timed("divergence", || diverging::end_blocks_at_divergence(&mut declarations));
    timed("field reads", || loads::reuse_field_reads(&mut declarations));
    let forwarders = forwarders::Forwarders::new(emitter.foreign_packages);
    timed("forwarders", || forwarders.call_methods(&mut declarations));
    timed("unreferenced", || unreferenced::drop_unreferenced_definitions(&mut declarations));
    // Last, so that every pass before reads the constructions' fields in their literals.
    timed("constructions", || emitter.call_constructor_functions(&mut declarations))?;
    if let Some(aside) = lines_aside {
        lines::restore(&mut declarations, aside);
    }
    let mut homes: FxHashMap<String, ModuleIndex> = std::mem::take(&mut emitter.homes)
        .into_iter()
        .filter_map(|(name, file)| Some((name, modules.index(file)?)))
        .collect();
    // The homes of the declarations each declaration stands for.
    let mut merged: FxHashMap<String, Vec<Option<ModuleIndex>>> = FxHashMap::default();
    let mut declarations = timed("deduplicate", || {
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
    let spans = std::mem::take(&mut emitter.spans);
    timed("spans", || lines::attribute_spans(&mut declarations, spans));
    let home = |declaration: &GoDeclaration| {
        let name = match declaration {
            GoDeclaration::Constants { names, .. } => names.first().map(String::as_str),
            declaration => declaration.name(),
        };
        name.and_then(|name| homes.get(name)).copied()
    };
    emitter.settle_array_boxes()?;
    emitter.settle_round_trips();
    emitter.spell_out_generic_alias_arguments();
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
    let mut files = timed("packages", || packaging.split(all))?;
    vector::attach_kernels(&mut files, &emitter.vector_kernels);
    if std::env::var_os("IRIS_GO_ANY_CENSUS").is_some() {
        let mut census = crate::erasure::Census::default();
        let mut textual = 0;
        for file in &files {
            let (source, file_census) = file.file.render_with_census();
            census.absorb(file_census);
            let identifier = |character: char| character.is_alphanumeric() || character == '_';
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
        for (erasure, count) in census.rows() {
            eprintln!("any-cause {} {count}", erasure.name());
        }
    }
    Ok((files, emitter.notes))
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
            array_boxes: Default::default(),
            recursive_names: FxHashMap::default(),
            type_aliases: FxHashMap::default(),
            type_declarations: vec![],
            reference_declared: false,
            support_functions: FxHashMap::default(),
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
            recycled_maps: FxHashMap::default(),
            vector_kernels: vector::Kernels::default(),
            byte_buffers: FxHashMap::default(),
            owning_variants: FxHashMap::default(),
            pending_owning_variants: vec![],
            writers: FxHashMap::default(),
            pending_writers: vec![],
            writable: FxHashMap::default(),
            array_writers: FxHashMap::default(),
            pending_array_writers: vec![],
            array_shows: FxHashMap::default(),
            pending_array_shows: vec![],
            inline_shapes: FxHashMap::default(),
            copied_by_containers: FxHashSet::default(),
            shared_nullaries: FxHashMap::default(),
            json_decoders: FxHashMap::default(),
            json_encoders: FxHashMap::default(),
            foreign_error_shows: FxHashMap::default(),
            maybe_helpers: maybe::MaybeHelpers::new(),
            constructor_functions: FxHashMap::default(),
            named_constructions: FxHashMap::default(),
            construction_functions: FxHashMap::default(),
            cell_types: FxHashMap::default(),
            reaching: FxHashMap::default(),
            holding: FxHashMap::default(),
            erasing: FxHashMap::default(),
            erasing_layouts: FxHashMap::default(),
            materialized: FxHashSet::default(),
            candidates: FxHashSet::default(),
            edge_bits: FxHashMap::default(),
            unique_rooms: FxHashMap::default(),
            effects: FxHashSet::default(),
            notes: vec![],
            foreign_data: vec![],
            uninitialized_locals: FxHashSet::default(),
            current: None,
            lazy_constants,
            arities,
            source_lines: lines::SourceLines::default(),
            spans: lines::Spans::default(),
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
    Write(String),
    Append(String),
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
    line: Option<&'e SourceLine>,
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
    parameters: Vec<GoExpression>,
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
    maybe: Option<maybe::MaybeLayout>,
    edges: Option<std::rc::Rc<layout::EdgeBits>>,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum DataKind {
    Enumeration,
    Tagged,
    Product,
    /// A boxed type with one constructor that has fields, such as `Leaf | Node ...` or
    /// `Nil | Cons ...`. Each nullary constructor is one shared cell, and a value is told apart
    /// by whether it is one of them, so the struct needs no tag: `m == sharedMapLeaf` is a
    /// comparison with an address, where `m.Tag == MapLeaf` loads from the cell.
    Sentinel,
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
    /// The constructions of sum types that a constructor function may build, by the Go struct
    /// and tag their composite literals carry.
    named_constructions: FxHashMap<constructors::ConstructionKey, (DataType, usize)>,
    /// The constructor function of each such construction, shared with the constructors
    /// used as values.
    construction_functions: FxHashMap<constructors::ConstructionKey, String>,
    round_trips: Vec<coerce::RoundTrip>,
    array_boxes: boxing::ArrayBoxes,
    recursive_names: FxHashMap<DataType, String>,
    /// The type each recursive newtype's alias spells.
    type_aliases: FxHashMap<String, GoType>,
    type_declarations: Vec<GoDeclaration>,
    reference_declared: bool,
    /// The name of each support function declared so far, by the base of its name.
    support_functions: FxHashMap<&'static str, String>,
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
    /// The maps that build a tail loop's next array in the buffers it recycles, by their
    /// callbacks.
    recycled_maps: FxHashMap<*const Expression, recycling::Recycled>,
    vector_kernels: vector::Kernels,
    /// The string parameters of the tail loop being emitted that it builds in a `[]byte`, with
    /// the buffer's name; the parameter itself reads `string(buffer)`.
    byte_buffers: FxHashMap<LocalId, String>,
    owning_variants: FxHashMap<(FunctionId, usize), String>,
    pending_owning_variants: Vec<(FunctionId, usize)>,
    writers: FxHashMap<FunctionId, String>,
    pending_writers: Vec<FunctionId>,
    writable: FxHashMap<FunctionId, bool>,
    array_writers: FxHashMap<FunctionId, (String, MonotypeId)>,
    pending_array_writers: Vec<FunctionId>,
    /// The function that shows a whole array as a string through its array writer.
    array_shows: FxHashMap<FunctionId, String>,
    pending_array_shows: Vec<FunctionId>,
    inline_shapes: FxHashMap<DataType, Option<layout::Shape>>,
    /// The data types that a cell or an array copies whenever it is copied;
    /// only these keep the smaller limit on being held by value.
    copied_by_containers: FxHashSet<DataType>,
    shared_nullaries: FxHashMap<String, String>,
    /// The typed Yoga.JSON decoder and encoder of each type, by their names.
    json_decoders: FxHashMap<MonotypeId, String>,
    json_encoders: FxHashMap<MonotypeId, String>,
    /// The function that shows a Yoga.JSON read's errors, by the type of the errors.
    foreign_error_shows: FxHashMap<MonotypeId, String>,
    maybe_helpers: maybe::MaybeHelpers,
    cell_types: FxHashMap<DataType, bool>,
    reaching: FxHashMap<(DataType, DataType), bool>,
    holding: FxHashMap<(MonotypeId, DataType), bool>,
    erasing: FxHashMap<MonotypeId, bool>,
    erasing_layouts: FxHashMap<DataType, bool>,
    materialized: FxHashSet<(FunctionId, LocalId)>,
    candidates: FxHashSet<DataType>,
    edge_bits: FxHashMap<DataType, Option<std::rc::Rc<layout::EdgeBits>>>,
    unique_rooms: FxHashMap<DataType, bool>,
    /// The Go functions the emitted code calls to run an effect.
    effects: headers::Effects,
    /// What the program does differently from the JavaScript backend's, for the user.
    notes: Vec<String>,
    /// The data types, at their erased arguments, whose values may reach a `Foreign`.
    foreign_data: Vec<MonotypeId>,
    /// The locals of the recursive bindings being assigned, which still hold
    /// Go's zero value.
    uninitialized_locals: FxHashSet<LocalId>,
    arities: Arities,
    source_lines: lines::SourceLines,
    spans: lines::Spans,
}

/// The largest data type held by value that cells and arrays copy.
const INLINE_DATA_LIMIT: usize = 128;
/// The largest data type held by value otherwise: a result or a step that is
/// matched once, where a pointer would cost an allocation per value.
const TRANSIENT_DATA_LIMIT: usize = 256;

impl DataLayout {
    fn go_type(&self) -> GoType {
        if let Some(maybe::MaybeLayout::Pointer { .. }) = &self.maybe {
            unreachable!("invariant violated: a pointer Maybe has its payload's type")
        }
        let named = GoType::Named(self.name.clone());
        if self.boxed { GoType::Pointer(Box::new(named)) } else { named }
    }
}

/// A field's Go name, for a struct whose fields are known not to collide: exported, since
/// the struct may live in another package than the code that builds or reads it.
fn field_name(label: &str) -> String {
    crate::naming::go_field(label)
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
    "eventloop",
    "promise",
    "foreignvalue",
    "tauri",
    "regex",
    "alloc",
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

#[derive(Clone, Copy)]
enum Direction {
    ToConvention,
    FromConvention,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Crossing {
    Boxed,
    Native,
}

impl Crossing {
    fn native_when(native: bool) -> Crossing {
        if native { Crossing::Native } else { Crossing::Boxed }
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
        GoExpression::Field { value, .. } | GoExpression::Conversion { value, .. } => {
            path_root(value)
        }
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
                let guards: usize =
                    branch.guards.iter().map(|guard| local_uses(guard.value(), local)).sum();
                guards + local_uses(&branch.body, local)
            })
            .sum(),
    }
}

impl<'q, Q> Emitter<'_, '_, 'q, Q>
where
    Q: checking::ExternalQueries,
{
    /// `path:line:column: ` of the offset in the file, with lines and columns from 1.
    fn location(&mut self, file_id: FileId, offset: Option<u32>) -> GoResult<String> {
        let Some(offset) = offset else { return Ok(String::new()) };
        let Some((_, path)) =
            self.foreign_packages.source_paths.iter().find(|(id, _)| *id == file_id)
        else {
            return Ok(String::new());
        };
        let path = path.clone();
        let content = self.context.queries.content(file_id)?;
        // A syntax node's range starts at the whitespace in front of it.
        let start = (offset as usize).min(content.len());
        let start = start + (content[start..].len() - content[start..].trim_start().len());
        let before = &content[..start];
        let line = before.matches('\n').count() + 1;
        let column = before.rsplit('\n').next().map_or(0, |text| text.chars().count()) + 1;
        Ok(format!("{path}:{line}:{column}: "))
    }

    /// A type as the program spells it, for messages.
    fn purescript_type(&mut self, monotype: MonotypeId) -> GoResult<String> {
        Ok(match self.monotypes.get(monotype).clone() {
            Monotype::Data(data) | Monotype::ForeignData(data) | Monotype::Recursive(data) => {
                let module = self.context.module(data.file_id)?.name.clone();
                format!("{module}.{}", self.context.type_name(data.file_id, data.item)?)
            }
            Monotype::Int => "Int".into(),
            Monotype::Int64 => "Int64".into(),
            Monotype::UInt64 => "UInt64".into(),
            Monotype::Number => "Number".into(),
            Monotype::String => "String".into(),
            Monotype::Boolean => "Boolean".into(),
            Monotype::Char => "Char".into(),
            Monotype::Unit => "Unit".into(),
            Monotype::Array(element) => format!("Array {}", self.purescript_type(element)?),
            Monotype::Record(fields) => {
                let labels: Vec<&str> = fields.iter().map(|field| field.label.as_str()).collect();
                format!("{{ {} }}", labels.join(", "))
            }
            _ => self.go_type(monotype)?.render(),
        })
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
        let start = out.len();
        let line = self.span_line(expression.position)?;
        let enclosing = self.spans.enter(line);
        let sunk = self.sink_unattributed(expression, mode, sink, out);
        self.spans.leave(enclosing);
        sunk?;
        self.attribute(expression.position, start, out)
    }

    fn sink_unattributed(
        &mut self,
        expression: &Expression,
        mode: Mode,
        sink: Sink,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<()> {
        if let Sink::Write(buffer) = &sink
            && self.write_text(expression, buffer, out)?
        {
            return Ok(());
        }
        if let Sink::Append(array) = &sink
            && let ExpressionKind::Array(elements) = &expression.kind
        {
            return self.append_elements(array, elements, out);
        }
        match &expression.kind {
            ExpressionKind::Let { bindings, body } => {
                self.bindings(bindings, out)?;
                self.sink(body, mode, sink, out)
            }
            ExpressionKind::If { condition, then, otherwise } => {
                let line = self.branch_line(condition.position)?;
                let otherwise_line = self.branch_line(otherwise.position)?;
                let condition = self.value(condition, out)?;
                let sink = self.prepare_branching_sink(sink, expression, mode, out)?;
                let mut then_statements = vec![];
                self.sink(then, mode, sink.clone(), &mut then_statements)?;
                let mut otherwise_statements = vec![];
                self.sink(otherwise, mode, sink.clone(), &mut otherwise_statements)?;
                if let Sink::Return = sink
                    && ends_in_jump(&then_statements)
                {
                    let branch =
                        GoStatement::If { condition, then: then_statements, otherwise: vec![] };
                    lines::push_at(line, branch, out);
                    out.extend(otherwise_statements);
                } else {
                    lines::open_otherwise_at(otherwise_line, &mut otherwise_statements);
                    let branch = GoStatement::If {
                        condition,
                        then: then_statements,
                        otherwise: otherwise_statements,
                    };
                    lines::push_at(line, branch, out);
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
            ExpressionKind::Foreign {
                foreign: crate::foreign::Foreign::Json(crate::foreign::JsonCodec::Read),
                arguments,
            } if mode == Mode::Value && !matches!(sink, Sink::Write(_) | Sink::Append(_)) => {
                self.json_read(&arguments[0], &arguments[1], expression.monotype, sink, out)
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
        parameters: &[GoExpression],
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
                && let Some(buffer) = self.byte_buffers.get(&id)
                && same_place(parameter, &identifier_expression(buffer))
            {
                continue;
            }
            let value = self.value(argument, out)?;
            if same_place(&value, parameter) {
                continue;
            }
            targets.push(parameter.clone());
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
            return self.deliver_expression(expression, sink, out);
        }
        let result =
            self.monotypes.effect_result(expression.monotype).unwrap_or(expression.monotype);
        match &expression.kind {
            ExpressionKind::EffectPure(value) => self.deliver_expression(value, sink, out),
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
            ExpressionKind::EffectEach { array, element, body, results: Results::Discarded }
                if self.is_fusible(array, fusion::Demand::FORWARD) =>
            {
                self.each_fused(array, element, body, out)?;
                self.deliver(unit_value(), result, sink, out)
            }
            ExpressionKind::EffectEach { array, element, body, results: Results::Collected } => {
                let collected = self.collect_each(array, element, body, result, out)?;
                self.deliver(collected, result, sink, out)
            }
            ExpressionKind::EffectEach { array, element, body, .. } => {
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
                self.perform_foreign(**foreign, arguments, result, sink, out)
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

    fn typed_argument(
        &mut self,
        value: GoExpression,
        argument: &Expression,
    ) -> GoResult<GoExpression> {
        let constant = matches!(value, GoExpression::String(_) | GoExpression::Boolean(_));
        if !constant && self.coerced_into_interface(argument)? {
            let type_ = self.go_type(argument.monotype)?;
            return Ok(GoExpression::Conversion { type_, value: Box::new(value) });
        }
        self.typed_constant(value, argument.monotype)
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

    /// Whether a function or effect returns Unit within `layers` applications or performances.
    fn has_unit_result(&self, monotype: MonotypeId, layers: usize) -> bool {
        if layers == 0
            || !matches!(self.monotypes.get(monotype), Monotype::Function(..) | Monotype::Effect(_))
        {
            return false;
        }
        let (_, result) = self.callable_parts(monotype);
        self.is_unit(result) || self.has_unit_result(result, layers - 1)
    }

    /// The Go type of a value whose Unit results within `layers` are Unit's value, `struct{}`.
    fn unit_valued_type(&mut self, monotype: MonotypeId, layers: usize) -> GoResult<GoType> {
        if self.is_unit(monotype) {
            return Ok(GoType::EmptyStruct);
        }
        if !self.has_unit_result(monotype, layers) {
            return self.go_type(monotype);
        }
        let (parameter, result) = self.callable_parts(monotype);
        let parameters = match parameter {
            Some(parameter) => vec![self.go_type(parameter)?],
            None => vec![],
        };
        let result = self.unit_valued_type(result, layers - 1)?;
        Ok(GoType::Function { parameters, result: Some(Box::new(result)) })
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

    fn deliver_expression(
        &mut self,
        expression: &Expression,
        sink: Sink,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<()> {
        let value = self.value(expression, out)?;
        if let Sink::Define(name) = &sink
            && self.coerced_into_interface(expression)?
        {
            let type_ = self.go_type(expression.monotype)?;
            out.push(GoStatement::Variable { name: name.clone(), type_, value: Some(value) });
            return Ok(());
        }
        self.deliver(value, expression.monotype, sink, out)
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
                } else if !aliases::is_named(&value, &name) {
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
            Sink::Write(buffer) => {
                let appended = self.text_append(&buffer, value);
                out.push(GoStatement::Assign {
                    targets: vec![identifier_expression(&buffer)],
                    values: vec![appended],
                });
            }
            Sink::Append(array) => {
                let appended = call(
                    identifier_expression("append"),
                    vec![identifier_expression(&array), GoExpression::Spread(Box::new(value))],
                );
                out.push(GoStatement::Assign {
                    targets: vec![identifier_expression(&array)],
                    values: vec![appended],
                });
            }
        }
        Ok(())
    }

    fn append_elements(
        &mut self,
        array: &str,
        elements: &[Expression],
        out: &mut Vec<GoStatement>,
    ) -> GoResult<()> {
        if elements.is_empty() {
            return Ok(());
        }
        let mut arguments = vec![identifier_expression(array)];
        for element in elements {
            arguments.push(self.value(element, out)?);
        }
        out.push(GoStatement::Assign {
            targets: vec![identifier_expression(array)],
            values: vec![call(identifier_expression("append"), arguments)],
        });
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
            let value = (!is_nil(&value)).then_some(value);
            return Ok(GoStatement::Variable { name, type_, value });
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
                let start = out.len();
                let value = self.value(&binding.value, out)?;
                if is_effectful_call(&value) {
                    out.push(GoStatement::Expression(value));
                }
                self.attribute(binding.value.position, start, out)?;
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
        let line = self.span_line(expression.position)?;
        let enclosing = self.spans.enter(line.clone());
        let value = self.value_unattributed(expression, out);
        self.spans.leave(enclosing);
        let value = value?;
        if let Some(line) = line {
            self.spans.record(&value, line);
        }
        Ok(value)
    }

    fn value_unattributed(
        &mut self,
        expression: &Expression,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<GoExpression> {
        if self.monotypes.effect_result(expression.monotype).is_some() && is_effect_node(expression)
        {
            return self.thunk(expression, out);
        }
        if self.builds_text(expression) {
            return self.buffered_text(expression, out);
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
                    let value = self.field_value(expression.monotype, label, value, out)?;
                    values.push((label.clone(), value));
                }
                self.record_value(expression.monotype, values)?
            }
            ExpressionKind::Access { record, label } => {
                let value = self.value(record, out)?;
                let read = self.read_field(value, record.monotype, label);
                match self.argument_groups(record.monotype, label) {
                    Some(groups) => {
                        let read = self.shared(read, "function", out);
                        self.curried_from_groups(read, expression.monotype, &groups)?
                    }
                    None => read,
                }
            }
            ExpressionKind::Update { record: source, updates }
                if !self.monotypes.same_without_causes(source.monotype, expression.monotype) =>
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
            ExpressionKind::Reuse { .. } => self.reused(&expression.kind, &[], out)?,
            ExpressionKind::UniqueEdge { owned, cell, edge } => {
                self.unique_edge(owned, cell, edge, out)?
            }
            ExpressionKind::UniqueEdges { value, edges } => match &value.kind {
                ExpressionKind::Construct { data, constructor, arguments } => {
                    let values = self.values(arguments, out)?;
                    let mask = self.unique_mask(data, *constructor, edges, None, out)?;
                    let constructed = self.construct(data, *constructor, values)?;
                    with_unique_mask(constructed, mask)
                }
                ExpressionKind::Reuse { .. } => self.reused(&value.kind, edges, out)?,
                _ => unreachable!(
                    "invariant violated: unique edges mark neither a construction nor a reuse"
                ),
            },
            ExpressionKind::Foreign { foreign, arguments } => match self.built(expression, out)? {
                Some(built) => built,
                None => self.foreign_value(foreign, arguments, expression.monotype, out)?,
            },
            ExpressionKind::Apply { function, arguments } => {
                let applied = self.application_value(function, arguments, out)?;
                if self.is_unit(expression.monotype) && is_effectful_call(&applied) {
                    out.push(GoStatement::Expression(applied));
                    return Ok(unit_value());
                }
                applied
            }
            ExpressionKind::Lambda { parameters, body } => {
                if let Some(callee) = self.eta_reduced(expression.monotype, parameters, body)? {
                    return self.value(callee, out);
                }
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
                self.coerce_at(coerced, value.monotype, expression.monotype, out)?
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
                    let base = scrutinee_name(&value);
                    paths.push(self.hoist(value, &base, out));
                }
                let Guarded::Unconditional(body) = &first.body else { unreachable!() };
                let (_, bindings) = self.alternative_tests(&paths, &first.patterns)?;
                self.bind_pattern_locals(&bindings, |local| local_uses(body, local), out)?;
                self.value(body, out)?
            }
            ExpressionKind::If { .. } | ExpressionKind::Case { .. }
                if let Some(condition) = shown_boolean(expression) =>
            {
                let condition = self.value(condition, out)?;
                self.format_boolean(condition)
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
            | ExpressionKind::EffectEach { .. } => self.thunk(expression, out)?,
        })
    }

    fn construct(
        &mut self,
        data: &DataType,
        constructor: usize,
        values: Vec<GoExpression>,
    ) -> GoResult<GoExpression> {
        let layout = self.data_layout(data)?;
        if let Some(maybe) = &layout.maybe {
            return self.construct_maybe(&layout, maybe, constructor, values);
        }
        let constructor_layout = layout.constructors[constructor].clone();
        Ok(match layout.kind {
            DataKind::Enumeration => identifier_expression(&constructor_layout.tag),
            DataKind::Tagged
                if layout.boxed
                    && !layout.erases_arguments
                    && constructor_layout.fields.is_empty() =>
            {
                let line = self.nullary_line(data, constructor)?;
                self.shared_nullary(&layout.name, &constructor_layout.tag, true, line)
            }
            DataKind::Sentinel if constructor_layout.fields.is_empty() => {
                let line = self.nullary_line(data, constructor)?;
                self.shared_nullary(&layout.name, &constructor_layout.tag, false, line)
            }
            DataKind::Tagged | DataKind::Product | DataKind::Sentinel => {
                if let Some(key) = self.construction_key(&layout, constructor)? {
                    self.named_constructions.insert(key, (data.clone(), constructor));
                }
                let composite = self.composite(&layout, constructor, values);
                if layout.boxed { GoExpression::Address(Box::new(composite)) } else { composite }
            }
        })
    }

    pub(super) fn composite(
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

    /// The one cell of a nullary constructor of a boxed type. A `Sentinel` type's struct has no
    /// tag; its cells are told apart by their addresses.
    fn shared_nullary(
        &mut self,
        type_name: &str,
        tag: &str,
        tagged: bool,
        line: Option<SourceLine>,
    ) -> GoExpression {
        if let Some(name) = self.shared_nullaries.get(tag) {
            return identifier_expression(name);
        }
        let name = self.global_name(Spelling::derived("shared", tag.into(), ""));
        let fields = if tagged {
            vec![(Some("Tag".to_string()), identifier_expression(tag))]
        } else {
            vec![]
        };
        let composite = GoExpression::Composite { type_: GoType::Named(type_name.into()), fields };
        self.type_declarations.push(GoDeclaration::Variable {
            name: name.clone(),
            type_: None,
            value: GoExpression::Address(Box::new(composite)),
            line,
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
                Some(RecordUpdate::Leaf { value, .. }) => {
                    self.field_value(target, label, value, out)?
                }
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
                    let value = self.field_value(record, label, value, out)?;
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

    fn field_value(
        &mut self,
        record: MonotypeId,
        label: &str,
        value: &Expression,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<GoExpression> {
        match self.argument_groups(record, label) {
            Some(groups) => self.grouped_value(value, &groups, out),
            None => self.value(value, out),
        }
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
            Literal::Utf16(units) => GoExpression::Utf16(Arc::clone(units)),
            Literal::Char(value) => GoExpression::Rune(*value),
            Literal::Boolean(value) => GoExpression::Boolean(*value),
        }
    }

    /// A first-class effect: the only place an `Effect` becomes a Go closure.
    fn thunk(
        &mut self,
        expression: &Expression,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<GoExpression> {
        let result =
            self.monotypes.effect_result(expression.monotype).unwrap_or(expression.monotype);
        let result_type = self.go_result(result)?;
        match &expression.kind {
            ExpressionKind::Let { bindings, body } => {
                self.bindings(bindings, out)?;
                return self.thunk(body, out);
            }
            ExpressionKind::EffectPure(value) if self.builds_eagerly(value) => {
                let value = self.value(value, out)?;
                let value = self.hoist(value, "pure", out);
                let returned = (!self.is_unit(result)).then_some(GoStatement::Return(Some(value)));
                let body = returned.into_iter().collect();
                return Ok(GoExpression::Function {
                    parameters: vec![],
                    result: result_type,
                    body,
                });
            }
            ExpressionKind::EffectBind { action, local, body }
                if let ExpressionKind::EffectPure(value) = &action.kind
                    && self.builds_eagerly(value) =>
            {
                let value = self.value(value, out)?;
                if uses_local(body, local.id) && !self.is_unit(local.monotype) {
                    let name = self.bind_local(local);
                    out.push(self.define(name, value, local.monotype)?);
                } else {
                    self.locals.insert(local.id, unit_value());
                    if is_effectful_call(&value) {
                        out.push(discarded(value));
                    }
                }
                return self.deferred_thunk(body, result_type);
            }
            _ => {}
        }
        self.deferred_thunk(expression, result_type)
    }

    fn builds_eagerly(&self, value: &Expression) -> bool {
        !self.is_already_a_value(value) && !crate::purity::is_discardable(value)
    }

    fn deferred_thunk(
        &mut self,
        expression: &Expression,
        result_type: Option<GoType>,
    ) -> GoResult<GoExpression> {
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
        if let ExpressionKind::Coerce(inner) = &function.kind
            && self.applies_through_coercion(inner.monotype, function.monotype, arguments.len())?
        {
            let values = self.values(arguments, out)?;
            let coerced = self.value(inner, out)?;
            return self.coerce_applied(coerced, inner.monotype, function.monotype, values, out);
        }
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
        let callable = match (known, &function.kind) {
            (Some(callable), _) => callable,
            (None, ExpressionKind::Access { record, label })
                if let Some(groups) = self.argument_groups(record.monotype, label) =>
            {
                let value = self.value(record, out)?;
                let read = self.read_field(value, record.monotype, label);
                if values.len() < groups.iter().sum() {
                    let read = self.shared(read, "function", out);
                    let curried = self.curried_from_groups(read, function.monotype, &groups)?;
                    return Ok((self.value_callable(curried, function.monotype), values));
                }
                let (&last, leading) = groups.split_last().expect("invariant violated: groups");
                let mut called = read;
                let mut monotype = function.monotype;
                for &size in leading {
                    called = call(called, values.drain(..size).collect());
                    monotype = self.monotypes.result_after(monotype, size);
                }
                Callable { function: called, monotype, arity: last, names: vec![] }
            }
            (None, _) => {
                let value = self.value(function, out)?;
                self.value_callable(value, function.monotype)
            }
        };
        Ok((callable, values))
    }

    /// The name of a support function, declared from its template on first use.
    pub(super) fn support_function(
        &mut self,
        base: &'static str,
        template: &'static str,
    ) -> String {
        if let Some(name) = self.support_functions.get(base) {
            return name.clone();
        }
        let name = self.global_name(Spelling::Base(base.into()));
        self.type_declarations.push(GoDeclaration::Source { name: name.clone(), template });
        self.support_functions.insert(base, name.clone());
        name
    }
}

/// The Boolean that `expression` chooses `"true"` or `"false"` on, as `show` does.
fn shown_boolean(expression: &Expression) -> Option<&Expression> {
    let says = |branch: &Expression, word: &str| matches!(&branch.kind, ExpressionKind::Literal(Literal::String(text)) if text == word);
    match &expression.kind {
        ExpressionKind::If { condition, then, otherwise }
            if says(then, "true") && says(otherwise, "false") =>
        {
            Some(condition)
        }
        ExpressionKind::Case { scrutinees, alternatives } => {
            let ([scrutinee], [first, second]) = (scrutinees.as_slice(), alternatives.as_slice())
            else {
                return None;
            };
            let (Some(tested), first_body) = boolean_branch(first)? else { return None };
            let (other, second_body) = boolean_branch(second)?;
            let word = |value: bool| if value { "true" } else { "false" };
            let shows = says(first_body, word(tested))
                && other.is_none_or(|other| other != tested)
                && says(second_body, word(!tested));
            shows.then_some(scrutinee)
        }
        _ => None,
    }
}

/// The Boolean an alternative of one column matches, if it does not match any, and its body.
fn boolean_branch(
    alternative: &crate::monomorphic::Alternative,
) -> Option<(Option<bool>, &Expression)> {
    match (&alternative.patterns[0].kind, &alternative.body) {
        (PatternKind::Literal(Literal::Boolean(value)), Guarded::Unconditional(body)) => {
            Some((Some(*value), body))
        }
        (PatternKind::Wildcard, Guarded::Unconditional(body)) => Some((None, body)),
        _ => None,
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

fn has_tail_call(expression: &Expression, function: FunctionId, arity: usize, mode: Mode) -> bool {
    !tail_calls(expression, function, arity, mode).is_empty()
}

fn tail_calls(
    expression: &Expression,
    function: FunctionId,
    arity: usize,
    mode: Mode,
) -> Vec<&[Expression]> {
    let mut calls = vec![];
    collect_tail_calls(expression, function, arity, mode, &mut calls);
    calls
}

fn collect_tail_calls<'e>(
    expression: &'e Expression,
    function: FunctionId,
    arity: usize,
    mode: Mode,
    calls: &mut Vec<&'e [Expression]>,
) {
    let bodies: Vec<&'e Expression> = match &expression.kind {
        ExpressionKind::Apply { function: callee, arguments } => {
            if matches!(callee.kind, ExpressionKind::Function(id) if id == function)
                && arguments.len() == arity
            {
                calls.push(arguments);
            }
            vec![]
        }
        ExpressionKind::Let { body, .. } => vec![body],
        ExpressionKind::If { then, otherwise, .. } => vec![then, otherwise],
        ExpressionKind::Case { alternatives, .. } => {
            let mut bodies = vec![];
            for alternative in alternatives {
                match &alternative.body {
                    Guarded::Unconditional(body) => bodies.push(body),
                    Guarded::Guards(branches) => {
                        bodies.extend(branches.iter().map(|branch| &branch.body));
                    }
                }
            }
            bodies
        }
        ExpressionKind::EffectBind { body, .. } if mode == Mode::Perform => vec![body],
        _ => vec![],
    };
    for body in bodies {
        collect_tail_calls(body, function, arity, mode, calls);
    }
}

fn same_place(left: &GoExpression, right: &GoExpression) -> bool {
    match (left, right) {
        (GoExpression::Identifier(left), GoExpression::Identifier(right)) => left == right,
        (
            GoExpression::Field { value: left_value, name: left_name },
            GoExpression::Field { value: right_value, name: right_name },
        ) => left_name == right_name && same_place(left_value, right_value),
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
                        branch.guards.iter().any(|guard| captures(guard.value(), Mode::Value))
                            || captures(&branch.body, mode)
                    }),
                })
        }
        _ => {
            let mut captured = false;
            crate::monomorphic::traversal::for_each_child(expression, &mut |child| {
                captured = captured || captures(child, Mode::Value);
            });
            captured
        }
    }
}
