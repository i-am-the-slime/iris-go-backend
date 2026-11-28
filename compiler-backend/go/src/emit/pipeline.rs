use rustc_hash::{FxHashMap, FxHashSet};

use super::builders::Worker;
use super::closures::{ClosureSet, Eliminators};
use super::declarations::await_fibers;
use super::headers::Effects;
use super::lines::SetAside;
use super::packages::{GoSourceFile, Packaging};
use super::reuse::Reused;
use super::{
    Emitter, IMPORTED_PACKAGES, aliases, array_parameters, ascii_heads, blocks, branch_tests,
    branches, builders, cells, chunks, closures, composites, conditions, confined, constant_fields,
    deduplicate, diverging, divisions, equality, forwarders, fresh, groups, guards, hash_maps,
    headers, immediate, index_arrays, inlining, intervals, invariants, joins, known, labelled,
    lengths, lines, loads, maybe, merging, narrow_fields, prepends, presized_objects, probes,
    ranges, references, reuse, scalars, scratch_keys, sharing, shorthands, singletons, swaps, text,
    unpacked, unreferenced, updates, upsert, vector, wrappers,
};
use crate::arity::Arities;
use crate::error::GoResult;
use crate::foreign::{ForeignPackages, GoFunction, LineCoverage};
use crate::maps::KeptOperations;
use crate::modules::{ModuleIndex, Modules};
use crate::monomorphic::{FunctionId, Program};
use crate::monotype::{DataType, MonotypeId, Monotypes};
use crate::syntax::{DeclarationNames, GoDeclaration, GoPackage};

pub struct EmissionInputs<'a, Q> {
    pub monotypes: &'a mut Monotypes,
    pub eliminators: &'a Eliminators,
    pub queries: &'a Q,
    pub foreign_packages: &'a ForeignPackages,
    pub modules: &'a Modules,
    pub module_path: &'a str,
    pub kept: &'a KeptOperations,
}

pub fn emit_program<Q>(
    program: Program,
    mut inputs: EmissionInputs<'_, Q>,
) -> GoResult<(Vec<GoSourceFile>, Vec<String>)>
where
    Q: checking::ExternalQueries,
{
    let lowered = inputs.lower(program)?;
    let (reused, copied_by_containers) = inputs.reuse_cells(&lowered)?;
    let program = &reused.program;
    let mut emitter = Emitter::new(
        program,
        inputs.monotypes,
        inputs.queries,
        inputs.foreign_packages,
        lowered.arities,
    );
    emitter.copied_by_containers = copied_by_containers;
    emitter.materialized = reused.materialized;
    emitter.candidates = reused.candidates;
    emitter.closure_sets = lowered.closure_sets;
    emitter.prepare()?;
    let mut declarations = emitter.declarations()?;
    let mut lines_aside = emitter.await_fibers_and_set_lines_aside(&mut declarations);
    emitter.simplify_statements(&mut declarations);
    emitter.keep_cells_in_locals(&mut declarations);
    let effects = std::mem::take(&mut emitter.effects);
    let pure_helpers = headers::keeping_helpers(&mut emitter.type_declarations, &effects);
    prove_bounds(&mut declarations, &effects, &pure_helpers);
    emitter.hoist_and_allocate(&mut declarations, &mut lines_aside);
    emitter.finish_statements(&mut declarations)?;
    if let Some(aside) = lines_aside {
        lines::restore(&mut declarations, aside);
    }
    let (declarations, mut homes) = emitter.deduplicate(declarations, inputs.modules);
    let all = emitter.complete_declarations(declarations, &effects, &pure_helpers)?;
    let all = emitter.place_in_modules(all, &mut homes, inputs.modules)?;
    let mut files = emitter.split_into_packages(all, inputs.modules, inputs.module_path)?;
    vector::attach_kernels(&mut files, &emitter.vector_kernels);
    if std::env::var_os("IRIS_GO_ANY_CENSUS").is_some() {
        report_any_census(&files);
    }
    Ok((files, emitter.notes))
}

struct Lowered {
    program: Program,
    arities: Arities,
    closure_sets: FxHashMap<MonotypeId, ClosureSet>,
}

impl<Q> EmissionInputs<'_, Q>
where
    Q: checking::ExternalQueries,
{
    fn lower(&mut self, mut program: Program) -> GoResult<Lowered> {
        let operations = self.kept.find(&program, self.modules);
        hash_maps::choose_hash_maps(&mut program, self.monotypes, &operations);
        prepends::append_prepending_folds(&mut program, self.monotypes);
        let arities = crate::arity::choose(&program, self.monotypes);
        let closure_sets = closures::defunctionalize(
            &mut program,
            self.monotypes,
            self.queries,
            &arities,
            self.eliminators,
        )?;
        Ok(Lowered { program, arities, closure_sets })
    }

    fn reuse_cells(&mut self, lowered: &Lowered) -> GoResult<(Reused, FxHashSet<DataType>)> {
        let program = &lowered.program;
        let arities = lowered.arities.clone();
        let mut probe =
            Emitter::new(program, self.monotypes, self.queries, self.foreign_packages, arities);
        probe.copied_by_containers = probe.data_copied_by_containers()?;
        let reused = reuse::reuse_cells(program, &mut probe);
        Ok((reused, probe.copied_by_containers))
    }
}

impl<Q> Emitter<'_, '_, '_, Q>
where
    Q: checking::ExternalQueries,
{
    fn prepare(&mut self) -> GoResult<()> {
        self.typed_slots = self.find_typed_slots(self.program)?;
        self.vector_kernels = vector::Kernels::new(self.program);
        self.assign_function_names();
        let groups = groups::tail_call_groups(self.program, self.monotypes, &self.lazy_constants);
        self.name_tail_groups(groups);
        Ok(())
    }

    fn declarations(&mut self) -> GoResult<Vec<GoDeclaration>> {
        let program = self.program;
        let entry_origin = program.function(program.entry).origin;
        let mut declarations = vec![];
        for index in 0..program.functions.len() {
            let id = FunctionId(index as u32);
            let emitted = self.function(id)?;
            self.note_homes(&emitted, program.function(id).origin);
            declarations.extend(emitted);
        }
        self.pending_variants(&mut declarations)?;
        let main = self.main()?;
        self.note_homes(main.as_slice(), entry_origin);
        declarations.extend(main);
        self.pending_variants(&mut declarations)?;
        self.delegate_to_writers(&mut declarations);
        // First, so that a top-level value that reads one finds it registered.
        let registrations = self.foreign_data_registrations()?;
        declarations.splice(0..0, registrations);
        let unused = self.unused_tail_group_entries();
        if !unused.is_empty() {
            declarations
                .retain(|declaration| declaration.name().is_none_or(|name| !unused.contains(name)));
        }
        Ok(declarations)
    }

    fn await_fibers_and_set_lines_aside(
        &mut self,
        declarations: &mut [GoDeclaration],
    ) -> Option<SetAside> {
        let every_line = self
            .foreign_packages
            .line_directives
            .as_ref()
            .is_some_and(|directives| directives.coverage == LineCoverage::Every);
        if self.imports.contains(GoPackage::Aff.path())
            || self.foreign_packages.imports_event_loop(&self.imports)
        {
            let await_ = GoFunction { package: GoPackage::EventLoop, name: "Await" };
            let await_ = self.performing(await_);
            await_fibers(declarations, await_, every_line);
        }
        every_line.then(|| lines::set_aside(declarations))
    }

    fn simplify_statements(&self, declarations: &mut Vec<GoDeclaration>) {
        wrappers::inline_wrappers(declarations);
        let structs = scalars::structs_of(&self.type_declarations);
        equality::compare_structs_whole(declarations, &structs);
        labelled::unlabel_blocks(declarations);
        known::drop_known_tests(declarations);
        merging::merge_identical_branches(declarations);
        fresh::drop_clips_of_fresh_slices(declarations);
        presized_objects::presize_filled_objects(declarations);
        references::promote_references(declarations);
        composites::take_composites_apart(declarations);
        immediate::reduce_immediate_calls(declarations);
        conditions::assign_conditions(declarations, conditions::Arms::Literal);
        singletons::run_bodies_of_chosen_singletons(declarations);
        aliases::substitute_aliases(declarations);
        updates::update_in_place(declarations);
        scalars::split_struct_locals(declarations, &structs);
        scalars::store_fields_in_place(declarations, &structs);
        aliases::substitute_aliases(declarations);
        inlining::inline_called_cell_loops(declarations, &structs);
        inlining::inline_cell_constructors(declarations);
        cells::forward_constructed_fields(declarations);
        cells::substitute_cell_aliases(declarations);
        aliases::substitute_aliases(declarations);
        references::promote_references(declarations);
    }

    fn keep_cells_in_locals(&self, declarations: &mut [GoDeclaration]) {
        let helpers: FxHashSet<String> = self.support_functions.values().cloned().collect();
        let type_declarations = self.type_declarations.iter();
        let constructors = type_declarations.filter_map(|declaration| match declaration {
            GoDeclaration::Function { name, .. } => Some(name.clone()),
            _ => None,
        });
        let safe_callees: FxHashSet<String> = helpers.iter().cloned().chain(constructors).collect();
        array_parameters::promote_array_parameters(declarations, &safe_callees);
        let never_recovering = self.foreign_packages.packages_that_never_recover();
        cells::keep_parameter_cells_in_locals(
            declarations,
            &helpers,
            &self.effects,
            &never_recovering,
        );
        confined::keep_confined_cells_in_locals(
            declarations,
            self.foreign_packages,
            &helpers,
            &self.effects,
            &never_recovering,
        );
        joins::join_shared_updates(declarations);
        ranges::read_elements_in_place(declarations);
        swaps::swap_crosswise_pokes(declarations);
    }

    fn hoist_and_allocate(
        &mut self,
        declarations: &mut Vec<GoDeclaration>,
        lines_aside: &mut Option<SetAside>,
    ) {
        let global_names = &self.global_names;
        let taken = |name: &str| global_names.contains(name) || IMPORTED_PACKAGES.contains(&name);
        lengths::count_lengths_up_to_comparisons(declarations);
        let names = declarations.iter_mut().map(GoDeclaration::declared_names);
        let mut names: Vec<DeclarationNames> = names.collect();
        if self.imports.contains(GoPackage::Direct.path()) {
            self.imports.insert(GoPackage::Prim.path().into());
        }
        lengths::hoist_loop_invariant_lengths(declarations, &mut names, &taken);
        invariants::hoist_loop_invariants(declarations, &mut names, &taken);
        ascii_heads::read_ascii_heads(declarations, &mut names, &taken);
        let chunked = chunks::allocate_linked_cells_in_chunks(declarations, &mut names, &taken);
        let workers = builders::allocate_built_cells_in_chunks(declarations, &mut names, &taken);
        if chunked || !workers.is_empty() {
            self.imports.insert(GoPackage::Alloc.path().into());
        }
        blocks::allocate_nested_cells_together(declarations, &mut names, &taken);
        self.adopt_workers(workers, lines_aside);
    }

    fn adopt_workers(&mut self, workers: Vec<Worker>, lines_aside: &mut Option<SetAside>) {
        for worker in workers {
            if let Some(aside) = lines_aside {
                aside.share(&worker.builder, &worker.name);
            }
            if let Some(&home) = self.homes.get(&worker.builder) {
                self.homes.insert(worker.name.clone(), home);
            }
            self.global_names.insert(worker.name);
        }
    }

    fn finish_statements(&mut self, declarations: &mut Vec<GoDeclaration>) -> GoResult<()> {
        diverging::end_blocks_at_divergence(declarations);
        loads::reuse_field_reads(declarations);
        branches::simplify_branches(declarations);
        aliases::substitute_aliases(declarations);
        constant_fields::read_constant_fields(declarations);
        merging::join_repeated_tests(declarations);
        unpacked::read_found_answers(declarations);
        conditions::assign_conditions(declarations, conditions::Arms::Valued);
        maybe::compare_chars_whole(declarations, &self.char_nothings());
        branch_tests::test_in_each_branch(declarations);
        let global_names = &self.global_names;
        let global = |name: &str| global_names.contains(name) || IMPORTED_PACKAGES.contains(&name);
        upsert::look_up_and_write_once(declarations, &global);
        probes::probe_once(declarations, &global);
        index_arrays::count_instead_of_listing_indices(declarations);
        scratch_keys::build_looked_up_keys_in_scratch(declarations, &global);
        let mut record_value_name = |type_name: &str| {
            let (&monotype, _) = self.record_names.iter().find(|(_, name)| *name == type_name)?;
            Some(self.value_base(monotype))
        };
        sharing::share_repeated_constructions(declarations, &mut record_value_name);
        let forwarders = forwarders::Forwarders::new(self.foreign_packages);
        forwarders.call_forwarded(declarations);
        unreferenced::drop_calls_of_empty_functions(declarations);
        unreferenced::drop_unreferenced_definitions(declarations);
        constant_fields::drop_calls_of_constant_functions(declarations);
        self.return_failures_apart(declarations)?;
        conditions::test_bounds_unsigned(declarations);
        // Last, so that every pass before reads the constructions' fields in their literals.
        self.call_constructor_functions(declarations)
    }

    fn deduplicate(
        &mut self,
        declarations: Vec<GoDeclaration>,
        modules: &Modules,
    ) -> (Vec<GoDeclaration>, FxHashMap<String, ModuleIndex>) {
        let mut homes: FxHashMap<String, ModuleIndex> = std::mem::take(&mut self.homes)
            .into_iter()
            .filter_map(|(name, file)| Some((name, modules.index(file)?)))
            .collect();
        // The homes of the declarations each declaration stands for.
        let mut merged: FxHashMap<String, Vec<Option<ModuleIndex>>> = FxHashMap::default();
        let mut merge_homes = |from: &str, into: &str| {
            let from_homes = merged.remove(from).unwrap_or_else(|| vec![homes.get(from).copied()]);
            merged
                .entry(into.to_string())
                .or_insert_with(|| vec![homes.get(into).copied()])
                .extend(from_homes);
        };
        let distinct = deduplicate::merge_identical_declarations(declarations, &mut merge_homes);
        for (name, merged_homes) in merged {
            match modules.common_home(&merged_homes) {
                Some(home) => homes.insert(name, home),
                None => homes.remove(&name),
            };
        }
        (distinct, homes)
    }

    fn complete_declarations(
        &mut self,
        mut declarations: Vec<GoDeclaration>,
        effects: &Effects,
        pure_helpers: &FxHashSet<String>,
    ) -> GoResult<Vec<GoDeclaration>> {
        let spans = std::mem::take(&mut self.spans);
        lines::attribute_spans(&mut declarations, spans);
        self.settle_array_boxes()?;
        self.settle_round_trips();
        self.spell_out_generic_alias_arguments();
        let mut all = std::mem::take(&mut self.type_declarations);
        all.extend(declarations);
        text::drop_unreached_functions(&mut all);
        let data_structs: FxHashSet<String> = self
            .data_layouts
            .values()
            .filter(|layout| layout.maybe.is_none())
            .map(|layout| layout.name.clone())
            .collect();
        narrow_fields::narrow_int_fields(&mut all, &data_structs, effects, pure_helpers);
        Ok(all)
    }

    fn place_in_modules(
        &mut self,
        all: Vec<GoDeclaration>,
        homes: &mut FxHashMap<String, ModuleIndex>,
        modules: &Modules,
    ) -> GoResult<Vec<(GoDeclaration, Option<ModuleIndex>)>> {
        let declared = all.iter().flat_map(|declaration| match declaration {
            GoDeclaration::Constants { names, .. } => names.clone(),
            declaration => declaration.name().map(str::to_string).into_iter().collect(),
        });
        let declared: FxHashSet<String> = declared.collect();
        let record_homes = self.spell_pending(modules, &declared)?;
        for (name, file) in record_homes {
            if let Some(home) = modules.index(file) {
                homes.entry(name).or_insert(home);
            }
        }
        let home = |declaration: &GoDeclaration| {
            let name = match declaration {
                GoDeclaration::Constants { names, .. } => names.first().map(String::as_str),
                declaration => declaration.name(),
            };
            name.and_then(|name| homes.get(name)).copied()
        };
        let placed = all.into_iter().map(|declaration| {
            let home = home(&declaration);
            (declaration, home)
        });
        Ok(placed.collect())
    }

    fn split_into_packages(
        &self,
        all: Vec<(GoDeclaration, Option<ModuleIndex>)>,
        modules: &Modules,
        module_path: &str,
    ) -> GoResult<Vec<GoSourceFile>> {
        let typed_records: Vec<Option<String>> = self
            .typed_records
            .iter()
            .map(|monotype| self.record_names.get(monotype).cloned())
            .collect();
        let packaging = Packaging {
            modules,
            module_path,
            spellings: &self.spellings,
            imports: &self.imports,
            typed_records: &typed_records,
        };
        packaging.split(all)
    }
}

fn prove_bounds(
    declarations: &mut [GoDeclaration],
    effects: &Effects,
    pure_helpers: &FxHashSet<String>,
) {
    headers::read_headers_once(declarations, effects, pure_helpers);
    headers::drop_repeated_bounds_tests(declarations, effects, pure_helpers);
    guards::guard_accesses_together(declarations, effects, pure_helpers);
    intervals::prove_bounds(declarations, effects, pure_helpers);
    divisions::reduce_constant_divisions(declarations);
    shorthands::use_shorthands(declarations);
}

fn report_any_census(files: &[GoSourceFile]) {
    let mut census = crate::erasure::Census::default();
    let mut textual = 0;
    for file in files {
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
