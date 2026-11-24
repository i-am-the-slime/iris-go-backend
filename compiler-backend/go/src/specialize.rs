//! Whole-program specialization from an entry point. Every reference is resolved
//! against the checker's recorded instantiations and evidence, so each generated
//! function is closed: no type variables and no dictionaries remain.

use std::collections::{BTreeSet, VecDeque};
use std::sync::Arc;

use checking::TypeId;
use checking::core::Type;
use checking::evidence::{EvidenceBinderId, InstanceCandidateOrigin};
use checking::tree::{self, DeclarationAbstraction, TermDeclarationKind};
use files::FileId;
use indexing::{EquationSourceId, TermItemId};
use rustc_hash::{FxHashMap, FxHashSet};
use smol_str::SmolStr;

use crate::blocker::{Blocker, Blockers};
use crate::context::{Context, ModuleData};
use crate::dictionary::{Dictionary, InstanceDictionary};
use crate::erasure::Erasure;
use crate::error::{GoError, GoResult, UnsupportedState};
use crate::foreign::{Foreign, ForeignPackages, Signature};
use crate::monomorphic::{
    Alternative, Expression, ExpressionKind, Function, FunctionId, Guarded, Literal, Local,
    LocalId, SourcePosition,
};
use crate::monotype::{Monotype, MonotypeId, Monotypes};
use crate::primitives::Signedness;
use crate::scheme::{Read, SchemeKey};
use crate::timing::timed;
use crate::types::{Substituted, Substitution};

mod equations;
mod evidence;
mod existential;
mod expressions;
mod floating;
mod foreign;
mod growth;
mod hash_map;
mod instantiation;
mod int64;
mod json;
mod locals;
mod native;
mod patterns;
mod references;
mod reified;
mod runtime;
mod show;
mod spine;
mod traverse;
mod variant;

use self::evidence::EvidenceScope;

const SPECIALIZATION_LIMIT: usize = 100_000;
const LOCAL_SPECIALIZATION_LIMIT: usize = 64;

struct IgnoringCallee {
    ignored: &'static [usize],
    monotype: MonotypeId,
    offset: usize,
}

impl IgnoringCallee {
    fn of(function: &Expression, offset: usize) -> IgnoringCallee {
        let ignored = match &function.kind {
            ExpressionKind::Lambda { body, .. } => match body.kind {
                ExpressionKind::Foreign { foreign, .. } => foreign.ignored_arguments(),
                _ => &[],
            },
            _ => &[],
        };
        IgnoringCallee { ignored, monotype: function.monotype, offset }
    }

    fn ignores(&self, monotypes: &Monotypes, position: usize) -> Option<MonotypeId> {
        let position = position.checked_sub(self.offset)?;
        if !self.ignored.contains(&position) {
            return None;
        }
        let remaining = monotypes.result_after(self.monotype, position);
        monotypes.function_parts(remaining).map(|(parameter, _)| parameter)
    }
}

fn is_foreign_wrapper(function: &Expression, expected: Foreign) -> bool {
    matches!(&function.kind, ExpressionKind::Lambda { body, .. }
        if matches!(body.kind, ExpressionKind::Foreign { foreign, .. } if *foreign == expected))
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum Definition {
    Value { file_id: FileId, term: TermItemId },
    Member { dictionary: Arc<InstanceDictionary>, member: (FileId, TermItemId) },
}

impl Definition {
    /// The module the definition is written in: an instance member's is the
    /// instance's module.
    fn origin(&self) -> FileId {
        match self {
            Definition::Value { file_id, .. } => *file_id,
            Definition::Member { dictionary, .. } => match dictionary.origin {
                InstanceCandidateOrigin::Instance(file_id, _)
                | InstanceCandidateOrigin::Derive(file_id, _) => file_id,
            },
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct SpecializationKey {
    definition: Definition,
    types: Arc<[TypeId]>,
    dictionaries: Arc<[Dictionary]>,
    /// The signedness of the definition's `Data.Int64.Internal` Longs.
    signedness: Option<Signedness>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum LocalSource {
    Binder(lowering::BinderId),
    Checked(tree::BinderId),
    Let(lowering::LetBindingNameGroupId),
    RecordPun(lowering::RecordPunId),
}

struct Scope {
    module: Arc<ModuleData>,
    substitution: Substitution,
    givens: FxHashMap<EvidenceBinderId, Dictionary>,
    locals: FxHashMap<LocalSource, Local>,
    polymorphic_locals: FxHashMap<lowering::LetBindingNameGroupId, PolymorphicLocal>,
    local_aliases: FxHashMap<lowering::LetBindingNameGroupId, tree::ExpressionId>,
    scheme_locals: FxHashMap<LocalSource, TypeId>,
    /// The expression being specialized at one instantiation of its rank-N type.
    rank_n_body: Option<tree::ExpressionId>,
    definition: String,
    /// What every bare `Data.Int64.Internal` Long in this definition is.
    signedness: Option<Signedness>,
}

/// A reference to a top-level value, and the expression that makes it.
#[derive(Clone, Copy)]
struct Reference {
    file_id: FileId,
    term: TermItemId,
    expression: tree::ExpressionId,
}

struct PolymorphicLocal {
    name: SmolStr,
    declaration: tree::LocalDeclarationId,
    specializations: Vec<LocalSpecialization>,
    active: Option<usize>,
}

struct LocalSpecialization {
    types: Arc<[TypeId]>,
    dictionaries: Arc<[Dictionary]>,
    local: Local,
    value: Option<Expression>,
    requester: Option<usize>,
}

enum LocalForm {
    Monomorphic,
    Polymorphic,
    Alias(tree::ExpressionId),
}

impl Scope {
    fn new(
        module: &Arc<ModuleData>,
        substitution: Substitution,
        givens: FxHashMap<EvidenceBinderId, Dictionary>,
        definition: String,
    ) -> Scope {
        Scope {
            module: Arc::clone(module),
            substitution,
            givens,
            locals: FxHashMap::default(),
            polymorphic_locals: FxHashMap::default(),
            local_aliases: FxHashMap::default(),
            scheme_locals: FxHashMap::default(),
            rank_n_body: None,
            definition,
            signedness: None,
        }
    }

    fn evidence(&self) -> EvidenceScope<'_> {
        EvidenceScope {
            module: &self.module,
            substitution: &self.substitution,
            givens: &self.givens,
            definition: &self.definition,
        }
    }
}

pub struct Specializer<'q, Q> {
    context: Context<'q, Q>,
    pub monotypes: Monotypes,
    functions: Vec<Option<Function>>,
    keys: FxHashMap<SpecializationKey, FunctionId>,
    function_keys: Vec<SpecializationKey>,
    parents: Vec<Option<FunctionId>>,
    current: Option<FunctionId>,
    queue: VecDeque<(FunctionId, SpecializationKey, SmolStr)>,
    next_local: u32,
    foreign_packages: &'q ForeignPackages,
    blockers: Vec<RecordedBlocker>,
    blocker_positions: FxHashMap<(String, UnsupportedState), usize>,
    /// What each function read of the schemes while it was specialized.
    function_reads: Vec<Vec<Read>>,
    /// Whether this round grew the schemes: it met a new instantiation of a
    /// scheme, a new rank-N field type, or an owner whose rank-N fields stay
    /// erased.
    grown: bool,
    /// Functions left with a placeholder for what this round still had to
    /// discover, to specialize again whether or not they read what grew.
    pending_functions: BTreeSet<FunctionId>,
    /// The functions that built a value of each scheme from its instantiations.
    constructions: FxHashMap<SchemeKey, Vec<FunctionId>>,
    /// Functions that built a value of a scheme before the scheme grew.
    stale: BTreeSet<FunctionId>,
    callback_arities: FxHashMap<(FileId, TermItemId), (&'static [usize], &'static Signature)>,
    constructing: Vec<(SchemeKey, Arc<[TypeId]>)>,
    growing_owners: Vec<String>,
    erased_families: Vec<(TypeId, Erasure)>,
    crossings: rustc_hash::FxHashSet<(MonotypeId, MonotypeId)>,
    variant_crossings: Vec<(TypeId, TypeId)>,
    narrowed_variant_rows: Vec<TypeId>,
    int64: int64::Int64Types,
    /// The parameters of the lambdas the source writes as thunks, `\_ -> later`.
    thunk_parameters: FxHashSet<LocalId>,
    /// Evidence an application passes to its result where a polymorphic
    /// function (`$`, `<<<`, `const`) was instantiated at a constrained type,
    /// `Monad Effect => Policy Effect`: each closed constraint with the
    /// dictionary the references inside its arguments are specialized with.
    floating: Vec<(TypeId, Dictionary)>,
}

struct RecordedBlocker {
    definition: String,
    state: UnsupportedState,
    requester: Option<FunctionId>,
    occurrences: usize,
}

impl<'q, Q> Specializer<'q, Q>
where
    Q: checking::ExternalQueries,
{
    pub fn new(
        queries: &'q Q,
        foreign_packages: &'q ForeignPackages,
        substituted: Substituted,
    ) -> Specializer<'q, Q> {
        let mut monotypes = Monotypes::default();
        monotypes.foreign_modules = foreign_packages.provided();
        monotypes.foreign_sources = foreign_packages.sources.clone();
        Specializer {
            context: Context::sharing(queries, substituted),
            monotypes,
            functions: vec![],
            keys: FxHashMap::default(),
            function_keys: vec![],
            parents: vec![],
            current: None,
            queue: VecDeque::new(),
            next_local: 0,
            foreign_packages,
            blockers: vec![],
            blocker_positions: FxHashMap::default(),
            function_reads: vec![],
            grown: false,
            pending_functions: BTreeSet::new(),
            constructions: FxHashMap::default(),
            stale: BTreeSet::new(),
            callback_arities: FxHashMap::default(),
            constructing: vec![],
            growing_owners: vec![],
            erased_families: vec![],
            crossings: rustc_hash::FxHashSet::default(),
            variant_crossings: vec![],
            narrowed_variant_rows: vec![],
            int64: int64::Int64Types::default(),
            thunk_parameters: FxHashSet::default(),
            floating: vec![],
        }
    }

    pub fn context(&mut self) -> &mut Context<'q, Q> {
        &mut self.context
    }

    pub fn specialize_entry(&mut self, file_id: FileId, term: TermItemId) -> GoResult<FunctionId> {
        let name = self.context.term_name(file_id, term)?;
        let key = SpecializationKey {
            definition: Definition::Value { file_id, term },
            types: Arc::from([]),
            dictionaries: Arc::from([]),
            signedness: None,
        };
        let entry = self.request(key, name)?;
        let mut round = 0;
        loop {
            self.grown = false;
            let version = self.monotypes.schemes.version();
            let specialized = timed(&format!("round {round}"), || {
                self.specialize_requested()?;
                self.note_reference_crossings();
                self.adopt_rank_n_fields();
                Ok::<_, GoError>(())
            });
            specialized?;
            if self.monotypes.schemes.version() == version {
                break;
            }
            let mut stale = self.stale_functions();
            stale.append(&mut self.pending_functions);
            if stale.is_empty() {
                break;
            }
            self.monotypes.forget_stale_conversions();
            self.stale.extend(stale);
            round += 1;
        }
        Ok(entry)
    }

    /// Specializes every requested function, and the stale ones after them,
    /// recording what each read of the schemes.
    fn specialize_requested(&mut self) -> GoResult<()> {
        while let Some((id, key, name)) = self.next_specialization() {
            self.current = Some(id);
            self.monotypes.schemes.take_reads();
            let specialized = self.specialize(&key, name.clone()).and_then(|mut function| {
                self.match_field_representations(&mut function.body)?;
                Ok(function)
            });
            let function = match specialized {
                Ok(function) => function,
                Err(error) => {
                    self.record(error)?;
                    let erased = self.monotypes.intern(Monotype::Erased(Erasure::FailedDefinition));
                    let body = Expression::new(ExpressionKind::Fail(name.clone()), erased);
                    Function {
                        name,
                        origin: Some(key.definition.origin()),
                        parameters: vec![],
                        result: erased,
                        body,
                        position: None,
                    }
                }
            };
            self.functions[id.0 as usize] = Some(function);
            self.adopt_rank_n_fields();
            self.function_reads[id.0 as usize] = self.monotypes.schemes.take_reads();
        }
        Ok(())
    }

    pub(super) fn note_pending(&mut self) {
        if let Some(current) = self.current {
            self.pending_functions.insert(current);
        }
    }

    /// The functions that read a decision of the schemes before growth
    /// changed it, which must be specialized again under the schemes as they
    /// are now.
    fn stale_functions(&self) -> BTreeSet<FunctionId> {
        let mut staleness = FxHashMap::default();
        let mut stale = BTreeSet::new();
        for (index, reads) in self.function_reads.iter().enumerate() {
            if reads.iter().any(|read| self.monotypes.is_stale(read, &mut staleness)) {
                stale.insert(FunctionId(index as u32));
            }
        }
        stale
    }

    /// The next requested function, or else a stale one. A pass that grew the
    /// schemes is repeated from scratch, but first the functions that built a
    /// scheme's value without its newer instantiations are specialized again,
    /// so that instantiations met only inside those are discovered in this pass
    /// rather than in one more pass per link of the chain.
    fn next_specialization(&mut self) -> Option<(FunctionId, SpecializationKey, SmolStr)> {
        if let Some(requested) = self.queue.pop_front() {
            return Some(requested);
        }
        let stale = self.stale.pop_first()?;
        let key = self.function_keys[stale.0 as usize].clone();
        let function = self.functions[stale.0 as usize].as_ref();
        let function = function.expect("invariant violated: a stale function was specialized");
        Some((stale, key, function.name.clone()))
    }

    fn note_construction(&mut self, key: &SchemeKey) {
        let Some(current) = self.current else { return };
        let functions = self.constructions.entry(key.clone()).or_default();
        if functions.last() != Some(&current) {
            functions.push(current);
        }
    }

    /// Rank-N field types met while specializing a function are specialized for
    /// the rest of the pass, as discovered instantiations are.
    fn adopt_rank_n_fields(&mut self) {
        let erased = std::mem::take(&mut self.monotypes.new_erased_owners);
        let erased_keys = std::mem::take(&mut self.monotypes.new_erased_keys);
        let keys = std::mem::take(&mut self.monotypes.new_rank_n_keys);
        let growing = std::mem::take(&mut self.growing_owners);
        let families = std::mem::take(&mut self.erased_families);
        let narrowed = self.narrowed_variant_rows_to_erase();
        if erased.is_empty()
            && erased_keys.is_empty()
            && keys.is_empty()
            && growing.is_empty()
            && families.is_empty()
            && narrowed.is_empty()
        {
            return;
        }
        for row in narrowed {
            self.context.erased_variant_rows.insert(row);
            self.monotypes.schemes.erase_variant(row);
        }
        for (family, erasure) in families {
            self.monotypes.schemes.erase_family(family, erasure);
        }
        for owner in erased {
            self.monotypes.schemes.erase_owner(owner);
        }
        for owner in growing {
            self.monotypes.schemes.erase_growing_owner(owner);
        }
        for (key, owner) in keys {
            self.monotypes.schemes.add_rank_n(key, owner);
        }
        for key in erased_keys {
            self.monotypes.schemes.erase_key(key);
        }
        self.grown = true;
    }

    pub fn blockers(&mut self) -> GoResult<Option<Blockers>> {
        if self.blockers.is_empty() {
            return Ok(None);
        }
        Ok(Some(self.report()?))
    }

    fn record(&mut self, error: GoError) -> GoResult<()> {
        let GoError::Unsupported { definition, state } = error else {
            return Err(error);
        };
        let key = (definition, state);
        if let Some(&position) = self.blocker_positions.get(&key) {
            self.blockers[position].occurrences += 1;
            return Ok(());
        }
        let (definition, state) = key.clone();
        self.blocker_positions.insert(key, self.blockers.len());
        let requester = self.current;
        self.blockers.push(RecordedBlocker { definition, state, requester, occurrences: 1 });
        Ok(())
    }

    fn recover(
        &mut self,
        result: GoResult<Expression>,
        monotype: MonotypeId,
    ) -> GoResult<Expression> {
        match result {
            Ok(expression) => Ok(expression),
            Err(error) => {
                self.record(error)?;
                let blocked = SmolStr::new_static("blocked");
                Ok(Expression::new(ExpressionKind::Fail(blocked), monotype))
            }
        }
    }

    fn report(&mut self) -> GoResult<Blockers> {
        let recorded = std::mem::take(&mut self.blockers);
        let mut blockers = Vec::with_capacity(recorded.len());
        for blocker in recorded {
            let mut requesters: Vec<String> = vec![];
            let mut ancestor = blocker.requester;
            while let Some(id) = ancestor {
                let description = self.describe(id)?;
                let repeated = requesters.last() == Some(&description)
                    || (requesters.is_empty() && description == blocker.definition);
                if !repeated {
                    requesters.push(description);
                }
                ancestor = self.parents[id.0 as usize];
            }
            blockers.push(Blocker {
                definition: blocker.definition,
                state: blocker.state,
                requesters,
                occurrences: blocker.occurrences,
            });
        }
        Ok(Blockers { blockers })
    }

    fn describe(&mut self, id: FunctionId) -> GoResult<String> {
        let definition = self.function_keys[id.0 as usize].definition.clone();
        self.describe_definition(definition)
    }

    fn describe_definition(&mut self, definition: Definition) -> GoResult<String> {
        match definition {
            Definition::Value { file_id, term } => {
                Ok(self.context.qualified_term_name(file_id, term)?)
            }
            Definition::Member { dictionary, member } => {
                let member = self.context.qualified_term_name(member.0, member.1)?;
                Ok(format!("{member} of {}", self.instance_name(dictionary.origin)?))
            }
        }
    }

    pub fn finish(mut self) -> (Vec<Function>, Monotypes, u32, FxHashSet<LocalId>) {
        let functions = std::mem::take(&mut self.functions).into_iter().map(|function| {
            function.expect("invariant violated: requested specialization was never produced")
        });
        let mut functions: Vec<Function> = functions.collect();
        let signatures: Vec<MonotypeId> =
            functions.iter().map(|function| self.signature(function)).collect();
        for function in &mut functions {
            self.reconcile_references(&mut function.body, &signatures);
        }
        (functions, self.monotypes, self.next_local, self.thunk_parameters)
    }

    fn note_reference_crossings(&mut self) {
        let functions = std::mem::take(&mut self.functions);
        let signatures: Vec<Option<MonotypeId>> = functions
            .iter()
            .map(|function| function.as_ref().map(|function| self.signature(function)))
            .collect();
        let mut mismatches = vec![];
        for function in functions.iter().flatten() {
            mismatched_references(&function.body, &signatures, &mut mismatches);
        }
        self.functions = functions;
        for (signature, expected) in mismatches {
            if self.changes_representation(signature, expected) {
                self.note_crossings(signature, expected);
            }
        }
    }

    fn signature(&mut self, function: &Function) -> MonotypeId {
        let mut monotype = function.result;
        for parameter in function.parameters.iter().rev() {
            monotype = self.monotypes.function(parameter.monotype, monotype);
        }
        monotype
    }

    fn reconcile_references(&mut self, expression: &mut Expression, signatures: &[MonotypeId]) {
        if let ExpressionKind::Function(id) = expression.kind {
            let signature = signatures[id.0 as usize];
            if signature != expression.monotype {
                let expected = expression.monotype;
                let reference = Expression::new(ExpressionKind::Function(id), signature);
                *expression = self.coerce(reference, expected);
            }
            return;
        }
        crate::monomorphic::traversal::for_each_child_mut(expression, &mut |child| {
            self.reconcile_references(child, signatures)
        });
    }

    fn request(&mut self, key: SpecializationKey, name: SmolStr) -> GoResult<FunctionId> {
        let definition = key.definition.clone();
        let (key, promotions) = self.terminate_growth(key)?;
        if !promotions.is_empty() {
            return Err(GoError::Unsupported {
                definition: self.describe_definition(definition)?,
                state: UnsupportedState::GrowingEvidence,
            });
        }
        self.enqueue(key, name)
    }

    fn enqueue(&mut self, key: SpecializationKey, name: SmolStr) -> GoResult<FunctionId> {
        let canonical = self.without_causes(&key);
        if let Some(&id) = self.keys.get(&canonical) {
            return Ok(id);
        }
        if self.functions.len() >= SPECIALIZATION_LIMIT {
            return Err(GoError::Unsupported {
                definition: self.describe_definition(key.definition)?,
                state: UnsupportedState::SpecializationLimit { limit: SPECIALIZATION_LIMIT },
            });
        }
        let id = FunctionId(self.functions.len() as u32);
        self.functions.push(None);
        self.function_reads.push(vec![]);
        self.function_keys.push(key.clone());
        self.parents.push(self.current);
        self.keys.insert(canonical, id);
        self.queue.push_back((id, key, name));
        Ok(id)
    }

    fn without_causes(&self, key: &SpecializationKey) -> SpecializationKey {
        let types = self.types_without_causes(&key.types);
        SpecializationKey {
            definition: key.definition.clone(),
            types,
            dictionaries: Arc::clone(&key.dictionaries),
            signedness: key.signedness,
        }
    }

    fn types_without_causes(&self, types: &Arc<[TypeId]>) -> Arc<[TypeId]> {
        let collapsed: Vec<TypeId> =
            types.iter().map(|&type_id| self.context.types.without_causes(type_id)).collect();
        if collapsed[..] == types[..] { Arc::clone(types) } else { Arc::from(collapsed) }
    }

    fn fresh_local(&mut self, name: SmolStr, monotype: MonotypeId) -> Local {
        Local::fresh(&mut self.next_local, name, monotype)
    }

    fn specialize(&mut self, key: &SpecializationKey, name: SmolStr) -> GoResult<Function> {
        let described = self.describe_definition(key.definition.clone())?;
        let (key, dictionary_parameters) = self.bind_runtime_dictionaries(key, &described)?;
        let key = &key;
        let (mut scope, value) = match &key.definition {
            Definition::Value { file_id, term } => {
                let module = self.context.module(*file_id)?;
                let definition = self.context.qualified_term_name(*file_id, *term)?;
                let unsupported =
                    |state| GoError::Unsupported { definition: definition.clone(), state };
                let declaration = module
                    .checked
                    .tree
                    .lookup_term(*term)
                    .ok_or_else(|| unsupported(UnsupportedState::MissingDeclaration))?;
                let TermDeclarationKind::Value(value) = &module.checked.tree[declaration].kind
                else {
                    return Err(unsupported(UnsupportedState::MissingDeclaration));
                };
                let value = (Arc::clone(&value.abstractions), Arc::clone(&value.equations));
                let scope =
                    Scope::new(&module, Substitution::default(), FxHashMap::default(), definition);
                (scope, value)
            }
            Definition::Member { dictionary, member } => {
                let (module, declaration) = self.instance_declaration(dictionary.origin)?;
                let member_name = self.context.qualified_term_name(member.0, member.1)?;
                let definition =
                    format!("{member_name} of {}", self.instance_name(dictionary.origin)?);
                let unsupported =
                    |state| GoError::Unsupported { definition: definition.clone(), state };
                let TermDeclarationKind::Instance(instance) =
                    &module.checked.tree[declaration].kind
                else {
                    return Err(unsupported(UnsupportedState::MissingDeclaration));
                };
                let tree::InstanceImplementation::Members(members) = &instance.implementation
                else {
                    return Err(unsupported(UnsupportedState::MissingDeclaration));
                };
                let Some(implementation) =
                    members.iter().find(|implementation| implementation.resolution == *member)
                else {
                    return Err(unsupported(UnsupportedState::MissingInstanceMember {
                        member: member_name.clone(),
                    }));
                };
                let value = (
                    Arc::clone(&implementation.abstractions),
                    Arc::clone(&implementation.equations),
                );
                let (substitution, givens) =
                    self.instance_environment(&module, declaration, dictionary)?;
                let scope = Scope::new(&module, substitution, givens, definition);
                (scope, value)
            }
        };
        let (abstractions, equations) = value;
        scope.signedness = key.signedness;
        self.bind_abstractions(&mut scope, &abstractions, &key.types, &key.dictionaries)?;
        let position =
            equations.first().and_then(|first| definition_position(&scope.module, first.source));
        let mut body = self.equations(&mut scope, &equations)?;
        if self.reads_json_directly(key)? {
            body = self.json_read(body);
        }
        if !dictionary_parameters.is_empty() {
            body = self.lambda(dictionary_parameters, body);
        }
        Ok(self.function(name, Some(key.definition.origin()), body, position))
    }

    fn function(
        &mut self,
        name: SmolStr,
        origin: Option<FileId>,
        body: Expression,
        position: Option<SourcePosition>,
    ) -> Function {
        let mut parameters = vec![];
        let mut body = body;
        while let ExpressionKind::Lambda { .. } = body.kind {
            let ExpressionKind::Lambda { parameters: lambda_parameters, body: lambda_body } =
                body.kind
            else {
                unreachable!()
            };
            parameters.extend(lambda_parameters);
            body = *lambda_body;
        }
        let result = body.monotype;
        Function { name, origin, parameters, result, body, position }
    }

    fn bind_abstractions(
        &mut self,
        scope: &mut Scope,
        abstractions: &[DeclarationAbstraction],
        types: &[TypeId],
        dictionaries: &[Dictionary],
    ) -> GoResult<()> {
        let mut types = types.iter();
        let mut dictionaries = dictionaries.iter();
        for abstraction in abstractions {
            match abstraction {
                DeclarationAbstraction::Type { binder, rigid } => {
                    let Some(&argument) = types.next() else {
                        return Err(self.unsupported(scope, UnsupportedState::MissingDeclaration));
                    };
                    let binder = self.context.queries.lookup_forall_binder(*binder);
                    scope.substitution.insert(binder.name, argument);
                    if let Type::Rigid(name, _, _) = self.context.types.lookup(*rigid) {
                        scope.substitution.insert(*name, argument);
                    }
                }
                DeclarationAbstraction::Evidence { binder, .. } => {
                    let Some(dictionary) = dictionaries.next() else {
                        return Err(self.unsupported(scope, UnsupportedState::UnboundEvidence));
                    };
                    scope.givens.insert(*binder, dictionary.clone());
                }
                DeclarationAbstraction::Argument => {}
            }
        }
        if dictionaries.next().is_some() {
            return Err(self.unsupported(scope, UnsupportedState::UnabstractedEvidence));
        }
        Ok(())
    }

    fn unsupported(&self, scope: &Scope, state: UnsupportedState) -> GoError {
        GoError::Unsupported { definition: scope.definition.clone(), state }
    }

    fn monotype(&mut self, scope: &Scope, type_id: TypeId) -> GoResult<MonotypeId> {
        // Inside one instantiation of a rank-N expression, or in the body of a
        // definition whose result is quantified (`hoistFree k = ...` has type
        // `Free f ~> Free g`), the quantifiers are already substituted; the
        // expression has the instantiated type.
        let (head, _) = self.context.types.spine(type_id);
        let mut instantiated = match self.context.types.lookup(head) {
            Type::Synonym(..) => crate::monotype::expand_synonyms(&mut self.context, type_id)?,
            _ => type_id,
        };
        while let Type::Forall(binder, inner) =
            self.context.types.lookup(self.context.types.strip_annotations(instantiated)).clone()
        {
            let binder = self.context.queries.lookup_forall_binder(binder);
            if !scope.substitution.contains_key(&binder.name) {
                break;
            }
            instantiated = inner;
        }
        let closed = self.context.types.substitute(instantiated, &scope.substitution);
        self.closed_monotype(scope, closed)
    }

    /// A binder's quantifiers are never instantiated where it binds: a parameter
    /// of type `f ~> m` is a rank-N value, even when an enclosing instantiation
    /// gave a quantifier of the same synonym a type.
    fn binder_monotype(&mut self, scope: &Scope, type_id: TypeId) -> GoResult<MonotypeId> {
        let closed = self.context.types.substitute(type_id, &scope.substitution);
        self.closed_monotype(scope, closed)
    }

    /// Notes where the `unsafeCoerce` from `from` to `to` is written, the first time it is met.
    fn note_coercion_site(
        &mut self,
        scope: &Scope,
        expression: tree::ExpressionId,
        from: MonotypeId,
        to: MonotypeId,
    ) -> GoResult<()> {
        if self.monotypes.coercion_sites.contains_key(&(from, to)) {
            return Ok(());
        }
        let Some(file_id) = self.context.queries.module_file(&scope.module.name) else {
            return Ok(());
        };
        let offset = match scope.module.checked.tree[expression].source {
            Some(tree::ExpressionSource::Expression(source)) => {
                let stabilized = self.context.queries.stabilized(file_id)?;
                stabilized
                    .ast_ptr(source)
                    .map(|pointer| u32::from(pointer.syntax_node_ptr().text_range().start()))
            }
            _ => None,
        };
        let definition = scope.definition.clone();
        let site = crate::monotype::CoercionSite { definition, file_id, offset };
        self.monotypes.coercion_sites.insert((from, to), site);
        Ok(())
    }

    fn closed_monotype(&mut self, scope: &Scope, closed: TypeId) -> GoResult<MonotypeId> {
        let closed = match scope.signedness {
            Some(signedness) => self.spelled_longs(closed, signedness)?,
            None => closed,
        };
        let monotype = self.monotypes.monotype(&mut self.context, closed);
        monotype.map_err(|failure| failure.at(&scope.definition))
    }
}

fn mismatched_references(
    expression: &Expression,
    signatures: &[Option<MonotypeId>],
    mismatches: &mut Vec<(MonotypeId, MonotypeId)>,
) {
    if let ExpressionKind::Function(id) = expression.kind {
        if let Some(signature) = signatures[id.0 as usize]
            && signature != expression.monotype
        {
            mismatches.push((signature, expression.monotype));
        }
        return;
    }
    crate::monomorphic::traversal::for_each_child(expression, &mut |child| {
        mismatched_references(child, signatures, mismatches)
    });
}

fn alternatives_monotype(alternatives: &[Alternative]) -> MonotypeId {
    match &alternatives[0].body {
        Guarded::Unconditional(body) => body.monotype,
        Guarded::Guards(branches) => branches[0].body.monotype,
    }
}

/// The text of a type-level string. Dictionaries carry symbols as Rust strings, so a lone
/// surrogate in one reads as U+FFFD.
fn symbol_text(value: &lowering::StringLiteral) -> String {
    String::from_utf16_lossy(value.as_utf16())
}

/// A string literal: a `Literal::String` unless it holds a lone surrogate.
fn string_literal(value: &lowering::StringLiteral) -> Literal {
    match value.to_utf8() {
        Ok(text) => Literal::String(text),
        Err(_) => Literal::Utf16(Arc::from(value.as_utf16())),
    }
}

/// Whether the checked lambda is one the source writes with a backslash, rather than one that
/// desugaring a do block or a section makes.
fn is_written_lambda(module: &ModuleData, lambda: &tree::Expression) -> bool {
    let Some(tree::ExpressionSource::Expression(source)) = lambda.source else { return false };
    matches!(
        module.lowered.tree.get_expression_kind(source),
        Some(lowering::ExpressionKind::Lambda { .. })
    )
}

/// Where the checked expression is written: the start of its syntax, which is the whitespace in
/// front of it.
fn source_position(module: &ModuleData, id: tree::ExpressionId) -> Option<SourcePosition> {
    let pointer = match module.checked.tree[id].source? {
        tree::ExpressionSource::Expression(source) => module.stabilized.syntax_ptr(source),
        tree::ExpressionSource::DoStatement(source) => module.stabilized.syntax_ptr(source),
    }?;
    let offset = u32::from(pointer.text_range().start());
    Some(SourcePosition { file: module.file_id, offset })
}

fn case_branch_position(
    module: &ModuleData,
    source: Option<lowering::CaseBranchId>,
) -> Option<SourcePosition> {
    let pointer = module.stabilized.syntax_ptr(source?)?;
    let offset = u32::from(pointer.text_range().start());
    Some(SourcePosition { file: module.file_id, offset })
}

fn definition_position(
    module: &ModuleData,
    source: tree::EquationSource,
) -> Option<SourcePosition> {
    let tree::EquationSource::Generated { derive, .. } = source else {
        return equation_position(module, source);
    };
    let pointer = module.stabilized.syntax_ptr(derive)?;
    let offset = u32::from(pointer.text_range().start());
    Some(SourcePosition { file: module.file_id, offset })
}

fn equation_position(module: &ModuleData, source: tree::EquationSource) -> Option<SourcePosition> {
    let pointer = match source {
        tree::EquationSource::Item(EquationSourceId::Value(id)) => module.stabilized.syntax_ptr(id),
        tree::EquationSource::Item(EquationSourceId::Instance(id)) => {
            module.stabilized.syntax_ptr(id)
        }
        tree::EquationSource::Local(id) => module.stabilized.syntax_ptr(id),
        tree::EquationSource::Generated { .. } => None,
    }?;
    let offset = u32::from(pointer.text_range().start());
    Some(SourcePosition { file: module.file_id, offset })
}
