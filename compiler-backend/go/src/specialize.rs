//! Whole-program specialization from an entry point. Every reference is resolved
//! against the checker's recorded instantiations and evidence, so each generated
//! function is closed: no type variables and no dictionaries remain.

use std::collections::{BTreeSet, VecDeque};
use std::sync::Arc;

use checking::TypeId;
use checking::core::{Name, Type};
use checking::evidence::{
    EvidenceBinderId, InstanceCandidateOrigin,
};
use checking::tree::{self, DeclarationAbstraction, TermDeclarationKind};
use files::FileId;
use indexing::{IndexedTermItemKind, TermItemId};
use rustc_hash::FxHashMap;
use smol_str::{SmolStr, format_smolstr};

use crate::blocker::{Blocker, Blockers};
use crate::context::{Context, ModuleData};
use crate::dictionary::{Dictionary, InstanceDictionary, Reflected};
use crate::erasure::Erasure;
use crate::error::{GoError, GoResult, UnsupportedState};
use crate::foreign::{self, Accumulator, Boundary, Foreign, ForeignPackages, Signature, Spelled};
use crate::mono::{
    Alternative, Binding, Expression, ExpressionKind, Function, FunctionId, FunctionSpelling,
    Guard, Guarded, GuardedBranch, Literal, Local, Pattern, PatternKind, RecordUpdate,
};
use crate::monotype::{Monotype, MonotypeId, Monotypes, supported};
use crate::scheme::{
    Read, SCHEME_INSTANTIATION_LIMIT, SchemeInstantiation, SchemeKey, constrained_scheme,
    rank_n_scheme,
};
use crate::timing::timed;
use crate::types::{Substituted, Substitution};

mod evidence;
mod existential;
mod growth;
mod patterns;
mod reified;
mod runtime;
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
        monotypes.foreign_modules = foreign_packages.modules.clone();
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
        let mut memo = FxHashMap::default();
        let mut stale = BTreeSet::new();
        for (index, reads) in self.function_reads.iter().enumerate() {
            if reads.iter().any(|read| self.monotypes.is_stale(read, &mut memo)) {
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

    pub fn finish(mut self) -> (Vec<Function>, Monotypes, u32) {
        let functions = std::mem::take(&mut self.functions).into_iter().map(|function| {
            function.expect("invariant violated: requested specialization was never produced")
        });
        let mut functions: Vec<Function> = functions.collect();
        let signatures: Vec<MonotypeId> =
            functions.iter().map(|function| self.signature(function)).collect();
        for function in &mut functions {
            self.reconcile_references(&mut function.body, &signatures);
        }
        (functions, self.monotypes, self.next_local)
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
        crate::simplify::for_each_child_mut(expression, &mut |child| {
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
        }
    }

    fn types_without_causes(&self, types: &Arc<[TypeId]>) -> Arc<[TypeId]> {
        let collapsed: Vec<TypeId> =
            types.iter().map(|&type_id| self.context.types.without_causes(type_id)).collect();
        if collapsed[..] == types[..] { Arc::clone(types) } else { Arc::from(collapsed) }
    }

    /// Polymorphic recursion requests a definition at ever larger types. When a
    /// request embeds the types of the same definition further up its chain of
    /// requesters, the growing positions are erased so specialization terminates.
    fn terminate_growth(
        &mut self,
        mut key: SpecializationKey,
    ) -> GoResult<(SpecializationKey, Vec<runtime::Promotion>)> {
        let requested = Arc::clone(&key.types);
        let mut ancestor = self.current;
        let mut types: Vec<TypeId> = key.types.to_vec();
        let mut changed = false;
        let mut evidence_grows = false;
        while let Some(id) = ancestor {
            let ancestor_key = &self.function_keys[id.0 as usize];
            if ancestor_key.definition == key.definition {
                let mut grows = false;
                for (position, ancestor_type) in ancestor_key.types.iter().enumerate() {
                    let Some(requested) = types.get(position).copied() else { continue };
                    if self.context.types.grows(requested, *ancestor_type) {
                        types[position] = self.context.types.erased(Erasure::PolymorphicRecursion);
                        grows = true;
                    }
                }
                evidence_grows |= grows && ancestor_key.dictionaries != key.dictionaries;
                changed |= grows;
            }
            ancestor = self.parents[id.0 as usize];
        }
        if changed {
            key.types = Arc::from(types);
        }
        if !evidence_grows {
            return Ok((key, vec![]));
        }
        let promotions = self.promote_growing_evidence(&mut key, &requested)?;
        Ok((key, promotions))
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
        self.bind_abstractions(&mut scope, &abstractions, &key.types, &key.dictionaries)?;
        let mut body = self.equations(&mut scope, &equations)?;
        if !dictionary_parameters.is_empty() {
            body = self.lambda(dictionary_parameters, body);
        }
        Ok(self.function(name, Some(key.definition.origin()), body))
    }

    fn function(&mut self, name: SmolStr, origin: Option<FileId>, body: Expression) -> Function {
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
        Function { name, origin, parameters, result, body }
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

    fn closed_monotype(&mut self, scope: &Scope, closed: TypeId) -> GoResult<MonotypeId> {
        let monotype = self.monotypes.monotype(&mut self.context, closed);
        monotype.map_err(|failure| failure.at(&scope.definition))
    }

    fn equations(
        &mut self,
        scope: &mut Scope,
        equations: &[tree::Equation],
    ) -> GoResult<Expression> {
        let Some(first) = equations.first() else {
            return Err(self.unsupported(scope, UnsupportedState::MissingEquation));
        };
        let pattern_match = tree::PatternMatch::Equations(first.source);
        let exhaustive = scope.module.checked.tree.is_exhaustive_match(pattern_match);
        let arity = equations.iter().map(|equation| equation.binders.len()).max().unwrap_or(0);
        if arity == 0 {
            return self.guarded_expression(scope, &first.guarded_expression, exhaustive);
        }
        if let [equation] = equations
            && let Some(parameters) = self.variable_parameters(scope, &equation.binders)?
        {
            let body = self.guarded_expression(scope, &equation.guarded_expression, exhaustive)?;
            return Ok(self.lambda(parameters, body));
        }
        let mut parameters = Vec::with_capacity(arity);
        for position in 0..arity {
            let binder = equations
                .iter()
                .find_map(|equation| equation.binders.get(position))
                .copied()
                .expect("invariant violated: arity is the maximum binder count");
            let monotype =
                self.binder_monotype(scope, scope.module.checked.tree[binder].type_id)?;
            let binders = equations.iter().filter_map(|equation| equation.binders.get(position));
            let name = self.parameter_name(scope, binders.copied(), monotype);
            parameters.push(self.fresh_local(name, monotype));
        }
        let mut alternatives = Vec::with_capacity(equations.len());
        for equation in equations {
            let mut patterns = Vec::with_capacity(arity);
            for &binder in equation.binders.iter() {
                patterns.push(self.pattern(scope, binder)?);
            }
            for parameter in &parameters[patterns.len()..] {
                patterns
                    .push(Pattern { kind: PatternKind::Wildcard, monotype: parameter.monotype });
            }
            let body = self.guarded(scope, &equation.guarded_expression)?;
            alternatives.push(Alternative { patterns, body });
        }
        let scrutinees: Vec<Expression> = parameters.iter().map(Local::expression).collect();
        let monotype = alternatives_monotype(&alternatives);
        if !exhaustive {
            alternatives.push(Alternative::match_failure(&scrutinees, monotype));
        }
        let body = Expression::new(ExpressionKind::Case { scrutinees, alternatives }, monotype);
        Ok(self.lambda(parameters, body))
    }

    /// A parameter that patterns take apart is called by the name a variable
    /// or as-pattern gives it in one of them, else after its type.
    fn parameter_name(
        &self,
        scope: &Scope,
        binders: impl IntoIterator<Item = tree::BinderId>,
        monotype: MonotypeId,
    ) -> SmolStr {
        let named = binders.into_iter().find_map(|binder| match self.unwrap_typed(scope, binder) {
            (binder, tree::BinderKind::Variable) => Some(self.binder_name(scope, binder)),
            (_, tree::BinderKind::Named { name, .. }) => Some(name.clone()),
            _ => None,
        });
        named.unwrap_or_else(|| self.monotypes.value_name(monotype))
    }

    fn variable_parameters(
        &mut self,
        scope: &mut Scope,
        binders: &[tree::BinderId],
    ) -> GoResult<Option<Vec<Local>>> {
        let all_variables = binders.iter().all(|&binder| {
            matches!(
                self.unwrap_typed(scope, binder).1,
                tree::BinderKind::Variable | tree::BinderKind::Wildcard
            )
        });
        if !all_variables {
            return Ok(None);
        }
        let mut parameters = Vec::with_capacity(binders.len());
        for &binder in binders {
            let pattern = self.pattern(scope, binder)?;
            let local = match pattern.kind {
                PatternKind::Variable(local) => local,
                PatternKind::Wildcard => {
                    self.fresh_local(SmolStr::new_static("ignored"), pattern.monotype)
                }
                _ => unreachable!(
                    "invariant violated: variable binders convert to variable patterns"
                ),
            };
            parameters.push(local);
        }
        Ok(Some(parameters))
    }

    fn unwrap_typed<'s>(
        &self,
        scope: &'s Scope,
        mut binder: tree::BinderId,
    ) -> (tree::BinderId, &'s tree::BinderKind) {
        loop {
            match &scope.module.checked.tree[binder].kind {
                tree::BinderKind::Typed { binder: inner, .. } => binder = *inner,
                kind => return (binder, kind),
            }
        }
    }

    fn lambda(&mut self, parameters: Vec<Local>, body: Expression) -> Expression {
        let mut monotype = body.monotype;
        for parameter in parameters.iter().rev() {
            monotype = self.monotypes.function(parameter.monotype, monotype);
        }
        Expression::new(ExpressionKind::Lambda { parameters, body: Box::new(body) }, monotype)
    }

    fn guarded(
        &mut self,
        scope: &mut Scope,
        guarded: &tree::GuardedExpression,
    ) -> GoResult<Guarded> {
        if let [alternative] = guarded.alternatives.as_ref()
            && alternative.pattern_guards.is_empty()
        {
            let body = self.where_expression(scope, &alternative.where_expression)?;
            return Ok(Guarded::Unconditional(body));
        }
        let mut branches = Vec::with_capacity(guarded.alternatives.len());
        for alternative in guarded.alternatives.iter() {
            let mut guards = Vec::with_capacity(alternative.pattern_guards.len());
            for guard in alternative.pattern_guards.iter() {
                let guard = match guard {
                    tree::PatternGuard::Boolean { expression } => {
                        Guard::Boolean(self.expression(scope, *expression)?)
                    }
                    tree::PatternGuard::Pattern { binder, expression, .. } => {
                        let value = self.expression(scope, *expression)?;
                        let pattern = self.pattern(scope, *binder)?;
                        Guard::Pattern { pattern, value }
                    }
                };
                guards.push(guard);
            }
            let body = self.where_expression(scope, &alternative.where_expression)?;
            branches.push(GuardedBranch { guards, body });
        }
        Ok(Guarded::Guards(branches))
    }

    fn guarded_expression(
        &mut self,
        scope: &mut Scope,
        guarded: &tree::GuardedExpression,
        exhaustive: bool,
    ) -> GoResult<Expression> {
        match self.guarded(scope, guarded)? {
            Guarded::Unconditional(body) => Ok(body),
            Guarded::Guards(branches) => {
                let monotype = branches[0].body.monotype;
                let alternative = Alternative { patterns: vec![], body: Guarded::Guards(branches) };
                let mut alternatives = vec![alternative];
                if !exhaustive {
                    alternatives.push(Alternative::match_failure(&[], monotype));
                }
                let kind = ExpressionKind::Case { scrutinees: vec![], alternatives };
                Ok(Expression::new(kind, monotype))
            }
        }
    }

    fn where_expression(
        &mut self,
        scope: &mut Scope,
        where_expression: &tree::WhereExpression,
    ) -> GoResult<Expression> {
        self.let_bindings(scope, &where_expression.bindings, where_expression.expression)
    }

    fn let_bindings(
        &mut self,
        scope: &mut Scope,
        bindings: &tree::LetBindings,
        body: tree::ExpressionId,
    ) -> GoResult<Expression> {
        enum Declared {
            Monomorphic(Local, Arc<[tree::Equation]>),
            Polymorphic(lowering::LetBindingNameGroupId),
        }
        enum Member {
            Monomorphic(Binding),
            Polymorphic(lowering::LetBindingNameGroupId),
        }
        enum Chunk {
            Names(Vec<Vec<Member>>),
            Pattern(Pattern, Expression, bool),
        }
        let module = Arc::clone(&scope.module);
        let mut chunks = Vec::with_capacity(bindings.chunks.len());
        let mut polymorphic = vec![];
        let mut shadowed = vec![];
        for chunk in bindings.chunks.iter() {
            match chunk {
                tree::LetBindingChunk::Pattern { binder, where_expression, .. } => {
                    let value = self.where_expression(scope, where_expression)?;
                    let pattern = self.pattern(scope, *binder)?;
                    let pattern_match = tree::PatternMatch::LetPattern(*binder);
                    let exhaustive = module.checked.tree.is_exhaustive_match(pattern_match);
                    chunks.push(Chunk::Pattern(pattern, value, exhaustive));
                }
                tree::LetBindingChunk::PatternError { .. } => {
                    return Err(self.unsupported(scope, UnsupportedState::BinderError));
                }
                tree::LetBindingChunk::Names { groups, .. } => {
                    let mut declarations = vec![];
                    for group in groups.iter() {
                        let mut members = vec![];
                        for &source in group.as_slice() {
                            let Some(declaration_id) = module.checked.tree.lookup_let(source)
                            else {
                                return Err(self.unsupported(
                                    scope,
                                    UnsupportedState::MissingLocalDeclaration,
                                ));
                            };
                            let declaration = &module.checked.tree[declaration_id];
                            let name = module
                                .lowered
                                .tree
                                .get_let_binding_group(source)
                                .name
                                .clone()
                                .unwrap_or_else(|| SmolStr::new_static("binding"));
                            match self.local_form(scope, declaration)? {
                                LocalForm::Monomorphic => {
                                    let monotype = self.monotype(scope, declaration.type_id)?;
                                    let local = self.fresh_local(name, monotype);
                                    scope.locals.insert(LocalSource::Let(source), local.clone());
                                    let equations = Arc::clone(&declaration.value.equations);
                                    members.push(Declared::Monomorphic(local, equations));
                                }
                                LocalForm::Polymorphic => {
                                    let entry = PolymorphicLocal {
                                        name,
                                        declaration: declaration_id,
                                        specializations: vec![],
                                        active: None,
                                    };
                                    let previous = scope.polymorphic_locals.insert(source, entry);
                                    shadowed.push((source, previous));
                                    polymorphic.push(source);
                                    members.push(Declared::Polymorphic(source));
                                }
                                LocalForm::Alias(expression) => {
                                    scope.local_aliases.insert(source, expression);
                                }
                            }
                        }
                        declarations.push(members);
                    }
                    let mut groups = Vec::with_capacity(declarations.len());
                    for members in declarations {
                        let mut converted = Vec::with_capacity(members.len());
                        for member in members {
                            converted.push(match member {
                                Declared::Monomorphic(local, equations) => {
                                    let value = self.equations(scope, &equations);
                                    let value = self.recover(value, local.monotype)?;
                                    Member::Monomorphic(Binding { local, value })
                                }
                                Declared::Polymorphic(source) => Member::Polymorphic(source),
                            });
                        }
                        groups.push(converted);
                    }
                    chunks.push(Chunk::Names(groups));
                }
            }
        }
        let mut body = self.expression(scope, body)?;
        self.specialize_polymorphic_locals(scope, &polymorphic)?;
        for chunk in chunks.into_iter().rev() {
            match chunk {
                Chunk::Names(groups) => {
                    for members in groups.into_iter().rev() {
                        let mut bindings = vec![];
                        for member in members {
                            match member {
                                Member::Monomorphic(binding) => bindings.push(binding),
                                Member::Polymorphic(source) => {
                                    bindings.extend(self.specialized_bindings(scope, source));
                                }
                            }
                        }
                        if bindings.is_empty() {
                            continue;
                        }
                        let monotype = body.monotype;
                        let kind = ExpressionKind::Let { bindings, body: Box::new(body) };
                        body = Expression::new(kind, monotype);
                    }
                }
                Chunk::Pattern(pattern, value, exhaustive) => {
                    let monotype = body.monotype;
                    let alternative =
                        Alternative { patterns: vec![pattern], body: Guarded::Unconditional(body) };
                    let scrutinees = vec![value];
                    let mut alternatives = vec![alternative];
                    if !exhaustive {
                        alternatives.push(Alternative::match_failure(&scrutinees, monotype));
                    }
                    let kind = ExpressionKind::Case { scrutinees, alternatives };
                    body = Expression::new(kind, monotype);
                }
            }
        }
        for (source, previous) in shadowed.into_iter().rev() {
            match previous {
                Some(previous) => scope.polymorphic_locals.insert(source, previous),
                None => scope.polymorphic_locals.remove(&source),
            };
        }
        Ok(body)
    }

    fn expression(&mut self, scope: &mut Scope, id: tree::ExpressionId) -> GoResult<Expression> {
        let result = self.translate_expression(scope, id);
        if result.is_ok() {
            return result;
        }
        let monotype = self.monotype(scope, scope.module.checked.tree[id].type_id);
        match monotype {
            Ok(monotype) => self.recover(result, monotype),
            Err(error) => {
                self.record(result.err().expect("invariant violated: result is an error"))?;
                Err(error)
            }
        }
    }

    fn translate_expression(
        &mut self,
        scope: &mut Scope,
        id: tree::ExpressionId,
    ) -> GoResult<Expression> {
        if let Some(constructed) = self.rank_n_construction(scope, id)? {
            return Ok(constructed);
        }
        self.translate_expression_at(scope, id)
    }

    /// An expression checked against an unconstrained `forall` (a CPS parser
    /// passed to its constructor, say) becomes one specialization per
    /// instantiation of the quantified variables, as a record of them.
    fn rank_n_construction(
        &mut self,
        scope: &mut Scope,
        id: tree::ExpressionId,
    ) -> GoResult<Option<Expression>> {
        if scope.rank_n_body == Some(id) {
            return Ok(None);
        }
        let type_id = scope.module.checked.tree[id].type_id;
        let closed = self.context.types.substitute(type_id, &scope.substitution);
        let closed = self.instantiate_inner_quantifiers(scope, id, closed);
        if !matches!(
            self.context.types.lookup(self.context.types.strip_annotations(closed)),
            Type::Forall(..)
        ) {
            return Ok(None);
        }
        let Some(scheme) = self.monotypes.scheme_for(&mut self.context, closed)? else {
            return self.grown_construction(scope, id, closed);
        };
        // Checking against a `forall` binds scoped skolems; a polymorphic
        // reference's own quantifiers are instantiated where it is used.
        if !scheme.constraints.is_empty()
            || scheme.names.iter().any(|name| !name.scoped || scope.substitution.contains_key(name))
        {
            return Ok(None);
        }
        let monotype = self.closed_monotype(scope, closed)?;
        self.note_construction(&scheme.key);
        let instantiations = self.monotypes.schemes.get(&scheme.key).to_vec();
        let mut fields = Vec::with_capacity(instantiations.len());
        let enclosing = scope.rank_n_body.replace(id);
        for instantiation in instantiations {
            let substitution = scope.substitution.clone();
            scope
                .substitution
                .extend(scheme.names.iter().copied().zip(instantiation.types.iter().copied()));
            self.constructing.push((scheme.key.clone(), Arc::clone(&instantiation.types)));
            let value = self.translate_expression_at(scope, id);
            self.constructing.pop();
            scope.substitution = substitution;
            match value {
                Ok(value) => fields.push((instantiation.label, value)),
                Err(error) => {
                    scope.rank_n_body = enclosing;
                    return Err(error);
                }
            }
        }
        scope.rank_n_body = enclosing;
        fields.sort_by(|left, right| left.0.cmp(&right.0));
        Ok(Some(Expression::new(ExpressionKind::Record(fields), monotype)))
    }

    /// A polymorphic reference checked against a `forall` has the type
    /// `forall sk. <its own forall a. ...>`; its own quantifiers are
    /// instantiated in terms of the skolems where it is used, as the tree
    /// records, which leaves the rank-N type it is checked against.
    fn instantiate_inner_quantifiers(
        &mut self,
        scope: &Scope,
        id: tree::ExpressionId,
        closed: TypeId,
    ) -> TypeId {
        let stripped = self.context.types.strip_annotations(closed);
        let Type::Forall(binder, inner) = self.context.types.lookup(stripped).clone() else {
            return closed;
        };
        if !self.context.queries.lookup_forall_binder(binder).name.scoped {
            return closed;
        }
        let rest = self.instantiate_inner_quantifiers(scope, id, inner);
        let (names, body) = self.context.types.peel_quantifiers(rest);
        if names.iter().all(|name| name.scoped) || names.is_empty() {
            return self.context.queries.intern_type(Type::Forall(binder, rest));
        }
        let instantiations = self.recorded_instantiations(scope, id);
        if !names.iter().all(|name| instantiations.contains_key(name)) {
            return closed;
        }
        let (_, body) = self.context.types.peel_constraints(body);
        let body = self.context.types.substitute(body, &instantiations);
        self.context.queries.intern_type(Type::Forall(binder, body))
    }

    fn translate_expression_at(
        &mut self,
        scope: &mut Scope,
        id: tree::ExpressionId,
    ) -> GoResult<Expression> {
        let module = Arc::clone(&scope.module);
        let node = &module.checked.tree[id];
        let kind = match &node.kind {
            tree::ExpressionKind::Error => {
                return Err(self.unsupported(scope, UnsupportedState::ExpressionError));
            }
            tree::ExpressionKind::String { value, .. } => {
                ExpressionKind::Literal(string_literal(value))
            }
            tree::ExpressionKind::Char { value } => ExpressionKind::Literal(Literal::Char(*value)),
            tree::ExpressionKind::Boolean { value } => {
                ExpressionKind::Literal(Literal::Boolean(*value))
            }
            tree::ExpressionKind::Integer { value } => {
                let monotype = self.monotype(scope, node.type_id)?;
                if let Monotype::Number = self.monotypes.get(monotype) {
                    let value = format_smolstr!("{value}");
                    return Ok(Expression::new(
                        ExpressionKind::Literal(Literal::Number(value)),
                        monotype,
                    ));
                }
                ExpressionKind::Literal(Literal::Int(*value))
            }
            tree::ExpressionKind::Number { value } => {
                ExpressionKind::Literal(Literal::Number(value.clone()))
            }
            tree::ExpressionKind::Array { elements } => {
                let mut converted = Vec::with_capacity(elements.len());
                for &element in elements.iter() {
                    converted.push(self.expression(scope, element)?);
                }
                ExpressionKind::Array(converted)
            }
            tree::ExpressionKind::Record { fields } => {
                let mut converted = Vec::with_capacity(fields.len());
                for field in fields.iter() {
                    let (label, expression) = match field {
                        tree::RecordExpressionField::Field { label, expression }
                        | tree::RecordExpressionField::Pun { label, expression, .. } => {
                            (label, expression)
                        }
                    };
                    converted.push((label.clone(), self.expression(scope, *expression)?));
                }
                ExpressionKind::Record(converted)
            }
            tree::ExpressionKind::RecordAccess { record, labels } => {
                let mut record = self.expression(scope, *record)?;
                for label in labels.iter() {
                    let monotype = self.field_monotype(scope, record.monotype, label)?;
                    let kind =
                        ExpressionKind::Access { record: Box::new(record), label: label.clone() };
                    record = Expression::new(kind, monotype);
                }
                return Ok(record);
            }
            tree::ExpressionKind::RecordUpdate { record, updates } => {
                let record = self.expression(scope, *record)?;
                let updates = self.record_updates(scope, updates)?;
                ExpressionKind::Update { record: Box::new(record), updates }
            }
            tree::ExpressionKind::Constructor { .. }
            | tree::ExpressionKind::Variable { .. }
            | tree::ExpressionKind::RecordPun { .. }
            | tree::ExpressionKind::EvidenceApplication { .. } => {
                return self.reference(scope, id, Substitution::default(), None);
            }
            tree::ExpressionKind::Section { binder } => {
                return self.local_reference(scope, self.checked_binder_source(scope, *binder));
            }
            tree::ExpressionKind::TermApplication { .. } => return self.application(scope, id),
            tree::ExpressionKind::EvidenceAbstraction { binder, expression } => {
                let constraint = module.checked.evidence[*binder].constraint;
                if crate::monotype::is_partial(&mut self.context, constraint)? {
                    scope.givens.insert(*binder, Dictionary::Trivial);
                    return self.expression(scope, *expression);
                }
                return self.scheme_construction(scope, id);
            }
            tree::ExpressionKind::Lambda { binders, expression } => {
                if let Some(parameters) = self.variable_parameters(scope, binders)? {
                    let body = self.expression(scope, *expression)?;
                    return Ok(self.lambda(parameters, body));
                }
                let mut parameters = Vec::with_capacity(binders.len());
                let mut patterns = Vec::with_capacity(binders.len());
                for &binder in binders.iter() {
                    let pattern = self.pattern(scope, binder)?;
                    let name = self.parameter_name(scope, [binder], pattern.monotype);
                    parameters.push(self.fresh_local(name, pattern.monotype));
                    patterns.push(pattern);
                }
                let body = self.expression(scope, *expression)?;
                let monotype = body.monotype;
                let scrutinees: Vec<Expression> = parameters.iter().map(Local::expression).collect();
                let alternative = Alternative { patterns, body: Guarded::Unconditional(body) };
                let mut alternatives = vec![alternative];
                if !module.checked.tree.is_exhaustive_match(tree::PatternMatch::Expression(id)) {
                    alternatives.push(Alternative::match_failure(&scrutinees, monotype));
                }
                let kind = ExpressionKind::Case { scrutinees, alternatives };
                let body = Expression::new(kind, monotype);
                return Ok(self.lambda(parameters, body));
            }
            tree::ExpressionKind::IfThenElse { condition, then, else_ } => ExpressionKind::If {
                condition: Box::new(self.expression(scope, *condition)?),
                then: Box::new(self.expression(scope, *then)?),
                otherwise: Box::new(self.expression(scope, *else_)?),
            },
            tree::ExpressionKind::Case { scrutinees, alternatives } => {
                let mut converted_scrutinees = Vec::with_capacity(scrutinees.len());
                for &scrutinee in scrutinees.iter() {
                    converted_scrutinees.push(self.expression(scope, scrutinee)?);
                }
                let mut converted = Vec::with_capacity(alternatives.len());
                for alternative in alternatives.iter() {
                    let mut patterns = Vec::with_capacity(alternative.binders.len());
                    for &binder in alternative.binders.iter() {
                        patterns.push(self.pattern(scope, binder)?);
                    }
                    let body = self.guarded(scope, &alternative.guarded_expression)?;
                    converted.push(Alternative { patterns, body });
                }
                if !module.checked.tree.is_exhaustive_match(tree::PatternMatch::Expression(id)) {
                    let monotype = self.monotype(scope, node.type_id)?;
                    converted.push(Alternative::match_failure(&converted_scrutinees, monotype));
                }
                ExpressionKind::Case { scrutinees: converted_scrutinees, alternatives: converted }
            }
            tree::ExpressionKind::Let { bindings, expression } => {
                return self.let_bindings(scope, bindings, *expression);
            }
        };
        let monotype = self.monotype(scope, node.type_id)?;
        Ok(Expression::new(kind, monotype))
    }

    fn field_monotype(
        &mut self,
        scope: &Scope,
        record: MonotypeId,
        label: &str,
    ) -> GoResult<MonotypeId> {
        if let Monotype::Record(fields) = self.monotypes.get(record)
            && let Some(field) = fields.iter().find(|field| field.label == label)
        {
            return Ok(field.monotype);
        }
        Err(self
            .unsupported(scope, UnsupportedState::OpenType { rendered: format!("{{ {label} }}") }))
    }

    fn record_updates(
        &mut self,
        scope: &mut Scope,
        updates: &[tree::RecordExpressionUpdate],
    ) -> GoResult<Vec<RecordUpdate>> {
        let mut converted = Vec::with_capacity(updates.len());
        for update in updates {
            converted.push(match update {
                tree::RecordExpressionUpdate::Leaf { label, expression } => RecordUpdate::Leaf {
                    label: label.clone(),
                    value: self.expression(scope, *expression)?,
                },
                tree::RecordExpressionUpdate::Branch { label, updates } => RecordUpdate::Branch {
                    label: label.clone(),
                    updates: self.record_updates(scope, updates)?,
                },
                tree::RecordExpressionUpdate::Error => {
                    return Err(self.unsupported(scope, UnsupportedState::ExpressionError));
                }
            });
        }
        Ok(converted)
    }

    fn application(&mut self, scope: &mut Scope, id: tree::ExpressionId) -> GoResult<Expression> {
        let module = Arc::clone(&scope.module);
        let spine::ApplicationSpine { head, arguments, trailing: evidence, instantiations } =
            self.application_spine(scope, id);
        let mut result_instantiations = instantiations;
        self.context.types.close(&mut result_instantiations);
        let monotype = self.instantiated_result_monotype(
            scope,
            module.checked.tree[id].type_id,
            &result_instantiations,
        )?;
        let trailing = self.trailing_dictionaries(scope, &evidence)?;
        if let tree::ExpressionKind::Constructor { resolution } = module.checked.tree[head].kind
            && trailing.is_empty()
            && self.is_newtype_constructor(resolution)?
            && let [argument] = arguments[..]
        {
            let mut argument = self.expression(scope, argument)?;
            if matches!(self.monotypes.get(monotype), Monotype::Recursive(_)) {
                return Ok(argument);
            }
            if self.mentions_erased(monotype) {
                return Ok(self.coerce(argument, monotype));
            }
            argument.monotype = monotype;
            return Ok(argument);
        }
        if !trailing.is_empty()
            && let [argument] = arguments[..]
            && self.is_unsafe_coerce(scope, head)?
        {
            let result = module.checked.tree[id].type_id;
            let result = self.context.types.substitute(result, &scope.substitution);
            let result = (result, monotype);
            return self.coerced_with_evidence(scope, argument, &evidence, trailing, result);
        }
        if trailing.is_empty()
            && let Some(reference) = self.traversal_reference(scope, head, &arguments)?
        {
            return self.traverse_array(scope, reference, &arguments);
        }
        let head_type = self.instantiated_node_type(scope, head, &result_instantiations);
        let function = match module.checked.tree[head].kind {
            tree::ExpressionKind::Constructor { .. }
            | tree::ExpressionKind::Variable { .. }
            | tree::ExpressionKind::RecordPun { .. }
            | tree::ExpressionKind::EvidenceApplication { .. } => {
                self.trailed_reference(scope, head, result_instantiations.clone(), None, trailing)
            }
            _ if trailing.is_empty() => self.expression(scope, head),
            _ => Err(self.unsupported(
                scope,
                UnsupportedState::Construct { construct: "evidence applied to a non-reference" },
            )),
        };
        let mut function = match function {
            Ok(function) => function,
            Err(error) => {
                self.record(error)?;
                for argument in arguments {
                    self.expression(scope, argument)?;
                }
                let blocked = SmolStr::new_static("blocked");
                return Ok(Expression::new(ExpressionKind::Fail(blocked), monotype));
            }
        };
        let mut parameter_type = head_type;
        let mut callee = IgnoringCallee::of(&function, 0);
        let mut converted = Vec::with_capacity(arguments.len());
        for (position, argument) in arguments.into_iter().enumerate() {
            let expected = self.next_parameter_type(parameter_type, &result_instantiations)?;
            if let Some((_, result)) = expected {
                parameter_type = result;
            }
            if let Some(parameter) = callee.ignores(&self.monotypes, position) {
                let ignored = SmolStr::new_static("ignored foreign argument");
                converted.push(Expression::new(ExpressionKind::Fail(ignored), parameter));
                continue;
            }
            let converted_argument = match (&module.checked.tree[argument].kind, expected) {
                (
                    tree::ExpressionKind::Variable { .. }
                    | tree::ExpressionKind::EvidenceApplication { .. },
                    Some((expected, _)),
                ) if !self.is_continuation(scope, expected)? => {
                    self.reference(scope, argument, Substitution::default(), Some(expected))?
                }
                _ => self.expression(scope, argument)?,
            };
            if position == 0 && is_foreign_wrapper(&function, Foreign::Identity) {
                callee = IgnoringCallee::of(&converted_argument, 1);
            }
            converted.push(converted_argument);
        }
        if let Monotype::Erased(_) = self.monotypes.get(function.monotype) {
            let mut expected = monotype;
            for argument in converted.iter().rev() {
                expected = self.monotypes.function(argument.monotype, expected);
            }
            function = self.coerce(function, expected);
        }
        let mut result = function.monotype;
        let mut coerced = Vec::with_capacity(converted.len());
        for argument in converted {
            match self.monotypes.function_parts(result) {
                Some((parameter, rest)) => {
                    coerced.push(self.coerce(argument, parameter));
                    result = rest;
                }
                None => coerced.push(argument),
            }
        }
        let kind = ExpressionKind::Apply { function: Box::new(function), arguments: coerced };
        if result != monotype && self.mentions_erased(result) {
            let applied = Expression::new(kind, result);
            return Ok(self.coerce(applied, monotype));
        }
        Ok(Expression::new(kind, monotype))
    }

    fn is_continuation(&mut self, scope: &Scope, expected: TypeId) -> GoResult<bool> {
        let closed = self.context.types.substitute(expected, &scope.substitution);
        let Some(scheme) = crate::scheme::rank_n_scheme(&mut self.context, closed)? else {
            return Ok(false);
        };
        Ok(self.monotypes.schemes.continuation_family(&scheme.key).is_some())
    }

    /// The type a reference node stands at. The checker gives the node the
    /// declared type and records the instantiations of its quantifiers apart,
    /// on the node, its evidence applications, and the applications of it.
    fn instantiated_node_type(
        &self,
        scope: &Scope,
        node: tree::ExpressionId,
        result_instantiations: &Substitution,
    ) -> TypeId {
        let tree = &scope.module.checked.tree;
        let mut substitution = result_instantiations.clone();
        substitution.extend(self.recorded_instantiations(scope, node));
        self.context.types.close(&mut substitution);
        let node_type = self.outer_body(tree[node].type_id, &mut vec![]);
        let node_type = self.context.types.substitute(node_type, &substitution);
        self.context.types.substitute(node_type, &scope.substitution)
    }

    /// The instantiations recorded at a reference and its evidence applications.
    fn recorded_instantiations(&self, scope: &Scope, node: tree::ExpressionId) -> Substitution {
        let tree = &scope.module.checked.tree;
        let mut recorded = Substitution::default();
        let mut current = node;
        loop {
            for instantiation in tree.lookup_instantiations(current) {
                recorded.insert(instantiation.name, instantiation.argument);
            }
            match tree[current].kind {
                tree::ExpressionKind::EvidenceApplication { function, .. } => current = function,
                _ => break,
            }
        }
        self.closed_instantiations(scope, recorded)
    }

    /// The instantiations the checker recorded at one reference, closed. They
    /// bind their names at that reference: where a synonym quantifies both the
    /// enclosing definition and an annotation inside it (`conv :: m ~> m'` using
    /// `identity :: List ~> List`), its quantifier is instantiated at the
    /// annotation as the reference records, not as the enclosing scope does.
    fn closed_instantiations(&self, scope: &Scope, mut recorded: Substitution) -> Substitution {
        self.context.types.close(&mut recorded);
        for argument in recorded.values_mut() {
            *argument = self.context.types.substitute(*argument, &scope.substitution);
        }
        recorded
    }

    fn instantiated_result_monotype(
        &mut self,
        scope: &Scope,
        type_id: TypeId,
        result_instantiations: &Substitution,
    ) -> GoResult<MonotypeId> {
        if result_instantiations.is_empty() {
            return self.monotype(scope, type_id);
        }
        let stripped =
            self.strip_instantiated_result_quantifiers(type_id, result_instantiations)?;
        let instantiated = self.context.types.substitute(stripped, result_instantiations);
        self.monotype(scope, instantiated)
    }
    fn coerce(&mut self, mut expression: Expression, monotype: MonotypeId) -> Expression {
        if self.monotypes.same_without_causes(expression.monotype, monotype) {
            expression.monotype = monotype;
            return expression;
        }
        if !self.changes_representation(expression.monotype, monotype) {
            return expression;
        }
        self.note_crossings(expression.monotype, monotype);
        Expression::new(ExpressionKind::Coerce(Box::new(expression)), monotype)
    }

    /// Whether a value of one type needs converting to stand at another: the
    /// types of one value differ in representation only through erasure or a
    /// recursive newtype.
    fn changes_representation(&self, from: MonotypeId, to: MonotypeId) -> bool {
        !self.monotypes.same_without_causes(from, to)
            && (self.mentions_erased(from)
                || self.mentions_erased(to)
                || self.mentions_recursive(from)
                || self.mentions_recursive(to)
                || self.mentions_variant(from)
                || self.mentions_variant(to))
    }

    /// Whether a type contains a recursive newtype, whose named Go type differs
    /// from its unfolded representation inside function types.
    fn mentions_recursive(&self, monotype: MonotypeId) -> bool {
        match self.monotypes.get(monotype) {
            Monotype::Recursive(_) => true,
            Monotype::Array(inner)
            | Monotype::Effect(inner)
            | Monotype::Lazy(inner)
            | Monotype::ConsList(inner)
            | Monotype::Nullable(inner) => self.mentions_recursive(*inner),
            Monotype::Function(argument, result) => {
                self.mentions_recursive(*argument) || self.mentions_recursive(*result)
            }
            _ => false,
        }
    }

    fn mentions_erased(&self, monotype: MonotypeId) -> bool {
        match self.monotypes.get(monotype) {
            Monotype::Erased(_) => true,
            Monotype::Function(argument, result) => {
                self.mentions_erased(*argument) || self.mentions_erased(*result)
            }
            Monotype::Record(fields) => {
                fields.iter().any(|field| self.mentions_erased(field.monotype))
            }
            Monotype::Data(data) | Monotype::Recursive(data) | Monotype::ForeignData(data) => {
                data.arguments.iter().any(|&argument| self.context.types.contains_erased(argument))
            }
            other => other.element().is_some_and(|element| self.mentions_erased(element)),
        }
    }

    fn is_newtype_constructor(&mut self, (file_id, term): (FileId, TermItemId)) -> GoResult<bool> {
        let module = self.context.module(file_id)?;
        let IndexedTermItemKind::Constructor { type_id: Some(type_item), .. } =
            module.indexed.items[term].kind
        else {
            return Ok(false);
        };
        Ok(matches!(
            module.indexed.items[type_item].kind,
            indexing::IndexedTypeItemKind::Newtype { .. }
        ))
    }

    fn checked_binder_source(&self, scope: &Scope, binder: tree::BinderId) -> LocalSource {
        match scope.module.checked.tree[binder].source {
            tree::BinderSource::Binder(source) => LocalSource::Binder(source),
            _ => LocalSource::Checked(binder),
        }
    }

    fn scheme_construction(
        &mut self,
        scope: &mut Scope,
        id: tree::ExpressionId,
    ) -> GoResult<Expression> {
        let module = Arc::clone(&scope.module);
        let closed =
            self.context.types.substitute(module.checked.tree[id].type_id, &scope.substitution);
        let Some(scheme) = constrained_scheme(&mut self.context, closed)? else {
            return Err(self.unsupported(
                scope,
                UnsupportedState::Construct { construct: "constrained higher-rank arguments" },
            ));
        };
        let mut binders = vec![];
        let mut body = id;
        while let tree::ExpressionKind::EvidenceAbstraction { binder, expression } =
            module.checked.tree[body].kind
        {
            binders.push(binder);
            body = expression;
        }
        if binders.len() != scheme.constraints.len() {
            return Err(self.unsupported(
                scope,
                UnsupportedState::Construct { construct: "constrained higher-rank arguments" },
            ));
        }
        let monotype = self.closed_monotype(scope, closed)?;
        self.note_construction(&scheme.key);
        let instantiations = self.monotypes.schemes.get(&scheme.key).to_vec();
        let mut fields = Vec::with_capacity(instantiations.len());
        for instantiation in instantiations {
            let (parameters, dictionaries) =
                self.reified_parameters(scope, &scheme, &instantiation)?;
            let substitution = scope.substitution.clone();
            let givens = scope.givens.clone();
            scope
                .substitution
                .extend(scheme.names.iter().copied().zip(instantiation.types.iter().copied()));
            scope.givens.extend(binders.iter().copied().zip(dictionaries));
            self.constructing.push((scheme.key.clone(), Arc::clone(&instantiation.types)));
            let value = self.expression(scope, body);
            self.constructing.pop();
            scope.substitution = substitution;
            scope.givens = givens;
            let value = match parameters.is_empty() {
                true => value?,
                false => self.lambda(parameters, value?),
            };
            fields.push((instantiation.label, value));
        }
        fields.sort_by(|left, right| left.0.cmp(&right.0));
        Ok(Expression::new(ExpressionKind::Record(fields), monotype))
    }

    fn instantiated_local_reference(
        &mut self,
        scope: &mut Scope,
        source: LocalSource,
        instantiations: &Substitution,
        dictionaries: Vec<Dictionary>,
    ) -> GoResult<Expression> {
        let local = self.local_reference(scope, source)?;
        let scheme = match scope.scheme_locals.get(&source) {
            Some(&closed) => self.monotypes.scheme_for(&mut self.context, closed)?,
            None => None,
        };
        let Some(scheme) = scheme else {
            if !dictionaries.is_empty() {
                return Err(self.unsupported(scope, UnsupportedState::UnabstractedEvidence));
            }
            return Ok(local);
        };
        let uninstantiated = scheme.names.iter().find(|name| !instantiations.contains_key(name));
        if let Some(&name) = uninstantiated {
            let passed_whole = dictionaries.is_empty()
                && scheme.names.iter().all(|name| !instantiations.contains_key(name));
            if passed_whole {
                return Ok(local);
            }
            let variable = match scope.module.checked.lookup_name(name) {
                Some(text) => self.context.queries.lookup_smol_str(text).to_string(),
                None => name.as_text().to_string(),
            };
            return Err(
                self.unsupported(scope, UnsupportedState::UninstantiatedVariable { variable })
            );
        }
        let types: Vec<TypeId> = scheme.names.iter().map(|name| instantiations[name]).collect();
        let instantiated = scheme.instantiate(&self.context, &types);
        let monotype = self.closed_monotype(scope, instantiated)?;
        if let Some(known) = self.monotypes.schemes.find(&scheme.key, &types) {
            let label = known.label.clone();
            let kind = ExpressionKind::Access { record: Box::new(local), label };
            return Ok(Expression::new(kind, monotype));
        }
        self.discover(scope, scheme.key, types, dictionaries)?;
        self.note_pending();
        let pending = SmolStr::new_static("instantiation discovered in this pass");
        Ok(Expression::new(ExpressionKind::Fail(pending), monotype))
    }

    /// The parameters an instantiation's field takes for the values it reifies at run time,
    /// and its dictionaries with each reified one passed on at run time from its parameter.
    fn reified_parameters(
        &mut self,
        scope: &Scope,
        scheme: &crate::scheme::ConstrainedScheme,
        instantiation: &SchemeInstantiation,
    ) -> GoResult<(Vec<Local>, Vec<Dictionary>)> {
        let mut reified = scheme.reified_constraints(&self.context, instantiation).into_iter();
        let mut parameters = vec![];
        let mut dictionaries = Vec::with_capacity(instantiation.dictionaries.len());
        for dictionary in instantiation.dictionaries.iter() {
            let Dictionary::Reflectable(Reflected::Reified) = dictionary else {
                dictionaries.push(dictionary.clone());
                continue;
            };
            let Some(constraint) = reified.next() else {
                return Err(self.unsupported(scope, UnsupportedState::UnboundEvidence));
            };
            let Some(&reflected) = self.context.types.spine(constraint).1.last() else {
                return Err(self.unsupported(scope, UnsupportedState::UnboundEvidence));
            };
            let monotype = self.closed_monotype(scope, reflected)?;
            let parameter = self.fresh_local(SmolStr::new_static("reified"), monotype);
            let value = parameter.expression();
            dictionaries.push(self.reified_dictionary(&scope.definition, constraint, value)?);
            parameters.push(parameter);
        }
        Ok((parameters, dictionaries))
    }

    fn discover(
        &mut self,
        scope: &Scope,
        key: SchemeKey,
        types: Vec<TypeId>,
        dictionaries: Vec<Dictionary>,
    ) -> GoResult<()> {
        self.discover_labelled(scope, key, types, dictionaries, None)
    }

    fn discover_labelled(
        &mut self,
        scope: &Scope,
        key: SchemeKey,
        types: Vec<TypeId>,
        dictionaries: Vec<Dictionary>,
        preferred: Option<SmolStr>,
    ) -> GoResult<()> {
        if self.grows_construction(&key, &types) {
            let Some(owner) = self.monotypes.schemes.rank_n_owner(&key) else {
                return Err(self.unsupported(scope, UnsupportedState::GrowingEvidence));
            };
            self.growing_owners.push(owner.to_string());
            self.grown = true;
            return Ok(());
        }
        let known = self.monotypes.schemes.get(&key);
        let labels: Vec<SmolStr> = known.iter().map(|known| known.label.clone()).collect();
        if labels.len() >= SCHEME_INSTANTIATION_LIMIT {
            return Err(self.unsupported(
                scope,
                UnsupportedState::SpecializationLimit { limit: SCHEME_INSTANTIATION_LIMIT },
            ));
        }
        let label = match preferred.filter(|preferred| !labels.contains(preferred)) {
            Some(preferred) => preferred,
            None => self.fresh_instantiation_label(&types, &labels)?,
        };
        let instantiation = SchemeInstantiation {
            types: Arc::from(types),
            dictionaries: Arc::from(dictionaries),
            label,
        };
        // The rest of this pass already specializes the new instantiation, so a
        // chain of instantiations, each met only inside the previous one, is
        // discovered in one pass instead of one pass per link. Values built
        // before it lack it, so the pass is repeated.
        if let Some(functions) = self.constructions.get(&key) {
            self.stale.extend(functions.iter().copied());
        }
        self.monotypes.schemes.insert(key.clone(), instantiation.clone());
        self.grown = true;
        for source in self.monotypes.schemes.coerced_sources(&key).to_vec() {
            self.share_instantiation(scope, source, &instantiation)?;
        }
        Ok(())
    }

    fn fresh_instantiation_label(
        &mut self,
        types: &[TypeId],
        labels: &[SmolStr],
    ) -> GoResult<SmolStr> {
        let mut suffix = String::new();
        for &type_id in types {
            self.instantiation_suffix(type_id, &mut suffix)?;
        }
        let base: String =
            suffix.chars().filter(|character| character.is_ascii_alphanumeric()).collect();
        let base = if base.is_empty() { String::from("Instance") } else { base };
        let mut label = SmolStr::from(&base);
        let mut index = 1;
        while labels.contains(&label) {
            label = format_smolstr!("{base}{index}");
            index += 1;
        }
        Ok(label)
    }

    /// A type's spelling in an instantiation's label, as `type_suffix` spells
    /// it, except that a record a synonym or newtype names is spelled by that
    /// name: `SurfaceAnim` rather than all its labels.
    fn instantiation_suffix(&mut self, type_id: TypeId, output: &mut String) -> GoResult<()> {
        let type_id = self.context.types.strip_annotations(type_id);
        match self.context.types.lookup(type_id).clone() {
            Type::Application(function, argument) => {
                if let Some(name) = self.declared_record_name(function, argument)? {
                    output.push_str(&name);
                    return Ok(());
                }
                self.instantiation_suffix(function, output)?;
                self.instantiation_suffix(argument, output)?;
            }
            Type::Function(argument, result) => {
                output.push_str("Fn");
                self.instantiation_suffix(argument, output)?;
                self.instantiation_suffix(result, output)?;
            }
            _ => self.context.type_suffix(type_id, output)?,
        }
        Ok(())
    }

    /// The name of the synonym or newtype, without arguments, that spelled
    /// the record `Record row` where a type was converted.
    fn declared_record_name(&mut self, function: TypeId, row: TypeId) -> GoResult<Option<String>> {
        let function = self.context.types.strip_annotations(function);
        let Type::Constructor(file_id, item) = self.context.types.lookup(function).clone() else {
            return Ok(None);
        };
        if file_id != self.context.queries.prim_id()
            || self.context.type_name(file_id, item)? != "Record"
        {
            return Ok(None);
        }
        let Some(record) = supported(self.monotypes.record(&mut self.context, row))? else {
            return Ok(None);
        };
        let Some(spellings) = self.monotypes.record_spellings.get(&record) else {
            return Ok(None);
        };
        let declared = spellings.iter().find(|(_, _, arguments)| arguments.is_empty());
        let Some(&(file_id, item, _)) = declared else { return Ok(None) };
        Ok(Some(crate::naming::capitalise(&self.context.type_name(file_id, item)?)))
    }

    fn share_instantiation(
        &mut self,
        scope: &Scope,
        source: SchemeKey,
        instantiation: &SchemeInstantiation,
    ) -> GoResult<()> {
        if self.monotypes.schemes.find(&source, &instantiation.types).is_some() {
            return Ok(());
        }
        let types = instantiation.types.to_vec();
        let dictionaries = instantiation.dictionaries.to_vec();
        let label = Some(instantiation.label.clone());
        self.discover_labelled(scope, source, types, dictionaries, label)
    }

    fn link_coerced_rank_n(
        &mut self,
        scope: &Scope,
        file_id: FileId,
        term: TermItemId,
        instantiations: &Substitution,
    ) -> GoResult<()> {
        let module = self.context.module(file_id)?;
        let Some(declared) = module.checked.lookup_term_item_type(term) else {
            return Ok(());
        };
        let declared = self.outer_body(declared, &mut vec![]);
        let closed = self.context.types.substitute(declared, instantiations);
        let Some((from, to)) = self.context.types.function_parts(closed) else {
            return Ok(());
        };
        self.link_coercion(scope, from, to)
    }

    fn link_coercion(&mut self, scope: &Scope, from: TypeId, to: TypeId) -> GoResult<()> {
        let from = crate::monotype::expand_synonyms(&mut self.context, from)?;
        let to = crate::monotype::expand_synonyms(&mut self.context, to)?;
        if let (Some((from_argument, from_result)), Some((to_argument, to_result))) =
            (self.context.types.function_parts(from), self.context.types.function_parts(to))
        {
            self.link_coercion(scope, to_argument, from_argument)?;
            return self.link_coercion(scope, from_result, to_result);
        }
        let source = self.monotypes.rank_n_key(&mut self.context, from)?;
        let target = self.monotypes.rank_n_key(&mut self.context, to)?;
        let (Some(source), Some(target)) = (source, target) else { return Ok(()) };
        if source == target || !self.monotypes.schemes.link_coercion(source.clone(), target.clone())
        {
            return Ok(());
        }
        for instantiation in self.monotypes.schemes.get(&target).to_vec() {
            self.share_instantiation(scope, source.clone(), &instantiation)?;
        }
        Ok(())
    }

    fn local_reference(&mut self, scope: &Scope, source: LocalSource) -> GoResult<Expression> {
        let Some(local) = scope.locals.get(&source) else {
            return Err(self.unsupported(
                scope,
                UnsupportedState::Construct {
                    construct: "references to locals outside their scope",
                },
            ));
        };
        Ok(Expression::new(ExpressionKind::Local(local.id), local.monotype))
    }

    fn reference(
        &mut self,
        scope: &mut Scope,
        id: tree::ExpressionId,
        instantiations: Substitution,
        expected: Option<TypeId>,
    ) -> GoResult<Expression> {
        self.trailed_reference(scope, id, instantiations, expected, vec![])
    }

    fn trailed_reference(
        &mut self,
        scope: &mut Scope,
        id: tree::ExpressionId,
        mut instantiations: Substitution,
        expected: Option<TypeId>,
        trailing: Vec<Dictionary>,
    ) -> GoResult<Expression> {
        let module = Arc::clone(&scope.module);
        let tree = &module.checked.tree;
        let mut dictionaries = vec![];
        let mut current = id;
        let mut through_alias = false;
        let resolution = loop {
            let mut evidences = vec![];
            let mut recorded = Substitution::default();
            loop {
                for instantiation in tree.lookup_instantiations(current) {
                    recorded.insert(instantiation.name, instantiation.argument);
                }
                match tree[current].kind {
                    tree::ExpressionKind::EvidenceApplication {
                        function,
                        evidence,
                        constraint,
                    } => {
                        evidences.push((evidence, constraint));
                        current = function;
                    }
                    _ => break,
                }
            }
            instantiations.extend(self.closed_instantiations(scope, recorded));
            self.context.types.close(&mut instantiations);
            evidences.reverse();
            for (evidence, constraint) in evidences {
                let constraint = self.context.types.substitute(constraint, &scope.substitution);
                dictionaries.push(self.resolve_evidence(
                    &scope.evidence(),
                    evidence,
                    constraint,
                )?);
            }

            let resolution = match &tree[current].kind {
                tree::ExpressionKind::Variable { resolution }
                | tree::ExpressionKind::RecordPun { resolution, .. } => *resolution,
                tree::ExpressionKind::Constructor { resolution } if trailing.is_empty() => {
                    let (file_id, term) = *resolution;
                    let monotype =
                        self.instantiated_monotype(scope, current, file_id, term, &instantiations)?;
                    return self.constructor(scope, file_id, term, monotype);
                }
                tree::ExpressionKind::EvidenceAbstraction { .. } => {
                    dictionaries.extend(trailing);
                    return self.evidence_redex(scope, current, dictionaries);
                }
                tree::ExpressionKind::TermApplication { .. }
                    if !through_alias && !dictionaries.is_empty() && trailing.is_empty() =>
                {
                    return self.application(scope, id);
                }
                _ => {
                    if dictionaries.is_empty() && trailing.is_empty() {
                        return self.expression(scope, current);
                    }
                    return Err(self.unsupported(
                        scope,
                        UnsupportedState::Construct {
                            construct: "evidence applied to a non-reference",
                        },
                    ));
                }
            };
            if let tree::VariableResolution::Source(lowering::TermVariableResolution::Let(group)) =
                resolution
                && let Some(&aliased) = scope.local_aliases.get(&group)
            {
                current = aliased;
                through_alias = true;
                continue;
            }
            break resolution;
        };
        dictionaries.extend(trailing);

        match resolution {
            tree::VariableResolution::Generated(binder) => {
                let source = self.checked_binder_source(scope, binder);
                self.instantiated_local_reference(scope, source, &instantiations, dictionaries)
            }
            tree::VariableResolution::Source(lowering::TermVariableResolution::Binder(binder)) => {
                let source = LocalSource::Binder(binder);
                self.instantiated_local_reference(scope, source, &instantiations, dictionaries)
            }
            tree::VariableResolution::Source(lowering::TermVariableResolution::Let(group))
                if scope.polymorphic_locals.contains_key(&group) =>
            {
                self.polymorphic_local_reference(scope, group, &instantiations, dictionaries)
            }
            tree::VariableResolution::Source(lowering::TermVariableResolution::Let(group)) => {
                let source = LocalSource::Let(group);
                self.instantiated_local_reference(scope, source, &instantiations, dictionaries)
            }
            tree::VariableResolution::Source(lowering::TermVariableResolution::RecordPun(pun)) => {
                let source = LocalSource::RecordPun(pun);
                self.instantiated_local_reference(scope, source, &instantiations, dictionaries)
            }
            tree::VariableResolution::Source(lowering::TermVariableResolution::Reference(
                file_id,
                term,
            )) => {
                let checked = expected.unwrap_or(tree[id].type_id);
                self.erase_rank_n_skolems(scope, checked, &mut instantiations)?;
                self.recover_unrecorded_instantiations(
                    scope,
                    checked,
                    file_id,
                    term,
                    &mut instantiations,
                )?;
                let monotype =
                    self.instantiated_monotype(scope, current, file_id, term, &instantiations)?;
                self.global_reference(scope, file_id, term, &instantiations, dictionaries, monotype)
            }
        }
    }

    fn evidence_redex(
        &mut self,
        scope: &mut Scope,
        abstraction: tree::ExpressionId,
        dictionaries: Vec<Dictionary>,
    ) -> GoResult<Expression> {
        let module = Arc::clone(&scope.module);
        let tree = &module.checked.tree;
        let mut binders = Vec::with_capacity(dictionaries.len());
        let mut body = abstraction;
        while binders.len() < dictionaries.len()
            && let tree::ExpressionKind::EvidenceAbstraction { binder, expression } =
                tree[body].kind
        {
            binders.push(binder);
            body = expression;
        }
        if binders.len() != dictionaries.len() {
            return Err(self.unsupported(
                scope,
                UnsupportedState::Construct { construct: "evidence applied to a non-reference" },
            ));
        }
        let previous: Vec<_> = binders
            .iter()
            .zip(dictionaries)
            .map(|(&binder, dictionary)| (binder, scope.givens.insert(binder, dictionary)))
            .collect();
        let reduced = self.expression(scope, body);
        for (binder, given) in previous {
            match given {
                Some(dictionary) => scope.givens.insert(binder, dictionary),
                None => scope.givens.remove(&binder),
            };
        }
        reduced
    }

    fn local_form(
        &self,
        scope: &Scope,
        declaration: &tree::LocalDeclaration,
    ) -> GoResult<LocalForm> {
        let abstracted = declaration
            .value
            .abstractions
            .iter()
            .any(|abstraction| !matches!(abstraction, DeclarationAbstraction::Argument));
        if abstracted {
            return Ok(LocalForm::Polymorphic);
        }
        let (names, inner) = self.context.types.peel_quantifiers(declaration.type_id);
        let (constraints, _) = self.context.types.peel_constraints(inner);
        if names.is_empty() && constraints.is_empty() {
            return Ok(LocalForm::Monomorphic);
        }
        if let [equation] = declaration.value.equations.as_ref()
            && equation.binders.is_empty()
            && let [alternative] = equation.guarded_expression.alternatives.as_ref()
            && alternative.pattern_guards.is_empty()
            && alternative.where_expression.bindings.chunks.is_empty()
        {
            return Ok(LocalForm::Alias(alternative.where_expression.expression));
        }
        Err(self.unsupported(
            scope,
            UnsupportedState::Construct { construct: "inferred polymorphic local bindings" },
        ))
    }

    fn polymorphic_local_reference(
        &mut self,
        scope: &mut Scope,
        source: lowering::LetBindingNameGroupId,
        instantiations: &Substitution,
        dictionaries: Vec<Dictionary>,
    ) -> GoResult<Expression> {
        let module = Arc::clone(&scope.module);
        let declaration = &module.checked.tree[scope.polymorphic_locals[&source].declaration];
        let requested =
            self.abstraction_types(scope, &declaration.value.abstractions, instantiations)?;
        let mut substitution = scope.substitution.clone();
        substitution.extend(instantiations.iter().map(|(&name, &type_id)| (name, type_id)));
        let requested_monotype =
            self.declared_monotype(scope, declaration.type_id, &substitution)?;
        let types = self.terminate_local_growth(&scope.polymorphic_locals[&source], &requested);
        for (name, (&requested, &terminated)) in self
            .abstraction_names(&declaration.value.abstractions)
            .into_iter()
            .zip(requested.iter().zip(types.iter()))
        {
            if requested != terminated {
                substitution.insert(name, terminated);
            }
        }
        let types: Arc<[TypeId]> = Arc::from(types);
        let (dictionaries, runtime_values) = self::runtime::detach_runtime_values(&dictionaries);
        let dictionaries: Arc<[Dictionary]> = Arc::from(dictionaries);
        let canonical = self.types_without_causes(&types);
        let existing =
            scope.polymorphic_locals[&source].specializations.iter().find(|specialization| {
                self.types_without_causes(&specialization.types) == canonical
                    && specialization.dictionaries == dictionaries
            });
        if let Some(specialization) = existing {
            let local = &specialization.local;
            let expression = Expression::new(ExpressionKind::Local(local.id), local.monotype);
            let expression = self.applied_local(expression, runtime_values);
            return Ok(self.coerce(expression, requested_monotype));
        }
        let mut monotype = self.declared_monotype(scope, declaration.type_id, &substitution)?;
        for value in runtime_values.iter().rev() {
            monotype = self.monotypes.function(value.monotype, monotype);
        }
        let polymorphic = scope
            .polymorphic_locals
            .get_mut(&source)
            .expect("invariant violated: polymorphic local is in scope");
        let local = self.fresh_local(polymorphic.name.clone(), monotype);
        let expression = Expression::new(ExpressionKind::Local(local.id), monotype);
        let requester = polymorphic.active;
        polymorphic.specializations.push(LocalSpecialization {
            types,
            dictionaries,
            local,
            value: None,
            requester,
        });
        let expression = self.applied_local(expression, runtime_values);
        Ok(self.coerce(expression, requested_monotype))
    }

    /// A local specialization applied to the run-time dictionaries it takes first.
    fn applied_local(&mut self, local: Expression, arguments: Vec<Expression>) -> Expression {
        if arguments.is_empty() {
            return local;
        }
        let mut monotype = local.monotype;
        for _ in &arguments {
            monotype = self.monotypes.result_after(monotype, 1);
        }
        let kind = ExpressionKind::Apply { function: Box::new(local), arguments };
        Expression::new(kind, monotype)
    }

    fn terminate_local_growth(
        &self,
        polymorphic: &PolymorphicLocal,
        requested: &[TypeId],
    ) -> Vec<TypeId> {
        let mut types = requested.to_vec();
        let mut ancestor = polymorphic.active;
        while let Some(index) = ancestor {
            let specialization = &polymorphic.specializations[index];
            for (position, &ancestor_type) in specialization.types.iter().enumerate() {
                let Some(&requested) = types.get(position) else { continue };
                if self.context.types.grows(requested, ancestor_type) {
                    types[position] = self.context.types.erased(Erasure::PolymorphicRecursion);
                }
            }
            ancestor = specialization.requester;
        }
        types
    }

    fn abstraction_names(&self, abstractions: &[DeclarationAbstraction]) -> Vec<Name> {
        let names = abstractions.iter().filter_map(|abstraction| match abstraction {
            DeclarationAbstraction::Type { binder, .. } => {
                Some(self.context.queries.lookup_forall_binder(*binder).name)
            }
            _ => None,
        });
        names.collect()
    }

    fn specialize_polymorphic_locals(
        &mut self,
        scope: &mut Scope,
        sources: &[lowering::LetBindingNameGroupId],
    ) -> GoResult<()> {
        let module = Arc::clone(&scope.module);
        loop {
            let pending = sources.iter().find_map(|&source| {
                let specializations = &scope.polymorphic_locals[&source].specializations;
                let index = specializations
                    .iter()
                    .position(|specialization| specialization.value.is_none())?;
                Some((source, index))
            });
            let Some((source, index)) = pending else {
                return Ok(());
            };
            let polymorphic = &scope.polymorphic_locals[&source];
            if polymorphic.specializations.len() > LOCAL_SPECIALIZATION_LIMIT {
                return Err(self.unsupported(
                    scope,
                    UnsupportedState::SpecializationLimit { limit: LOCAL_SPECIALIZATION_LIMIT },
                ));
            }
            let value = &module.checked.tree[polymorphic.declaration].value;
            let specialization = &polymorphic.specializations[index];
            let types = Arc::clone(&specialization.types);
            let dictionaries = Arc::clone(&specialization.dictionaries);
            let substitution = scope.substitution.clone();
            let givens = scope.givens.clone();
            let active = scope
                .polymorphic_locals
                .get_mut(&source)
                .map(|polymorphic| std::mem::replace(&mut polymorphic.active, Some(index)));
            let specialized = self
                .bind_local_runtime_dictionaries(&scope.definition, &dictionaries)
                .and_then(|(dictionaries, parameters)| {
                    self.bind_abstractions(scope, &value.abstractions, &types, &dictionaries)?;
                    let body = self.equations(scope, &value.equations)?;
                    Ok(match parameters.is_empty() {
                        true => body,
                        false => self.lambda(parameters, body),
                    })
                });
            scope.substitution = substitution;
            scope.givens = givens;
            let polymorphic = scope
                .polymorphic_locals
                .get_mut(&source)
                .expect("invariant violated: polymorphic local is in scope");
            polymorphic.active = active.flatten();
            polymorphic.specializations[index].value = Some(specialized?);
        }
    }

    fn specialized_bindings(
        &mut self,
        scope: &mut Scope,
        source: lowering::LetBindingNameGroupId,
    ) -> Vec<Binding> {
        let polymorphic = scope
            .polymorphic_locals
            .get_mut(&source)
            .expect("invariant violated: polymorphic local is in scope");
        let specializations = std::mem::take(&mut polymorphic.specializations);
        let bindings = specializations.into_iter().map(|specialization| Binding {
            local: specialization.local,
            value: specialization
                .value
                .expect("invariant violated: requested local specialization was never produced"),
        });
        bindings.collect()
    }

    /// Recovers, from the type the reference is checked at, the quantifiers
    /// the checker records no instantiation for: those of a result type, and
    /// those of a declaration referenced from its own recursive binding group,
    /// where the reference is monomorphic until the group is generalized.
    /// A reference checked against an unspecialized `forall` (`measure` passed
    /// as `Algebra`, `forall node ops. ...`) is instantiated at the skolems the
    /// checker introduced for its quantifiers. That `forall` is erased, so its
    /// skolems are too, and the reference is specialized at the erased type the
    /// parameter has.
    fn erase_rank_n_skolems(
        &mut self,
        scope: &Scope,
        checked: TypeId,
        instantiations: &mut Substitution,
    ) -> GoResult<()> {
        let checked = self.context.types.substitute(checked, &scope.substitution);
        let checked = crate::monotype::expand_synonyms(&mut self.context, checked)?;
        let checked = self.context.types.strip_annotations(checked);
        if !matches!(self.context.types.lookup(checked), Type::Forall(..)) {
            return Ok(());
        }
        if self.monotypes.scheme_for(&mut self.context, checked)?.is_some() {
            return Ok(());
        }
        let mut skolems = vec![];
        for &argument in instantiations.values() {
            self.context.types.rigid_names(argument, &mut skolems);
        }
        let accumulator = match rank_n_scheme(&mut self.context, checked)? {
            Some(scheme) => self.monotypes.schemes.accumulator(&scheme.key),
            None => None,
        };
        let erased = accumulator.unwrap_or_else(|| self.context.types.erased(Erasure::RankN));
        let skolems: Substitution = skolems
            .into_iter()
            .filter(|name| !scope.substitution.contains_key(name))
            .filter(|&name| self.context.types.name_erasure(name).is_none())
            .filter(|&name| !self.context.types.is_cons_list_name(name))
            .map(|name| (name, erased))
            .collect();
        for argument in instantiations.values_mut() {
            *argument = self.context.types.substitute(*argument, &skolems);
        }
        Ok(())
    }

    fn recover_unrecorded_instantiations(
        &mut self,
        scope: &Scope,
        checked: TypeId,
        file_id: FileId,
        term: TermItemId,
        instantiations: &mut Substitution,
    ) -> GoResult<()> {
        let module = self.context.module(file_id)?;
        let Some(declared) = module.checked.lookup_term_item_type(term) else {
            return Ok(());
        };
        let mut uninstantiated = vec![];
        let declared = self.outer_body(declared, &mut uninstantiated);
        let declared = self.strip_instantiated_result_quantifiers(declared, instantiations)?;
        let declared = self.context.types.substitute(declared, instantiations);
        let pattern = self.strip_inner_quantifiers(declared, &mut uninstantiated)?;
        uninstantiated.retain(|name| !instantiations.contains_key(name));
        if uninstantiated.is_empty() {
            return Ok(());
        }
        let checked = self.context.types.substitute(checked, &scope.substitution);
        let checked = self.strip_inner_quantifiers(checked, &mut vec![])?;
        let mut bindings = Substitution::default();
        if self.context.types.match_type(pattern, checked, &uninstantiated, &mut bindings) {
            instantiations.extend(bindings);
        }
        Ok(())
    }

    fn outer_body(&self, mut current: TypeId, names: &mut Vec<Name>) -> TypeId {
        loop {
            let (bound, inner) = self.context.types.peel_quantifiers(current);
            let (constraints, inner) = self.context.types.peel_constraints(inner);
            current = inner;
            names.extend(bound.iter().copied());
            if bound.is_empty() && constraints.is_empty() {
                return current;
            }
        }
    }

    fn strip_inner_quantifiers(
        &mut self,
        type_id: TypeId,
        names: &mut Vec<Name>,
    ) -> GoResult<TypeId> {
        let type_id = crate::monotype::expand_synonyms(&mut self.context, type_id)?;
        let (bound, body) = self.context.types.peel_quantifiers(type_id);
        names.extend(bound);
        let Some((argument, result)) = self.context.types.function_parts(body) else {
            return Ok(body);
        };
        let result = self.strip_inner_quantifiers(result, names)?;
        Ok(self.context.queries.intern_type(Type::Function(argument, result)))
    }

    /// The type of a reference after the checker's implicit instantiation: the
    /// declared type with its quantifiers replaced and its constraints discharged.
    fn instantiated_monotype(
        &mut self,
        scope: &Scope,
        node: tree::ExpressionId,
        file_id: FileId,
        term: TermItemId,
        instantiations: &Substitution,
    ) -> GoResult<MonotypeId> {
        let module = self.context.module(file_id)?;
        let declared = module
            .checked
            .lookup_term_item_type(term)
            .unwrap_or(scope.module.checked.tree[node].type_id);
        self.declared_monotype(scope, declared, instantiations)
    }

    fn declared_monotype(
        &mut self,
        scope: &Scope,
        declared: TypeId,
        instantiations: &Substitution,
    ) -> GoResult<MonotypeId> {
        let closed = self.instantiated_type(scope, declared, instantiations)?;
        self.closed_monotype(scope, closed)
    }

    fn instantiated_type(
        &mut self,
        scope: &Scope,
        declared: TypeId,
        instantiations: &Substitution,
    ) -> GoResult<TypeId> {
        let mut current = crate::monotype::expand_synonyms(&mut self.context, declared)?;
        let mut names = vec![];
        loop {
            let (bound, inner) = self.context.types.peel_quantifiers(current);
            let (constraints, inner) = self.context.types.peel_constraints(inner);
            names.extend(bound);
            current = crate::monotype::expand_synonyms(&mut self.context, inner)?;
            if constraints.is_empty()
                && !matches!(self.context.types.lookup(current), Type::Forall(..))
            {
                break;
            }
        }
        for name in &names {
            if !instantiations.contains_key(name) {
                let variable = format!("{name:?}");
                return Err(
                    self.unsupported(scope, UnsupportedState::UninstantiatedVariable { variable })
                );
            }
        }
        let current = self.strip_instantiated_result_quantifiers(current, instantiations)?;
        Ok(self.context.types.substitute(current, instantiations))
    }

    /// Where a reference is used the checker also instantiates the quantifiers
    /// in its result positions (`Free f ~> m` after `foldFree`'s argument). A
    /// quantifier in an argument position is rank-N and stays, even when a
    /// synonym gave it the same name as an instantiated one.
    fn strip_instantiated_result_quantifiers(
        &mut self,
        type_id: TypeId,
        instantiations: &Substitution,
    ) -> GoResult<TypeId> {
        let mut body = crate::monotype::expand_synonyms(&mut self.context, type_id)?;
        loop {
            match self.context.types.lookup(self.context.types.strip_annotations(body)).clone() {
                Type::Forall(binder, inner) => {
                    let binder = self.context.queries.lookup_forall_binder(binder);
                    if !instantiations.contains_key(&binder.name) {
                        return Ok(body);
                    }
                    body = crate::monotype::expand_synonyms(&mut self.context, inner)?;
                }
                Type::Constrained(_, inner) => body = inner,
                _ => break,
            }
        }
        let Some((argument, result)) = self.context.types.function_parts(body) else {
            return Ok(body);
        };
        let stripped = self.strip_instantiated_result_quantifiers(result, instantiations)?;
        if stripped == result {
            return Ok(body);
        }
        Ok(self.context.queries.intern_type(Type::Function(argument, stripped)))
    }

    fn global_reference(
        &mut self,
        scope: &mut Scope,
        file_id: FileId,
        term: TermItemId,
        instantiations: &Substitution,
        dictionaries: Vec<Dictionary>,
        monotype: MonotypeId,
    ) -> GoResult<Expression> {
        let module = self.context.module(file_id)?;
        let name = module.indexed.items[term].name.clone().unwrap_or_default();
        let is_constructor =
            matches!(module.indexed.items[term].kind, IndexedTermItemKind::Constructor { .. });
        let is_member =
            matches!(module.indexed.items[term].kind, IndexedTermItemKind::ClassMember { .. });
        let is_foreign =
            matches!(module.indexed.items[term].kind, IndexedTermItemKind::Foreign { .. });
        match () {
            () if is_foreign
                && dictionaries.iter().any(|dictionary| *dictionary != Dictionary::Trivial) =>
            {
                Err(self.unsupported(
                    scope,
                    UnsupportedState::Construct { construct: "foreign imports with constraints" },
                ))
            }
            () if is_foreign => {
                if let Some(foreign) = foreign::foreign_import(&module.name, &name) {
                    if let Foreign::UnsafeCoerce = foreign {
                        self.link_coerced_rank_n(scope, file_id, term, instantiations)?;
                        if let Some((from, to)) = self.monotypes.function_parts(monotype) {
                            self.note_crossings(from, to);
                        }
                    }
                    let foreign = self.with_callback_arities(file_id, term, foreign)?;
                    let accumulator = match foreign {
                        Foreign::Call { boundary, .. } => boundary.accumulator,
                        _ => None,
                    };
                    let monotype = match accumulator {
                        Some(fold) => {
                            self.accumulated_monotype(scope, file_id, term, instantiations, fold)?
                        }
                        None => monotype,
                    };
                    return Ok(self.foreign(foreign, monotype));
                }
                if self.foreign_packages.provides(&module.name) {
                    let foreign =
                        self.project_foreign(scope, file_id, term, instantiations, monotype)?;
                    let foreign = foreign.interned();
                    return Ok(self.foreign(foreign, monotype));
                }
                let name = format!("{}.{name}", module.name);
                Err(self.unsupported(scope, UnsupportedState::UnknownForeign { name }))
            }
            () if is_constructor => self.constructor(scope, file_id, term, monotype),
            () if is_member => {
                let mut dictionaries = dictionaries.into_iter();
                let Some(dictionary) = dictionaries.next() else {
                    return Err(self.unsupported(scope, UnsupportedState::UnboundEvidence));
                };
                let rest: Vec<Dictionary> = dictionaries.collect();
                self.member_reference(
                    scope,
                    (file_id, term),
                    dictionary,
                    instantiations,
                    rest,
                    monotype,
                )
            }
            () => {
                let instance_names = self.dictionary_names(&dictionaries)?;
                let instances: Vec<&str> = instance_names.iter().map(SmolStr::as_str).collect();
                if let Some(foreign) = foreign::intrinsic(&module.name, &name, &instances) {
                    let foreign = self.with_callback_arities(file_id, term, foreign)?;
                    return Ok(self.foreign(foreign, monotype));
                }
                let declaration =
                    module.checked.tree.lookup_term(term).ok_or_else(|| {
                        self.unsupported(scope, UnsupportedState::MissingDeclaration)
                    })?;
                let TermDeclarationKind::Value(value) = &module.checked.tree[declaration].kind
                else {
                    return Err(self.unsupported(scope, UnsupportedState::MissingDeclaration));
                };
                let types = self.abstraction_types(scope, &value.abstractions, instantiations)?;
                if let Some(primitive) = crate::primitives::known(&module.name, &name)
                    && let Some(expression) = self.primitive(
                        scope,
                        primitive,
                        (file_id, term),
                        &types,
                        instantiations,
                        monotype,
                    )?
                {
                    return Ok(expression);
                }
                let name = self.specialized_name(name, &types)?;
                let key = SpecializationKey {
                    definition: Definition::Value { file_id, term },
                    types: Arc::from(types),
                    dictionaries: Arc::from(dictionaries),
                };
                self.request_reference(scope, key, name, monotype)
            }
        }
    }

    fn member_reference(
        &mut self,
        scope: &mut Scope,
        member: (FileId, TermItemId),
        dictionary: Dictionary,
        instantiations: &Substitution,
        dictionaries: Vec<Dictionary>,
        monotype: MonotypeId,
    ) -> GoResult<Expression> {
        let member_module = self.context.module(member.0)?;
        let member_name = member_module.indexed.items[member.1].name.clone().unwrap_or_default();
        let instance = match dictionary {
            Dictionary::Instance(instance) => instance,
            Dictionary::Symbol(symbol) => {
                let symbol = ExpressionKind::Literal(Literal::String(symbol.to_string()));
                return Ok(self.constant_function(symbol, monotype));
            }
            Dictionary::Reflectable(reflected) => {
                let literal = match reflected {
                    Reflected::Integer(value) => Literal::Int(i64::from(value)),
                    Reflected::String(value) => Literal::String(value.to_string()),
                    Reflected::Boolean(value) => Literal::Boolean(value),
                    Reflected::Ordering(name) => {
                        let constructed = self.reflected_constructor(scope, &name, monotype)?;
                        return Ok(self.constant_function(constructed, monotype));
                    }
                    Reflected::Reified => {
                        return Err(self.unsupported(scope, UnsupportedState::UnboundEvidence));
                    }
                };
                return Ok(self.constant_function(ExpressionKind::Literal(literal), monotype));
            }
            Dictionary::Trivial => {
                return Err(self.unsupported(
                    scope,
                    UnsupportedState::MissingInstanceMember { member: member_name.to_string() },
                ));
            }
            Dictionary::Runtime(runtime) => {
                return self.runtime_member(scope, runtime, member_name, monotype);
            }
        };
        let mut instance_names = vec![self.instance_name(instance.origin)?];
        instance_names.extend(self.dictionary_names(&dictionaries)?);
        let instances: Vec<&str> = instance_names.iter().map(SmolStr::as_str).collect();
        if let Some(foreign) = foreign::intrinsic(&member_module.name, &member_name, &instances) {
            return Ok(self.foreign(foreign, monotype));
        }
        let (module, declaration) = self.instance_declaration(instance.origin)?;
        let TermDeclarationKind::Instance(declared) = &module.checked.tree[declaration].kind else {
            return Err(self.unsupported(scope, UnsupportedState::MissingDeclaration));
        };
        let tree::InstanceImplementation::Members(members) = &declared.implementation else {
            return Err(self.unsupported(scope, UnsupportedState::MissingDeclaration));
        };
        let Some(implementation) =
            members.iter().find(|implementation| implementation.resolution == member)
        else {
            return Err(self.unsupported(
                scope,
                UnsupportedState::MissingInstanceMember { member: member_name.to_string() },
            ));
        };
        let types = self.abstraction_types(scope, &implementation.abstractions, instantiations)?;
        let name = self.specialized_name(member_name, &instance.types)?;
        let key = SpecializationKey {
            definition: Definition::Member { dictionary: instance, member },
            types: Arc::from(types),
            dictionaries: Arc::from(dictionaries),
        };
        self.request_reference(scope, key, name, monotype)
    }

    /// A reflected type-level `Ordering` is the term-level constructor of the same name.
    fn reflected_constructor(
        &mut self,
        scope: &Scope,
        name: &str,
        monotype: MonotypeId,
    ) -> GoResult<ExpressionKind> {
        let result = self.monotypes.result_after(monotype, 1);
        let Monotype::Data(data) = self.monotypes.get(result).clone() else {
            let rendered = format!("reflected {name}");
            return Err(self.unsupported(scope, UnsupportedState::OpenType { rendered }));
        };
        let constructors = self.monotypes.constructors(&mut self.context, &data);
        let constructors = constructors.map_err(|failure| failure.at(&scope.definition))?;
        let Some(index) = constructors.iter().position(|constructor| constructor.name == name)
        else {
            return Err(self.unsupported(scope, UnsupportedState::MissingDeclaration));
        };
        Ok(ExpressionKind::Construct { data, constructor: index, arguments: vec![] })
    }

    /// The member of a compiler-solved class: a constant behind its `Proxy`.
    fn constant_function(&mut self, constant: ExpressionKind, monotype: MonotypeId) -> Expression {
        let Some((argument, result)) = self.monotypes.function_parts(monotype) else {
            return Expression::new(constant, monotype);
        };
        let parameter = self.fresh_local(SmolStr::new_static("proxy"), argument);
        let body = Expression::new(constant, result);
        self.lambda(vec![parameter], body)
    }

    fn abstraction_types(
        &mut self,
        scope: &Scope,
        abstractions: &[DeclarationAbstraction],
        instantiations: &Substitution,
    ) -> GoResult<Vec<TypeId>> {
        let mut types = vec![];
        for abstraction in abstractions {
            match abstraction {
                DeclarationAbstraction::Type { binder, .. } => {
                    let binder = self.context.queries.lookup_forall_binder(*binder);
                    let Some(&argument) = instantiations.get(&binder.name) else {
                        let variable = match scope.module.checked.lookup_name(binder.name) {
                            Some(text) => self.context.queries.lookup_smol_str(text).to_string(),
                            None => binder.name.as_text().to_string(),
                        };
                        return Err(self.unsupported(
                            scope,
                            UnsupportedState::UninstantiatedVariable { variable },
                        ));
                    };
                    types.push(argument);
                }
                DeclarationAbstraction::Evidence { .. } | DeclarationAbstraction::Argument => {}
            }
        }
        Ok(types)
    }

    /// Records how many arrows each parameter of a generic helper declares; see
    /// `Boundary::callback_arities`. Only pure helpers (`Call`) take
    /// uniformly represented callbacks.
    fn with_callback_arities(
        &mut self,
        file_id: FileId,
        term: TermItemId,
        foreign: &'static Foreign,
    ) -> GoResult<&'static Foreign> {
        let boundary = match foreign {
            Foreign::Call { boundary, .. } | Foreign::Perform { boundary, .. } => *boundary,
            _ => return Ok(foreign),
        };
        let declared = match self.callback_arities.get(&(file_id, term)) {
            Some(&declared) => declared,
            None => {
                let module = self.context.module(file_id)?;
                let Some(signature) = module.checked.lookup_term_item_type(term) else {
                    return Ok(foreign);
                };
                let signature = crate::monotype::expand_synonyms(&mut self.context, signature)?;
                let (_, mut current) = self.context.types.peel_quantifiers(signature);
                let mut arities = vec![];
                let mut parameters = vec![];
                while let Some((parameter, result)) = self.context.types.function_parts(current) {
                    let (_, parameter) = self.context.types.peel_quantifiers(parameter);
                    let mut arrows = 0;
                    let mut inner = parameter;
                    while let Some((_, result)) = self.context.types.function_parts(inner) {
                        arrows += 1;
                        inner = result;
                    }
                    arities.push(arrows);
                    parameters.push(self.spelled(parameter)?);
                    current = result;
                }
                if parameters.is_empty() {
                    let (parts, result) = self.uncurried_parts(current)?;
                    arities = parts.iter().map(Spelled::arrows).collect();
                    parameters = parts;
                    current = result;
                }
                let result = self.spelled(current)?;
                let arities: &'static [usize] = Box::leak(arities.into_boxed_slice());
                let signature: &'static Signature =
                    Box::leak(Box::new(Signature { parameters, result }));
                self.callback_arities.insert((file_id, term), (arities, signature));
                (arities, signature)
            }
        };
        let (arities, signature) = declared;
        let boundary =
            Boundary { callback_arities: arities, signature: Some(signature), ..boundary };
        let learned = match *foreign {
            Foreign::Call { function, arity, .. } => Foreign::Call { function, arity, boundary },
            Foreign::Perform { function, arity, .. } => {
                Foreign::Perform { function, arity, boundary }
            }
            _ => unreachable!(),
        };
        Ok(learned.interned())
    }

    fn accumulated_monotype(
        &mut self,
        scope: &Scope,
        file_id: FileId,
        term: TermItemId,
        instantiations: &Substitution,
        accumulator: Accumulator,
    ) -> GoResult<MonotypeId> {
        let module = self.context.module(file_id)?;
        let declared = module
            .checked
            .lookup_term_item_type(term)
            .ok_or_else(|| self.unsupported(scope, UnsupportedState::MissingDeclaration))?;
        let declared = crate::monotype::expand_synonyms(&mut self.context, declared)?;
        let (names, body) = self.context.types.peel_quantifiers(declared);
        let element = names.get(accumulator.element).and_then(|name| instantiations.get(name));
        let Some(&element) = element else {
            let variable = format!("accumulator element {}", accumulator.element);
            let state = UnsupportedState::UninstantiatedVariable { variable };
            return Err(self.unsupported(scope, state));
        };
        let cons_list = self.context.types.cons_list();
        let cons_list = self.context.queries.intern_type(Type::Application(cons_list, element));
        let (head, arguments) = self.context.types.spine(body);
        let parameter = match self.is_uncurried_function(head)? {
            true => arguments.get(accumulator.parameter).copied(),
            false => {
                let mut current = body;
                for _ in 0..accumulator.parameter {
                    let parts = self.context.types.function_parts(current);
                    current = parts.map_or(current, |(_, rest)| rest);
                }
                self.context.types.function_parts(current).map(|(parameter, _)| parameter)
            }
        };
        let Some(parameter) = parameter else {
            return Err(self.unsupported(scope, UnsupportedState::MissingDeclaration));
        };
        let parameter = self.context.types.substitute(parameter, instantiations);
        if let Some(scheme) = rank_n_scheme(&mut self.context, parameter)?
            && self.monotypes.schemes.add_accumulator(scheme.key, cons_list)
        {
            self.grown = true;
        }
        self.declared_monotype(scope, declared, instantiations)
    }

    fn is_uncurried_function(&mut self, head: TypeId) -> GoResult<bool> {
        let Type::Constructor(file_id, item) = self.context.types.lookup(head).clone() else {
            return Ok(false);
        };
        let module = self.context.module(file_id)?;
        let name = module.indexed.items[item].name.clone().unwrap_or_default();
        Ok(module.name == "Data.Function.Uncurried"
            && name.strip_prefix("Fn").is_some_and(|count| count.parse::<usize>().is_ok()))
    }

    fn uncurried_parts(&mut self, type_id: TypeId) -> GoResult<(Vec<Spelled>, TypeId)> {
        let (head, arguments) = self.context.types.spine(type_id);
        let uncurried = self.is_uncurried_function(head)?;
        let Some((&result, parameters)) = arguments.split_last().filter(|_| uncurried) else {
            return Ok((vec![], type_id));
        };
        let mut spelled = Vec::with_capacity(parameters.len());
        for &parameter in parameters {
            spelled.push(self.spelled(parameter)?);
        }
        Ok((spelled, result))
    }

    fn spelled(&mut self, type_id: TypeId) -> GoResult<Spelled> {
        let (_, type_id) = self.context.types.peel_quantifiers(type_id);
        if let Some((argument, result)) = self.context.types.function_parts(type_id) {
            let argument = self.spelled(argument)?;
            let result = self.spelled(result)?;
            return Ok(Spelled::Function(Box::new(argument), Box::new(result)));
        }
        let (head, arguments) = self.context.types.spine(type_id);
        let Type::Constructor(file_id, item) = self.context.types.lookup(head).clone() else {
            return Ok(Spelled::Opaque);
        };
        let [argument] = arguments[..] else { return Ok(Spelled::Opaque) };
        let module = self.context.module(file_id)?;
        let name = module.indexed.items[item].name.clone().unwrap_or_default();
        Ok(match (module.name.as_str(), name.as_str()) {
            ("Prim", "Array") => Spelled::Array(Box::new(self.spelled(argument)?)),
            ("Effect", "Effect") => Spelled::Effect(Box::new(self.spelled(argument)?)),
            _ => Spelled::Opaque,
        })
    }

    fn project_foreign(
        &mut self,
        scope: &Scope,
        file_id: FileId,
        term: TermItemId,
        instantiations: &Substitution,
        monotype: MonotypeId,
    ) -> GoResult<Foreign> {
        let mut arity = 0;
        let mut current = monotype;
        while let Some((_, result)) = self.monotypes.function_parts(current) {
            arity += 1;
            current = result;
        }
        let effectful = self.monotypes.effect_result(current).is_some();
        // Go has no generic variables: a quantified foreign value is a generic function
        // taking its quantifiers' instantiations in declared order.
        let mut type_arguments = vec![];
        let declared = self.context.module(file_id)?.checked.lookup_term_item_type(term);
        if let Some(declared) = declared.filter(|_| arity == 0) {
            let declared = crate::monotype::expand_synonyms(&mut self.context, declared)?;
            for quantifier in self.context.types.peel_quantifiers(declared).0 {
                let Some(&argument) = instantiations.get(&quantifier) else {
                    let variable = format!("{quantifier:?}");
                    let state = UnsupportedState::UninstantiatedVariable { variable };
                    return Err(self.unsupported(scope, state));
                };
                type_arguments.push(self.closed_monotype(scope, argument)?);
            }
        }
        let type_arguments = Box::leak(type_arguments.into_boxed_slice());
        Ok(Foreign::Project { file_id, term, arity, effectful, type_arguments })
    }

    fn foreign(&mut self, foreign: &'static Foreign, monotype: MonotypeId) -> Expression {
        let arity = foreign.arity();
        if arity == 0 {
            return Expression::new(
                ExpressionKind::Foreign { foreign, arguments: vec![] },
                monotype,
            );
        }
        let mut parameters = Vec::with_capacity(arity);
        let mut current = monotype;
        for _ in 0..arity {
            let (argument, result) = self
                .monotypes
                .function_parts(current)
                .expect("invariant violated: foreign arity exceeds its function type");
            parameters.push(self.fresh_local(self.monotypes.value_name(argument), argument));
            current = result;
        }
        let arguments = parameters.iter().map(Local::expression).collect();
        let body = Expression::new(ExpressionKind::Foreign { foreign, arguments }, current);
        self.lambda(parameters, body)
    }

    fn constructor(
        &mut self,
        scope: &Scope,
        file_id: FileId,
        term: TermItemId,
        monotype: MonotypeId,
    ) -> GoResult<Expression> {
        if self.is_newtype_constructor((file_id, term))? {
            let (argument, _) =
                self.monotypes.function_parts(monotype).unwrap_or((monotype, monotype));
            let result = self.monotypes.result_after(monotype, 1);
            let parameter = self.fresh_local(self.monotypes.value_name(argument), argument);
            let body = Expression::new(ExpressionKind::Local(parameter.id), result);
            return Ok(self.lambda(vec![parameter], body));
        }
        let mut result = monotype;
        while let Some((_, inner)) = self.monotypes.function_parts(result) {
            result = inner;
        }
        let Monotype::Data(data) = self.monotypes.get(result).clone() else {
            return Err(self.unsupported(
                scope,
                UnsupportedState::OpenType { rendered: "constructor".into() },
            ));
        };
        let constructors = self
            .monotypes
            .constructors(&mut self.context, &data)
            .map_err(|failure| failure.at(&scope.definition))?;
        let Some(index) =
            constructors.iter().position(|constructor| constructor.term == Some(term))
        else {
            return Err(self.unsupported(scope, UnsupportedState::MissingDeclaration));
        };
        let fields = constructors[index].fields.clone();
        let parameters: Vec<Local> = fields
            .iter()
            .map(|&field| self.fresh_local(self.monotypes.value_name(field), field))
            .collect();
        let arguments = parameters.iter().map(Local::expression).collect();
        let kind = ExpressionKind::Construct { data, constructor: index, arguments };
        let body = Expression::new(kind, result);
        if parameters.is_empty() {
            return Ok(body);
        }
        Ok(self.lambda(parameters, body))
    }

    fn pattern(&mut self, scope: &mut Scope, binder_id: tree::BinderId) -> GoResult<Pattern> {
        let module = Arc::clone(&scope.module);
        let binder = &module.checked.tree[binder_id];
        let monotype = self.binder_monotype(scope, binder.type_id)?;
        let kind = match &binder.kind {
            tree::BinderKind::Typed { binder, .. } => return self.pattern(scope, *binder),
            tree::BinderKind::Error => {
                return Err(self.unsupported(scope, UnsupportedState::BinderError));
            }
            tree::BinderKind::Integer { value } => {
                PatternKind::Literal(Literal::Int(i64::from(*value)))
            }
            tree::BinderKind::Number { negative, value } => {
                let value = if *negative { format_smolstr!("-{value}") } else { value.clone() };
                PatternKind::Literal(Literal::Number(value))
            }
            tree::BinderKind::Variable => {
                let name = self.binder_name(scope, binder_id);
                let local = self.fresh_local(name, monotype);
                let source = self.checked_binder_source(scope, binder_id);
                scope.locals.insert(source, local.clone());
                self.register_scheme_local(scope, source, binder.type_id)?;
                PatternKind::Variable(local)
            }
            tree::BinderKind::Named { name, binder: inner } => {
                let local = self.fresh_local(name.clone(), monotype);
                let source = self.checked_binder_source(scope, binder_id);
                scope.locals.insert(source, local.clone());
                self.register_scheme_local(scope, source, binder.type_id)?;
                let pattern = self.pattern(scope, *inner)?;
                PatternKind::Named { local, pattern: Box::new(pattern) }
            }
            tree::BinderKind::Wildcard => PatternKind::Wildcard,
            tree::BinderKind::String { value } => {
                PatternKind::Literal(string_literal(value))
            }
            tree::BinderKind::Char { value } => PatternKind::Literal(Literal::Char(*value)),
            tree::BinderKind::Boolean { value } => PatternKind::Literal(Literal::Boolean(*value)),
            tree::BinderKind::Array { elements } => {
                let mut patterns = Vec::with_capacity(elements.len());
                for &element in elements.iter() {
                    patterns.push(self.pattern(scope, element)?);
                }
                PatternKind::Array(patterns)
            }
            tree::BinderKind::Record { fields } => {
                let mut patterns = Vec::with_capacity(fields.len());
                for field in fields.iter() {
                    match field {
                        tree::RecordBinderField::Field { label, binder } => {
                            patterns.push((label.clone(), self.pattern(scope, *binder)?));
                        }
                        tree::RecordBinderField::Pun { label } => {
                            let Some(pun) = self.record_pun_source(scope, binder_id, label) else {
                                return Err(self.unsupported(scope, UnsupportedState::BinderError));
                            };
                            let field_monotype = self.field_monotype(scope, monotype, label)?;
                            let local = self.fresh_local(label.clone(), field_monotype);
                            scope.locals.insert(LocalSource::RecordPun(pun), local.clone());
                            let pattern = Pattern {
                                kind: PatternKind::Variable(local),
                                monotype: field_monotype,
                            };
                            patterns.push((label.clone(), pattern));
                        }
                    }
                }
                PatternKind::Record(patterns)
            }
            tree::BinderKind::Constructor { resolution, arguments } => {
                if self.is_newtype_constructor(*resolution)? {
                    let [argument] = arguments.as_ref() else {
                        return Err(self.unsupported(scope, UnsupportedState::BinderError));
                    };
                    let mut pattern = self.pattern(scope, *argument)?;
                    if let Monotype::Recursive(data) = self.monotypes.get(monotype).clone() {
                        // The wrapped value has the unfolded representation, as the
                        // declared type of a function like `step (ListT m) = m` says.
                        let unfolded = self.monotypes.unfold_in(
                            &mut self.context,
                            &data,
                            &scope.definition,
                        )?;
                        self.adopt_representation(scope, *argument, &mut pattern, unfolded);
                        pattern.monotype = unfolded;
                    } else {
                        if !self.monotypes.same_without_causes(pattern.monotype, monotype)
                            && self.mentions_erased(monotype)
                        {
                            self.adopt_representation(scope, *argument, &mut pattern, monotype);
                        }
                        pattern.monotype = monotype;
                    }
                    return Ok(pattern);
                }
                let Monotype::Data(data) = self.monotypes.get(monotype).clone() else {
                    return Err(self.unsupported(scope, UnsupportedState::BinderError));
                };
                let constructors = self
                    .monotypes
                    .constructors(&mut self.context, &data)
                    .map_err(|failure| failure.at(&scope.definition))?;
                let Some(constructor) = constructors
                    .iter()
                    .position(|constructor| constructor.term == Some(resolution.1))
                else {
                    return Err(self.unsupported(scope, UnsupportedState::BinderError));
                };
                let mut patterns = Vec::with_capacity(arguments.len());
                for &argument in arguments.iter() {
                    patterns.push(self.pattern(scope, argument)?);
                }
                PatternKind::Constructor { data, constructor, arguments: patterns }
            }
        };
        Ok(Pattern { kind, monotype })
    }

    fn adopt_representation(
        &mut self,
        scope: &mut Scope,
        binder: tree::BinderId,
        pattern: &mut Pattern,
        monotype: MonotypeId,
    ) {
        let (binder, _) = self.unwrap_typed(scope, binder);
        let source = self.checked_binder_source(scope, binder);
        if let PatternKind::Variable(local) | PatternKind::Named { local, .. } = &mut pattern.kind {
            local.monotype = monotype;
            scope.locals.insert(source, local.clone());
        }
    }

    /// A binder whose type is quantified, directly or through a synonym such as
    /// profunctor-lenses' `Lens s a`, is instantiated at each of its uses.
    fn register_scheme_local(
        &mut self,
        scope: &mut Scope,
        source: LocalSource,
        type_id: TypeId,
    ) -> GoResult<()> {
        let closed = self.context.types.substitute(type_id, &scope.substitution);
        let (head, _) = self.context.types.spine(closed);
        let closed = match self.context.types.lookup(head) {
            Type::Synonym(..) => crate::monotype::expand_synonyms(&mut self.context, closed)?,
            _ => closed,
        };
        if matches!(
            self.context.types.lookup(self.context.types.strip_annotations(closed)),
            Type::Forall(..)
        ) {
            scope.scheme_locals.insert(source, closed);
        } else {
            scope.scheme_locals.remove(&source);
        }
        Ok(())
    }

    fn binder_name(&self, scope: &Scope, binder_id: tree::BinderId) -> SmolStr {
        let binder = &scope.module.checked.tree[binder_id];
        match binder.source {
            tree::BinderSource::Binder(source) => {
                match scope.module.lowered.tree.get_binder_kind(source) {
                    Some(lowering::BinderKind::Variable { variable: Some(name) }) => name.clone(),
                    Some(lowering::BinderKind::Named { named: Some(name), .. }) => name.clone(),
                    _ => SmolStr::new_static(crate::naming::VALUE),
                }
            }
            tree::BinderSource::Generated { name, .. } => {
                SmolStr::clone(self.context.queries.lookup_smol_str(name))
            }
            _ => SmolStr::new_static(crate::naming::VALUE),
        }
    }

    fn record_pun_source(
        &self,
        scope: &Scope,
        binder_id: tree::BinderId,
        label: &str,
    ) -> Option<lowering::RecordPunId> {
        let tree::BinderSource::Binder(source) = scope.module.checked.tree[binder_id].source else {
            return None;
        };
        let lowering::BinderKind::Record { record } =
            scope.module.lowered.tree.get_binder_kind(source)?
        else {
            return None;
        };
        record.iter().find_map(|field| {
            let lowering::BinderRecordItem::RecordPun { id, name } = field else {
                return None;
            };
            name.as_deref().filter(|name| *name == label).map(|_| *id)
        })
    }

    /// A definition's name followed by the types it is specialized at, which
    /// the emitter spells again once it has named their records.
    fn specialized_name(&mut self, name: SmolStr, types: &[TypeId]) -> GoResult<SmolStr> {
        let mut spelled = name.to_string();
        for &type_id in types {
            self.context.type_suffix(type_id, &mut spelled)?;
        }
        let spelled = SmolStr::from(spelled);
        let spelling = FunctionSpelling::Specialized { name, types: Arc::from(types) };
        self.monotypes.function_spellings.entry(spelled.clone()).or_insert(spelling);
        Ok(spelled)
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
    crate::simplify::for_each_child(expression, &mut |child| {
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
