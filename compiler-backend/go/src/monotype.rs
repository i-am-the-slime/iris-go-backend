use std::sync::Arc;

use building_types::{QueryError, QueryResult};
use checking::TypeId;
use checking::core::{Name, Type};
use files::FileId;
use indexing::{IndexedTypeItemKind, TermItemId, TypeItemId};
use rustc_hash::FxHashMap;
use smol_str::SmolStr;

use crate::context::Context;
use crate::erasure::Erasure;
use crate::error::{GoError, GoResult, UnsupportedState};
use crate::scheme::{ConstrainedScheme, SchemeInstantiations, constrained_scheme, rank_n_scheme};
use crate::types::Substitution;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct MonotypeId(u32);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Monotype {
    Int,
    Number,
    Boolean,
    Char,
    String,
    Unit,
    Array(MonotypeId),
    Record(Arc<[RecordField]>),
    Function(MonotypeId, MonotypeId),
    Effect(MonotypeId),
    Reference(MonotypeId),
    MutableArray(MonotypeId),
    Object(MonotypeId),
    Nullable(MonotypeId),
    Error,
    Opaque,
    Regex,
    Mutex,
    BigInt,
    Lazy(MonotypeId),
    Data(DataType),
    /// A `foreign import data` type that a go-support package or the
    /// project's Go foreign package for its module declares, as a named Go type.
    ForeignData(DataType),
    Recursive(DataType),
    Erased(Erasure),
}

impl Monotype {
    /// The one type a container holds: an array's element, an effect's result.
    pub fn element(&self) -> Option<MonotypeId> {
        match self {
            Monotype::Array(element)
            | Monotype::Effect(element)
            | Monotype::Reference(element)
            | Monotype::MutableArray(element)
            | Monotype::Object(element)
            | Monotype::Nullable(element)
            | Monotype::Lazy(element) => Some(*element),
            _ => None,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct RecordField {
    pub label: SmolStr,
    pub monotype: MonotypeId,
}

/// What stops a type from converting: the checker's queries failing, or a type the backend
/// cannot compile.
#[derive(Debug)]
pub enum Failure {
    Query(QueryError),
    Unsupported(UnsupportedState),
}

pub type Converted<T> = Result<T, Failure>;

/// What converted, or nothing when the backend cannot compile the type.
pub fn supported<T>(converted: Converted<T>) -> QueryResult<Option<T>> {
    match converted {
        Ok(value) => Ok(Some(value)),
        Err(Failure::Unsupported(_)) => Ok(None),
        Err(Failure::Query(error)) => Err(error),
    }
}

impl From<QueryError> for Failure {
    fn from(error: QueryError) -> Failure {
        Failure::Query(error)
    }
}

impl From<UnsupportedState> for Failure {
    fn from(state: UnsupportedState) -> Failure {
        Failure::Unsupported(state)
    }
}

impl Failure {
    /// The error as reported by the emitter, which has no definition to name.
    pub fn in_code_generation(self) -> GoError {
        self.at("code generation")
    }

    /// The error as reported against the definition being compiled.
    pub fn at(self, definition: &str) -> GoError {
        match self {
            Failure::Query(error) => GoError::Query(error),
            Failure::Unsupported(state) => {
                GoError::Unsupported { definition: definition.to_string(), state }
            }
        }
    }
}

/// A data type applied to closed type arguments. Arguments stay checker types rather
/// than monotypes because they may be higher-kinded, as in `Free f a`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct DataType {
    pub file_id: FileId,
    pub item: TypeItemId,
    pub arguments: Arc<[TypeId]>,
}

#[derive(Debug, Clone)]
pub struct DataConstructor {
    pub term: TermItemId,
    pub name: SmolStr,
    pub fields: Vec<MonotypeId>,
    /// One of the fields is a type equality between apart types, as
    /// `IntValue (a ~ Int)` has at `Value String`. No value of the data type
    /// is built with the constructor, so a match on it is unreachable.
    pub refuted: bool,
}

const NEWTYPE_EXPANSION_LIMIT: usize = 64;

#[derive(Default)]
pub struct Monotypes {
    interned: Vec<Monotype>,
    lookup: FxHashMap<Monotype, MonotypeId>,
    converted: FxHashMap<TypeId, MonotypeId>,
    constructors: FxHashMap<DataType, Arc<[DataConstructor]>>,
    used_parameters: FxHashMap<(FileId, TypeItemId), Arc<[bool]>>,
    unfolded: FxHashMap<DataType, MonotypeId>,
    regular: FxHashMap<(FileId, TypeItemId), bool>,
    expanding: Vec<TypeId>,
    /// The newtype each function type is the representation of, or none when
    /// several newtypes share it.
    function_newtypes: FxHashMap<MonotypeId, Option<DataType>>,
    pub schemes: SchemeInstantiations,
    /// Rank-N field types met in this pass that the schemes do not list yet.
    pub new_rank_n_keys: Vec<(crate::scheme::SchemeKey, String)>,
    /// Owners of rank-N fields met with erased types in this pass.
    pub new_erased_owners: Vec<String>,
    /// Rank-N field types met in this pass that an erased owner holds.
    pub new_erased_keys: Vec<crate::scheme::SchemeKey>,
    /// Modules whose foreign imports the project implements in Go.
    pub foreign_modules: Vec<String>,
    /// How the names of specialized and lifted functions were formed, which
    /// travels with the types those names spell.
    pub function_spellings: crate::mono::FunctionSpellings,
    /// The synonyms and newtypes, with their arguments, that each record was
    /// spelled by where a type was converted, in the order met.
    pub record_spellings: FxHashMap<MonotypeId, Vec<(FileId, TypeItemId, Arc<[TypeId]>)>>,
    /// The name of each type constructor met, which names its values.
    pub type_names: FxHashMap<(FileId, TypeItemId), SmolStr>,
    /// The newtypes specialization erased to the types they wrap.
    pub erased_newtypes: Vec<crate::context::ErasedNewtype>,
    /// The records that hold a rank-N value specialized at each of its
    /// instantiations, one field per instantiation.
    instantiated_records: rustc_hash::FxHashSet<MonotypeId>,
}

impl Monotypes {
    pub fn intern(&mut self, monotype: Monotype) -> MonotypeId {
        let monotype = match monotype {
            Monotype::Erased(erasure) => Monotype::Erased(erasure.tracked()),
            monotype => monotype,
        };
        if let Some(&id) = self.lookup.get(&monotype) {
            return id;
        }
        let id = MonotypeId(self.interned.len() as u32);
        self.interned.push(monotype.clone());
        self.lookup.insert(monotype, id);
        id
    }

    /// Lists every interned monotype, for `IRIS_GO_DUMP`.
    pub fn dump(&self) {
        for (index, monotype) in self.interned.iter().enumerate() {
            eprintln!("monotype {index}: {monotype:?}");
        }
    }

    /// Every monotype interned so far.
    pub fn ids(&self) -> impl Iterator<Item = MonotypeId> + use<> {
        (0..self.interned.len() as u32).map(MonotypeId)
    }

    pub fn get(&self, id: MonotypeId) -> &Monotype {
        &self.interned[id.0 as usize]
    }

    /// Whether a record holds a rank-N value, one field per instantiation,
    /// rather than a PureScript record.
    pub fn is_instantiated_record(&self, id: MonotypeId) -> bool {
        self.instantiated_records.contains(&id)
    }

    /// The one newtype whose representation a function type is, as `Lazy Int`
    /// is `Unit -> Int`.
    pub fn function_newtype(&self, id: MonotypeId) -> Option<&DataType> {
        self.function_newtypes.get(&id)?.as_ref()
    }

    pub fn function(&mut self, argument: MonotypeId, result: MonotypeId) -> MonotypeId {
        self.intern(Monotype::Function(argument, result))
    }

    pub fn function_parts(&self, id: MonotypeId) -> Option<(MonotypeId, MonotypeId)> {
        match self.get(id) {
            Monotype::Function(argument, result) => Some((*argument, *result)),
            _ => None,
        }
    }

    pub fn effect_result(&self, id: MonotypeId) -> Option<MonotypeId> {
        match self.get(id) {
            Monotype::Effect(result) => Some(*result),
            _ => None,
        }
    }

    /// Strips `count` arguments off a curried function type.
    pub fn result_after(&self, mut id: MonotypeId, count: usize) -> MonotypeId {
        for _ in 0..count {
            match self.function_parts(id) {
                Some((_, result)) => id = result,
                None => break,
            }
        }
        id
    }

    pub fn monotype<Q>(
        &mut self,
        context: &mut Context<'_, Q>,
        type_id: TypeId,
    ) -> Converted<MonotypeId>
    where
        Q: checking::ExternalQueries,
    {
        self.convert(context, type_id, 0)
    }

    fn convert<Q>(
        &mut self,
        context: &mut Context<'_, Q>,
        type_id: TypeId,
        expansions: usize,
    ) -> Converted<MonotypeId>
    where
        Q: checking::ExternalQueries,
    {
        // Inside a newtype expansion the result depends on the newtypes being
        // expanded, so only conversions outside every expansion are remembered.
        if expansions > 0 || !self.expanding.is_empty() {
            return self.convert_uncached(context, type_id, expansions);
        }
        if let Some(&id) = self.converted.get(&type_id) {
            return Ok(id);
        }
        let converted = self.convert_uncached(context, type_id, expansions);
        if let Ok(id) = converted {
            self.converted.insert(type_id, id);
        }
        converted
    }

    fn convert_uncached<Q>(
        &mut self,
        context: &mut Context<'_, Q>,
        type_id: TypeId,
        expansions: usize,
    ) -> Converted<MonotypeId>
    where
        Q: checking::ExternalQueries,
    {
        if expansions > NEWTYPE_EXPANSION_LIMIT {
            return Err(
                UnsupportedState::Construct { construct: "infinitely nested newtypes" }.into()
            );
        }
        let type_id = context.types.strip_annotations(type_id);
        let monotype = match context.types.lookup(type_id).clone() {
            Type::Function(argument, result) => {
                let argument = self.convert(context, argument, expansions)?;
                let result = self.convert(context, result, expansions)?;
                Monotype::Function(argument, result)
            }
            Type::Forall(..) => match self.scheme_for(context, type_id)? {
                Some(scheme) => return self.convert_scheme(context, &scheme, expansions),
                None => {
                    // Without constraints there is no instantiation to specialize
                    // on yet: the quantified variables are erased.
                    let erasure = match self.schemes.has_grown() {
                        true => match rank_n_scheme(context, type_id)? {
                            Some(scheme) => self.schemes.rank_n_erasure(&scheme.key),
                            None => Erasure::RankN,
                        },
                        false => Erasure::RankN,
                    };
                    let (names, inner) = context.types.peel_quantifiers(type_id);
                    let erased = context.types.erased(erasure);
                    let substitution: crate::types::Substitution =
                        names.into_iter().map(|name| (name, erased)).collect();
                    let inner = context.types.substitute(inner, &substitution);
                    return self.convert(context, inner, expansions);
                }
            },
            Type::Rigid(..) => {
                Monotype::Erased(context.types.erasure(type_id).unwrap_or(Erasure::TypeVariable))
            }
            // The backend's own stand-in for a type nothing constrains, which
            // holds no information.
            Type::Unification(u32::MAX) => Monotype::Unit,
            Type::Unification(_) => Monotype::Erased(Erasure::Unsolved.tracked()),
            Type::Application(..) | Type::Constructor(..) | Type::Synonym(..) => {
                return self.convert_application(context, type_id, expansions);
            }
            Type::Constrained(constraint, inner) => {
                if is_partial(context, constraint)? {
                    return self.convert(context, inner, expansions);
                }
                return Err(UnsupportedState::Construct {
                    construct: "constrained types in argument positions",
                }
                .into());
            }
            Type::Row(_) | Type::Integer(_) | Type::String(..) => {
                return Err(open_type(context, type_id)?);
            }
            Type::Free(_) | Type::Unknown(_) => return Err(open_type(context, type_id)?),
            Type::Kinded(..) | Type::KindApplication(..) | Type::ConstraintOrigin(..) => {
                unreachable!("invariant violated: annotations are stripped before conversion")
            }
        };
        Ok(self.intern(monotype))
    }

    fn convert_application<Q>(
        &mut self,
        context: &mut Context<'_, Q>,
        type_id: TypeId,
        expansions: usize,
    ) -> Converted<MonotypeId>
    where
        Q: checking::ExternalQueries,
    {
        let (head, arguments) = context.types.spine(type_id);
        let (file_id, item) = match context.types.lookup(head).clone() {
            Type::Constructor(file_id, item) => (file_id, item),
            Type::Synonym(file_id, item) => {
                return match expand_synonym(context, file_id, item, &arguments)? {
                    Some(expanded) => {
                        let converted = self.convert(context, expanded, expansions + 1);
                        if let Ok(converted) = converted {
                            self.note_record_spelling(converted, file_id, item, &arguments);
                        }
                        converted
                    }
                    None => Err(UnsupportedState::UnsaturatedType {
                        name: context.type_name(file_id, item)?.to_string(),
                    }
                    .into()),
                };
            }
            Type::Rigid(..) | Type::Unification(_) => {
                let erasure = context.types.erasure(head).unwrap_or(Erasure::VariableApplication);
                return Ok(self.intern(Monotype::Erased(erasure)));
            }
            Type::Function(..) if arguments.is_empty() => {
                return self.convert(context, head, expansions);
            }
            _ => return Err(open_type(context, type_id)?),
        };

        let module = context.module(file_id)?;
        let name = module.indexed.items[item].name.clone().unwrap_or_default();
        self.type_names.entry((file_id, item)).or_insert_with(|| name.clone());
        let unary = |monotypes: &mut Monotypes,
                     context: &mut Context<'_, Q>,
                     argument: Option<&TypeId>|
         -> Converted<MonotypeId> {
            match argument {
                Some(&argument) => monotypes.convert(context, argument, expansions),
                None => Err(UnsupportedState::UnsaturatedType { name: name.to_string() }.into()),
            }
        };

        let monotype = match (module.name.as_str(), name.as_str()) {
            ("Prim", "Int") => Monotype::Int,
            ("Prim", "Number") => Monotype::Number,
            ("Prim", "Boolean") => Monotype::Boolean,
            ("Prim", "Char") => Monotype::Char,
            ("Prim", "String") => Monotype::String,
            ("Prim", "Array") => Monotype::Array(unary(self, context, arguments.first())?),
            ("Prim", "Function") => {
                let [argument, result] = arguments[..] else {
                    return Err(UnsupportedState::UnsaturatedType { name: name.to_string() }.into());
                };
                let function = context.queries.intern_type(Type::Function(argument, result));
                return self.convert(context, function, expansions);
            }
            ("Prim", "Record") => {
                let Some(&row) = arguments.first() else {
                    return Err(UnsupportedState::UnsaturatedType { name: name.to_string() }.into());
                };
                return self.convert_record(context, row, expansions);
            }
            ("Data.Unit", "Unit") => Monotype::Unit,
            ("Data.Functor.Variant", "VariantF" | "VariantFRep")
                if arguments.iter().any(|&argument| context.types.erasure(argument).is_none()) =>
            {
                let Some(representation) =
                    module.indexed.items.iter_types().find_map(|(item, indexed)| {
                        (indexed.name.as_deref() == Some("VariantFRep")).then_some(item)
                    })
                else {
                    return Err(open_type(context, type_id)?);
                };
                let erased = context.types.erased(Erasure::VariantRow);
                let representation =
                    context.queries.intern_type(Type::Constructor(file_id, representation));
                let representation =
                    context.queries.intern_type(Type::Application(representation, erased));
                let representation =
                    context.queries.intern_type(Type::Application(representation, erased));
                return self.convert(context, representation, expansions);
            }
            // `Variant` is `foreign import data`, built and taken apart through
            // `unsafeCoerce` to `VariantRep`, whose payload type depends on the
            // label at run time.
            ("Data.Variant", "Variant") => {
                let Some(internal) = context.queries.module_file("Data.Variant.Internal") else {
                    return Err(open_type(context, type_id)?);
                };
                let Some(representation) =
                    context.module(internal)?.indexed.items.iter_types().find_map(
                        |(item, indexed)| {
                            (indexed.name.as_deref() == Some("VariantRep")).then_some(item)
                        },
                    )
                else {
                    return Err(open_type(context, type_id)?);
                };
                let erased = context.types.erased(Erasure::VariantRow);
                let representation =
                    context.queries.intern_type(Type::Constructor(internal, representation));
                let representation =
                    context.queries.intern_type(Type::Application(representation, erased));
                return self.convert(context, representation, expansions);
            }
            ("Data.Exists", "Exists") => Monotype::Erased(Erasure::Existential),
            // A payload that `Data.Variant`'s `Eq`, `Ord`, `Show` and `Enum`
            // instances pass to the label's own instance, the same erased value
            // `VariantRep` holds.
            ("Data.Variant.Internal", "VariantCase")
            | ("Data.Variant.Internal", "VariantFCase") => Monotype::Erased(Erasure::VariantRow),
            ("Data.Function.Uncurried", name) if name.starts_with("Fn") => {
                let Some((&result, parameters)) = arguments.split_last() else {
                    return Err(UnsupportedState::UnsaturatedType { name: name.to_string() }.into());
                };
                let mut curried = result;
                for &parameter in parameters.iter().rev() {
                    curried = context.queries.intern_type(Type::Function(parameter, curried));
                }
                if parameters.is_empty() {
                    let unit = context.queries.intern_type(Type::Unification(u32::MAX));
                    curried = context.queries.intern_type(Type::Function(unit, curried));
                }
                return self.convert(context, curried, expansions);
            }
            ("Effect.Uncurried", name) if name.starts_with("EffectFn") => {
                let Some((&result, parameters)) = arguments.split_last() else {
                    return Err(UnsupportedState::UnsaturatedType { name: name.to_string() }.into());
                };
                let result = self.convert(context, result, expansions)?;
                let result = self.intern(Monotype::Effect(result));
                return self.curried_function(context, parameters, result, expansions);
            }
            ("Control.Monad.ST.Uncurried", name) if name.starts_with("STFn") => {
                let [parameters @ .., _, result] = &arguments[..] else {
                    return Err(UnsupportedState::UnsaturatedType { name: name.to_string() }.into());
                };
                let result = self.convert(context, *result, expansions)?;
                let result = self.intern(Monotype::Effect(result));
                return self.curried_function(context, parameters, result, expansions);
            }
            ("Effect", "Effect") | ("Effect.Aff", "Aff" | "ParAff") => {
                Monotype::Effect(unary(self, context, arguments.first())?)
            }
            ("Control.Monad.ST.Internal", "ST") => {
                Monotype::Effect(unary(self, context, arguments.get(1))?)
            }
            ("Effect.Ref", "Ref") => Monotype::Reference(unary(self, context, arguments.first())?),
            ("Data.Array.ST", "STArray") => {
                Monotype::MutableArray(unary(self, context, arguments.get(1))?)
            }
            // yoga-om's ParallelError is a JavaScript Error subclass that
            // `parallelErrorToError` coerces to Error; go-support keeps its
            // payload in the Error itself.
            ("Effect.Exception", "Error") | ("Yoga.Om.Error", "ParallelError") => Monotype::Error,
            ("Data.String.Regex", "Regex") => Monotype::Regex,
            ("Effect.Synchronized", "Mutex") => Monotype::Mutex,
            ("JS.BigInt", "BigInt") | ("Data.BigInt", "BigInt") => Monotype::BigInt,
            ("Data.Lazy", "Lazy") => Monotype::Lazy(unary(self, context, arguments.first())?),
            ("Promise.Internal", "Promise")
            | ("Promise.Rejection", "Rejection")
            | ("Foreign", "Foreign") => Monotype::Opaque,
            ("Data.Nullable", "Nullable") => {
                Monotype::Nullable(unary(self, context, arguments.first())?)
            }
            ("Foreign.Object", "Object") => {
                Monotype::Object(unary(self, context, arguments.first())?)
            }
            ("Foreign.Object.ST", "STObject") => {
                Monotype::Object(unary(self, context, arguments.get(1))?)
            }
            ("Control.Monad.ST.Internal", "STRef") => {
                Monotype::Reference(unary(self, context, arguments.get(1))?)
            }
            _ => match &module.indexed.items[item].kind {
                IndexedTypeItemKind::Newtype { constructors, .. } => {
                    let Some(&constructor) = constructors.first() else {
                        return Err(open_type(context, type_id)?);
                    };
                    if is_recursive_newtype(context, file_id, item)? {
                        let mut canonical = Vec::with_capacity(arguments.len());
                        for argument in arguments {
                            canonical.push(erase_newtypes(
                                context,
                                argument,
                                expansions,
                                &mut vec![],
                            )?);
                        }
                        let data = DataType { file_id, item, arguments: Arc::from(canonical) };
                        return Ok(self.intern(Monotype::Recursive(data)));
                    }
                    if self.expanding.contains(&type_id) {
                        return Ok(self.intern(Monotype::Erased(Erasure::NewtypeCycle)));
                    }
                    let Some(underlying) =
                        newtype_underlying(context, file_id, constructor, type_id)?
                    else {
                        return Err(open_type(context, type_id)?);
                    };
                    let owner = format!("{}.{name}", module.name);
                    self.note_rank_n_field(context, underlying, &owner)?;
                    self.expanding.push(type_id);
                    let converted = self.convert(context, underlying, expansions + 1);
                    self.expanding.pop();
                    if let Ok(converted) = converted {
                        self.note_record_spelling(converted, file_id, item, &arguments);
                    }
                    if let Ok(converted) = converted
                        && let Monotype::Function(..) = self.get(converted)
                    {
                        let newtype = DataType { file_id, item, arguments: Arc::from(arguments) };
                        self.function_newtypes
                            .entry(converted)
                            .and_modify(|known| {
                                if known.as_ref().is_some_and(|known| {
                                    (known.file_id, known.item) != (file_id, item)
                                }) {
                                    *known = None;
                                }
                            })
                            .or_insert(Some(newtype));
                    }
                    return converted;
                }
                // A data type without constructors that the project's Go foreign
                // package for its module declares, as for `foreign import data`
                // (hyrule's `ObjHack`).
                IndexedTypeItemKind::Data { constructors, .. }
                    if constructors.is_empty()
                        && self.foreign_modules.iter().any(|provided| *provided == module.name) =>
                {
                    let arguments = erased_newtypes(context, arguments, expansions)?;
                    Monotype::ForeignData(DataType { file_id, item, arguments })
                }
                IndexedTypeItemKind::Data { constructors, .. } if constructors.is_empty() => {
                    Monotype::Erased(Erasure::EmptyData)
                }
                IndexedTypeItemKind::Data { .. } => {
                    let regular = self.is_regular(context, file_id, item)?;
                    let arguments = if regular {
                        erased_newtypes(context, arguments, expansions)?
                    } else {
                        arguments.iter().map(|_| context.types.erased(Erasure::NonRegular)).collect()
                    };
                    Monotype::Data(DataType { file_id, item, arguments })
                }
                _ if crate::foreign::is_opaque_foreign_data(&module.name, &name) => {
                    Monotype::Opaque
                }
                _ if crate::foreign::support_data(&module.name, &name).is_some()
                    || self.foreign_modules.iter().any(|provided| *provided == module.name) =>
                {
                    let arguments = erased_newtypes(context, arguments, expansions)?;
                    Monotype::ForeignData(DataType { file_id, item, arguments })
                }
                _ => {
                    let name = format!("{}.{name}", module.name);
                    return Err(UnsupportedState::ForeignData { name }.into());
                }
            },
        };
        Ok(self.intern(monotype))
    }

    fn curried_function<Q>(
        &mut self,
        context: &mut Context<'_, Q>,
        parameters: &[TypeId],
        result: MonotypeId,
        expansions: usize,
    ) -> Converted<MonotypeId>
    where
        Q: checking::ExternalQueries,
    {
        let mut curried = result;
        for &parameter in parameters.iter().rev() {
            let parameter = self.convert(context, parameter, expansions)?;
            curried = self.function(parameter, curried);
        }
        Ok(curried)
    }

    /// The scheme a quantified type is specialized by: its constraints, or for
    /// an unconstrained `forall` its body, when some newtype or constructor
    /// field has that type and its representation depends on the quantified
    /// variables (see `note_rank_n_field`). Other foralls are erased.
    pub fn scheme_for<Q>(
        &mut self,
        context: &mut Context<'_, Q>,
        type_id: TypeId,
    ) -> QueryResult<Option<ConstrainedScheme>>
    where
        Q: checking::ExternalQueries,
    {
        if let Some(scheme) = constrained_scheme(context, type_id)? {
            return Ok(Some(scheme));
        }
        let Some(scheme) = rank_n_scheme(context, type_id)? else { return Ok(None) };
        if !self.schemes.is_rank_n(&scheme.key) {
            return Ok(None);
        }
        Ok(Some(scheme))
    }

    pub fn rank_n_key<Q>(
        &mut self,
        context: &mut Context<'_, Q>,
        type_id: TypeId,
    ) -> QueryResult<Option<crate::scheme::SchemeKey>>
    where
        Q: checking::ExternalQueries,
    {
        let mut current = type_id;
        for _ in 0..NEWTYPE_EXPANSION_LIMIT {
            let expanded = expand_synonyms(context, current)?;
            current = context.types.strip_annotations(expanded);
            if let Type::Forall(..) = context.types.lookup(current) {
                let scheme = self.scheme_for(context, current)?;
                return Ok(scheme.filter(|scheme| scheme.constraints.is_empty()).map(|s| s.key));
            }
            let (head, _) = context.types.spine(current);
            let Type::Constructor(file_id, item) = context.types.lookup(head).clone() else {
                return Ok(None);
            };
            let module = context.module(file_id)?;
            let IndexedTypeItemKind::Newtype { constructors, .. } =
                &module.indexed.items[item].kind
            else {
                return Ok(None);
            };
            let Some(&constructor) = constructors.first() else { return Ok(None) };
            if is_recursive_newtype(context, file_id, item)? {
                return Ok(None);
            }
            let Some(underlying) = newtype_underlying(context, file_id, constructor, current)?
            else {
                return Ok(None);
            };
            current = underlying;
        }
        Ok(None)
    }

    /// A newtype or constructor field whose type is a rank-N `forall` (a CPS
    /// parser's answer type) is specialized per instantiation, and so is every
    /// other occurrence of that same type. A field met for the first time asks
    /// for another specialization pass in which all occurrences agree.
    fn note_rank_n_field<Q>(
        &mut self,
        context: &mut Context<'_, Q>,
        field: TypeId,
        owner: &str,
    ) -> QueryResult<()>
    where
        Q: checking::ExternalQueries,
    {
        if constrained_scheme(context, field)?.is_some() {
            return Ok(());
        }
        let Some(scheme) = rank_n_scheme(context, field)? else { return Ok(()) };
        if self.schemes.is_erased_owner(owner) || self.new_erased_owners.iter().any(|o| o == owner)
        {
            self.note_erased_key(scheme.key);
            return Ok(());
        }
        if context.types.contains_erased(scheme.key.body()) {
            self.new_erased_owners.push(owner.to_string());
            return Ok(());
        }
        if self.schemes.is_rank_n(&scheme.key)
            || self.schemes.is_erased_key(&scheme.key)
            || self.new_rank_n_keys.iter().any(|(key, _)| *key == scheme.key)
        {
            return Ok(());
        }
        let probes = [context.types.erased(Erasure::RankN), self.probe_type(context)];
        let mut converted = Vec::with_capacity(probes.len());
        for probe in probes {
            let types: Vec<TypeId> = scheme.names.iter().map(|_| probe).collect();
            let instantiated = scheme.instantiate(context, &types);
            match supported(self.convert(context, instantiated, 1))? {
                Some(monotype) => converted.push(monotype),
                None => return Ok(()),
            }
        }
        if converted[0] != converted[1] {
            if std::env::var_os("IRIS_GO_DEBUG_RANK_N").is_some() {
                let mut suffix = String::new();
                let _ = context.type_suffix(scheme.body, &mut suffix);
                eprintln!("rank-N field of {owner}: forall {} . {suffix}", scheme.names.len());
            }
            self.new_rank_n_keys.push((scheme.key, owner.to_string()));
        }
        Ok(())
    }

    /// An erased owner's field type stays erased in every other owner too.
    /// Specialized in this pass already, it is erased from the next one on;
    /// otherwise no conversion of this pass depends on it, so it is erased at
    /// once.
    fn note_erased_key(&mut self, key: crate::scheme::SchemeKey) {
        if self.schemes.is_erased_key(&key) || self.new_erased_keys.contains(&key) {
            return;
        }
        let pending = self.new_rank_n_keys.iter().any(|(pending, _)| *pending == key);
        if self.schemes.is_rank_n(&key) || pending {
            self.new_erased_keys.push(key);
        } else {
            self.schemes.erase_key(key);
        }
    }

    /// A closed type no program value can be confused with, to test whether a
    /// representation depends on a variable.
    fn probe_type<Q>(&mut self, context: &mut Context<'_, Q>) -> TypeId
    where
        Q: checking::ExternalQueries,
    {
        context.types.erased(Erasure::Runtime)
    }

    fn convert_scheme<Q>(
        &mut self,
        context: &mut Context<'_, Q>,
        scheme: &ConstrainedScheme,
        expansions: usize,
    ) -> Converted<MonotypeId>
    where
        Q: checking::ExternalQueries,
    {
        let instantiations = self.schemes.get(&scheme.key).to_vec();
        let mut fields = Vec::with_capacity(instantiations.len());
        for instantiation in instantiations {
            let instantiated = scheme.instantiate(context, &instantiation.types);
            let monotype = self.convert(context, instantiated, expansions)?;
            fields.push(RecordField { label: instantiation.label, monotype });
        }
        fields.sort_by(|left, right| left.label.cmp(&right.label));
        let is_rank_n = scheme.constraints.is_empty() && !fields.is_empty();
        let record = self.intern(Monotype::Record(Arc::from(fields)));
        if is_rank_n {
            self.instantiated_records.insert(record);
        }
        Ok(record)
    }

    /// Remembers that a synonym or newtype applied to `arguments` spelled a
    /// record, which may then be named after it.
    fn note_record_spelling(
        &mut self,
        converted: MonotypeId,
        file_id: FileId,
        item: TypeItemId,
        arguments: &[TypeId],
    ) {
        if !matches!(self.get(converted), Monotype::Record(_)) {
            return;
        }
        let spellings = self.record_spellings.entry(converted).or_default();
        let spelling = (file_id, item, Arc::from(arguments));
        if !spellings.contains(&spelling) {
            spellings.push(spelling);
        }
    }

    /// The record of a closed row.
    pub fn record<Q>(&mut self, context: &mut Context<'_, Q>, row: TypeId) -> Converted<MonotypeId>
    where
        Q: checking::ExternalQueries,
    {
        self.convert_record(context, row, 0)
    }

    fn convert_record<Q>(
        &mut self,
        context: &mut Context<'_, Q>,
        row: TypeId,
        expansions: usize,
    ) -> Converted<MonotypeId>
    where
        Q: checking::ExternalQueries,
    {
        let row = context.types.strip_annotations(row);
        // A row synonym, `Padding (TokValue String ())`, or a row whose tail is
        // one spells a closed row only once it is expanded and flattened.
        let row = match context.types.lookup(row) {
            Type::Row(row_id) if context.queries.lookup_row_type(*row_id).tail.is_none() => row,
            _ => expand_synonyms(context, row)?,
        };
        let Type::Row(row_id) = context.types.lookup(row).clone() else {
            return Err(open_type(context, row)?);
        };
        let row_type = context.queries.lookup_row_type(row_id).clone();
        if let Some(tail) = row_type.tail
            && !matches!(context.types.lookup(tail), Type::Unification(_))
        {
            return Err(open_type(context, row)?);
        }
        let mut fields: Vec<RecordField> = Vec::with_capacity(row_type.fields.len());
        for field in row_type.fields.iter() {
            // A row lists a duplicated label leftmost first. A record value
            // holds only that one, as a JS object does after `Record.union`,
            // and `Lacks` keeps the shadowed types from being observed.
            if fields.iter().any(|known| known.label == field.label) {
                continue;
            }
            let monotype = self.convert(context, field.id, expansions)?;
            fields.push(RecordField { label: field.label.clone(), monotype });
        }
        fields.sort_by(|left, right| left.label.cmp(&right.label));
        Ok(self.intern(Monotype::Record(Arc::from(fields))))
    }

    /// A non-regular data type, such as `data Nested a = Flat | Deep a (Nested (Array a))`,
    /// would need infinitely many specializations; its arguments are erased instead.
    fn is_regular<Q>(
        &mut self,
        context: &mut Context<'_, Q>,
        file_id: FileId,
        item: TypeItemId,
    ) -> QueryResult<bool>
    where
        Q: checking::ExternalQueries,
    {
        if let Some(&regular) = self.regular.get(&(file_id, item)) {
            return Ok(regular);
        }
        self.regular.insert((file_id, item), true);
        let module = context.module(file_id)?;
        let terms = match &module.indexed.items[item].kind {
            IndexedTypeItemKind::Data { constructors, .. } => constructors.clone(),
            _ => vec![],
        };
        let mut regular = true;
        for term in terms {
            let Some(signature) = module.checked.lookup_term_item_type(term) else { continue };
            let (_, mut current) = context.types.peel_quantifiers(signature);
            let mut fields = vec![];
            while let Some((argument, result)) = context.types.function_parts(current) {
                fields.push(argument);
                current = result;
            }
            let (_, parameters) = context.types.spine(current);
            let parameters: Vec<TypeId> = parameters
                .iter()
                .map(|&parameter| context.types.strip_annotations(parameter))
                .collect();
            for field in fields {
                if !regular_occurrences(context, field, file_id, item, &parameters) {
                    regular = false;
                }
            }
        }
        self.regular.insert((file_id, item), regular);
        Ok(regular)
    }

    pub fn unfold<Q>(
        &mut self,
        context: &mut Context<'_, Q>,
        data: &DataType,
    ) -> Converted<MonotypeId>
    where
        Q: checking::ExternalQueries,
    {
        if let Some(&unfolded) = self.unfolded.get(data) {
            return Ok(unfolded);
        }
        let module = context.module(data.file_id)?;
        let IndexedTypeItemKind::Newtype { constructors, .. } =
            &module.indexed.items[data.item].kind
        else {
            return Err(UnsupportedState::MissingDeclaration.into());
        };
        let Some(&constructor) = constructors.first() else {
            return Err(UnsupportedState::MissingDeclaration.into());
        };
        let mut applied = context.queries.intern_type(Type::Constructor(data.file_id, data.item));
        for &argument in data.arguments.iter() {
            applied = context.queries.intern_type(Type::Application(applied, argument));
        }
        let Some(underlying) = newtype_underlying(context, data.file_id, constructor, applied)?
        else {
            return Err(open_type(context, applied)?);
        };
        let unfolded = self.monotype(context, underlying)?;
        self.unfolded.insert(data.clone(), unfolded);
        Ok(unfolded)
    }

    /// [`Self::unfold`], reporting what cannot be unfolded against `definition`.
    pub fn unfold_in<Q>(
        &mut self,
        context: &mut Context<'_, Q>,
        data: &DataType,
        definition: &str,
    ) -> GoResult<MonotypeId>
    where
        Q: checking::ExternalQueries,
    {
        self.unfold(context, data).map_err(|failure| failure.at(definition))
    }

    pub fn constructors<Q>(
        &mut self,
        context: &mut Context<'_, Q>,
        data: &DataType,
    ) -> Converted<Arc<[DataConstructor]>>
    where
        Q: checking::ExternalQueries,
    {
        if let Some(constructors) = self.constructors.get(data) {
            return Ok(Arc::clone(constructors));
        }
        let module = context.module(data.file_id)?;
        let terms = match &module.indexed.items[data.item].kind {
            IndexedTypeItemKind::Data { constructors, .. }
            | IndexedTypeItemKind::Newtype { constructors, .. } => constructors.clone(),
            _ => vec![],
        };
        let mut constructors = Vec::with_capacity(terms.len());
        for term in terms {
            let Some(signature) = module.checked.lookup_term_item_type(term) else {
                return Err(UnsupportedState::MissingDeclaration.into());
            };
            let (_, body) = context.types.peel_quantifiers(signature);
            let mut field_types = vec![];
            let mut current = body;
            while let Some((argument, result)) = context.types.function_parts(current) {
                field_types.push(argument);
                current = result;
            }
            let (_, parameters) = context.types.spine(current);
            let mut substitution = Substitution::default();
            for (parameter, &argument) in parameters.iter().zip(data.arguments.iter()) {
                if let Type::Rigid(name, _, _) = context.types.lookup(*parameter) {
                    substitution.insert(*name, argument);
                }
            }
            let mut fields = Vec::with_capacity(field_types.len());
            let mut refuted = false;
            for field_type in field_types {
                let field_type = context.types.substitute(field_type, &substitution);
                refuted |= is_refuted_equality(context, field_type)?;
                let constructor = module.indexed.items[term].name.clone().unwrap_or_default();
                let owner = format!("{}.{constructor}", module.name);
                self.note_rank_n_field(context, field_type, &owner)?;
                fields.push(self.monotype(context, field_type)?)
            }
            let name = module.indexed.items[term].name.clone().unwrap_or_default();
            constructors.push(DataConstructor { term, name, fields, refuted });
        }
        let constructors: Arc<[DataConstructor]> = Arc::from(constructors);
        self.constructors.insert(data.clone(), Arc::clone(&constructors));
        Ok(constructors)
    }

    pub fn used_parameters<Q>(
        &mut self,
        context: &mut Context<'_, Q>,
        file_id: FileId,
        item: TypeItemId,
    ) -> QueryResult<Arc<[bool]>>
    where
        Q: checking::ExternalQueries,
    {
        if let Some(used) = self.used_parameters.get(&(file_id, item)) {
            return Ok(Arc::clone(used));
        }
        let module = context.module(file_id)?;
        let terms = match &module.indexed.items[item].kind {
            IndexedTypeItemKind::Data { constructors, .. }
            | IndexedTypeItemKind::Newtype { constructors, .. } => constructors.clone(),
            _ => vec![],
        };
        let mut used: Vec<bool> = vec![];
        for term in terms {
            let Some(signature) = module.checked.lookup_term_item_type(term) else { continue };
            let (_, mut current) = context.types.peel_quantifiers(signature);
            let mut fields = vec![];
            while let Some((field, result)) = context.types.function_parts(current) {
                fields.push(field);
                current = result;
            }
            let mut mentioned = vec![];
            for field in fields {
                context.types.rigid_names_outside(field, Some(current), &mut mentioned);
            }
            let (_, parameters) = context.types.spine(current);
            used.resize(used.len().max(parameters.len()), false);
            for (position, parameter) in parameters.iter().enumerate() {
                if let Type::Rigid(name, _, _) = context.types.lookup(*parameter)
                    && mentioned.contains(name)
                {
                    used[position] = true;
                }
            }
        }
        let used: Arc<[bool]> = Arc::from(used);
        self.used_parameters.insert((file_id, item), Arc::clone(&used));
        Ok(used)
    }
}

const EQUALITY_UNWRAP_LIMIT: usize = 8;

/// Whether a type is an equality proof between apart types: after unwrapping
/// newtypes (`Leibniz a b`), `forall f. f a -> f b` where `a` and `b` are
/// closed and clash. No value has that type: `Data.Leibniz.refute` turns one
/// into a `Void` by choosing `f` to map `a` to `Unit` and `b` to `Void`.
fn is_refuted_equality<Q>(context: &mut Context<'_, Q>, type_id: TypeId) -> QueryResult<bool>
where
    Q: checking::ExternalQueries,
{
    let mut current = expand_synonyms(context, type_id)?;
    for _ in 0..EQUALITY_UNWRAP_LIMIT {
        let (head, _) = context.types.spine(current);
        let Type::Constructor(file_id, item) = context.types.lookup(head).clone() else { break };
        let module = context.module(file_id)?;
        let IndexedTypeItemKind::Newtype { constructors, .. } = &module.indexed.items[item].kind
        else {
            return Ok(false);
        };
        let Some(&constructor) = constructors.first() else { return Ok(false) };
        let Some(underlying) = newtype_underlying(context, file_id, constructor, current)? else {
            return Ok(false);
        };
        current = expand_synonyms(context, underlying)?;
    }
    let (names, body) = context.types.peel_quantifiers(current);
    let Some((argument, result)) = context.types.function_parts(body) else { return Ok(false) };
    let (argument_head, argument_arguments) = context.types.spine(argument);
    let (result_head, result_arguments) = context.types.spine(result);
    let (Type::Rigid(argument_variable, ..), Type::Rigid(result_variable, ..)) =
        (context.types.lookup(argument_head), context.types.lookup(result_head))
    else {
        return Ok(false);
    };
    let ([left], [right]) = (&argument_arguments[..], &result_arguments[..]) else {
        return Ok(false);
    };
    if argument_variable != result_variable || !names.contains(argument_variable) {
        return Ok(false);
    }
    // Data types share one representation for arguments that differ only by
    // newtypes, so equalities are refuted only between representations.
    let left = erase_newtypes(context, *left, 0, &mut vec![])?;
    let right = erase_newtypes(context, *right, 0, &mut vec![])?;
    Ok(apart(context, left, right))
}

/// Whether two types certainly differ: some position holds distinct type
/// constructors or literals. Anything not closed is never apart.
fn apart<Q>(context: &mut Context<'_, Q>, left: TypeId, right: TypeId) -> bool
where
    Q: checking::ExternalQueries,
{
    if let (Some((left_argument, left_result)), Some((right_argument, right_result))) =
        (context.types.function_parts(left), context.types.function_parts(right))
    {
        return apart(context, left_argument, right_argument)
            || apart(context, left_result, right_result);
    }
    let (left_head, left_arguments) = context.types.spine(left);
    let (right_head, right_arguments) = context.types.spine(right);
    match (context.types.lookup(left_head), context.types.lookup(right_head)) {
        (Type::Constructor(left_file, left_item), Type::Constructor(right_file, right_item)) => {
            if (left_file, left_item) != (right_file, right_item) {
                return true;
            }
            left_arguments.len() == right_arguments.len()
                && left_arguments
                    .iter()
                    .zip(right_arguments.iter())
                    .any(|(&left, &right)| apart(context, left, right))
        }
        (Type::Integer(left), Type::Integer(right)) => left != right,
        (Type::String(_, left), Type::String(_, right)) => left != right,
        _ => false,
    }
}

/// Newtypes have the runtime representation of their underlying type, and synonyms
/// are only names, so two data types whose arguments differ only by either share one
/// Go type.
fn erase_newtypes<Q>(
    context: &mut Context<'_, Q>,
    type_id: TypeId,
    expansions: usize,
    expanding: &mut Vec<TypeId>,
) -> QueryResult<TypeId>
where
    Q: checking::ExternalQueries,
{
    canonicalise(context, type_id, expansions, expanding, true)
}

/// Expands every synonym in a closed type, so that instance heads match it
/// structurally.
pub fn expand_synonyms<Q>(context: &mut Context<'_, Q>, type_id: TypeId) -> QueryResult<TypeId>
where
    Q: checking::ExternalQueries,
{
    canonicalise(context, type_id, 0, &mut vec![], false)
}

fn canonicalise<Q>(
    context: &mut Context<'_, Q>,
    type_id: TypeId,
    expansions: usize,
    expanding: &mut Vec<TypeId>,
    erase: bool,
) -> QueryResult<TypeId>
where
    Q: checking::ExternalQueries,
{
    // Below a newtype expansion the result depends on the expansions above it,
    // so only outermost results are remembered.
    if expansions > 0 || !expanding.is_empty() {
        return canonicalise_uncached(context, type_id, expansions, expanding, erase);
    }
    if let Some(&canonical) = context.canonical.get(&(type_id, erase)) {
        return Ok(canonical);
    }
    let canonical = canonicalise_uncached(context, type_id, expansions, expanding, erase)?;
    context.canonical.insert((type_id, erase), canonical);
    Ok(canonical)
}

fn canonicalise_uncached<Q>(
    context: &mut Context<'_, Q>,
    type_id: TypeId,
    expansions: usize,
    expanding: &mut Vec<TypeId>,
    erase: bool,
) -> QueryResult<TypeId>
where
    Q: checking::ExternalQueries,
{
    if expansions > NEWTYPE_EXPANSION_LIMIT {
        return Ok(type_id);
    }
    let type_id = context.types.strip_annotations(type_id);
    match context.types.lookup(type_id).clone() {
        Type::Function(argument, result) => {
            let argument = canonicalise(context, argument, expansions, expanding, erase)?;
            let result = canonicalise(context, result, expansions, expanding, erase)?;
            return Ok(context.queries.intern_type(Type::Function(argument, result)));
        }
        Type::Row(row) => {
            let row = context.queries.lookup_row_type(row).clone();
            let mut fields = Vec::with_capacity(row.fields.len());
            for field in row.fields.iter() {
                let id = canonicalise(context, field.id, expansions, expanding, erase)?;
                fields.push(checking::core::RowField { label: field.label.clone(), id });
            }
            // A tail such as `RENDER ()` in `METRICS + RENDER + ()` is a synonym
            // for more fields: expand it and flatten, so that every spelling of a
            // closed row has one canonical form.
            let mut tail = row.tail;
            while let Some(current) = tail {
                let expanded = canonicalise(context, current, expansions, expanding, erase)?;
                let Type::Row(inner) = context.types.lookup(expanded).clone() else {
                    tail = Some(expanded);
                    break;
                };
                let inner = context.queries.lookup_row_type(inner).clone();
                fields.extend(inner.fields.iter().cloned());
                tail = inner.tail;
            }
            fields.sort_by(|left, right| left.label.cmp(&right.label));
            let row = checking::core::RowType { fields: Arc::from(fields), tail };
            let row = context.queries.intern_row_type(row);
            return Ok(context.queries.intern_type(Type::Row(row)));
        }
        _ => {}
    }
    let (head, arguments) = context.types.spine(type_id);
    match context.types.lookup(head).clone() {
        Type::Rigid(..) | Type::Unification(_) if erase && arguments.is_empty() => {
            if context.types.erasure(head).is_some() {
                return Ok(head);
            }
            Ok(context.types.erased(Erasure::ArgumentVariable))
        }
        Type::Constructor(file_id, item) => {
            let module = context.module(file_id)?;
            if erase
                && !is_recursive_newtype(context, file_id, item)?
                && let IndexedTypeItemKind::Newtype { constructors, .. } =
                    &module.indexed.items[item].kind
                && let Some(&constructor) = constructors.first()
                && let Some(underlying) =
                    newtype_underlying(context, file_id, constructor, type_id)?
            {
                if expanding.contains(&type_id) {
                    return Ok(context.types.erased(Erasure::NewtypeCycle));
                }
                expanding.push(type_id);
                let erased = canonicalise(context, underlying, expansions + 1, expanding, erase)?;
                expanding.pop();
                let erased_newtype = crate::context::ErasedNewtype {
                    file_id,
                    item,
                    arguments: Arc::from(arguments),
                    erased,
                };
                if !context.erased_newtypes.contains(&erased_newtype) {
                    context.erased_newtypes.push(erased_newtype);
                }
                return Ok(erased);
            }
            if erase
                && !arguments.is_empty()
                && ignores_arguments(&module.name, module.indexed.items[item].name.as_deref())
            {
                let empty = checking::core::RowType { fields: Arc::from([]), tail: None };
                let empty = context.queries.intern_row_type(empty);
                let empty = context.queries.intern_type(Type::Row(empty));
                let mut rebuilt = head;
                for _ in arguments {
                    rebuilt = context.queries.intern_type(Type::Application(rebuilt, empty));
                }
                return Ok(rebuilt);
            }
            if module.name == "Prim"
                && module.indexed.items[item].name.as_deref() == Some("Function")
                && let [argument, result] = arguments[..]
            {
                let function = context.queries.intern_type(Type::Function(argument, result));
                return canonicalise(context, function, expansions, expanding, erase);
            }
            if arguments.is_empty() {
                return Ok(type_id);
            }
            let mut rebuilt = head;
            for argument in arguments {
                let argument = canonicalise(context, argument, expansions, expanding, erase)?;
                rebuilt = context.queries.intern_type(Type::Application(rebuilt, argument));
            }
            Ok(rebuilt)
        }
        Type::Synonym(file_id, item) => match expand_synonym(context, file_id, item, &arguments)? {
            Some(expanded) => canonicalise(context, expanded, expansions + 1, expanding, erase),
            None => Ok(type_id),
        },
        _ => Ok(type_id),
    }
}

fn ignores_arguments(module: &str, name: Option<&str>) -> bool {
    matches!(
        (module, name),
        ("Data.Variant", Some("Variant")) | ("Data.Functor.Variant", Some("VariantF"))
    )
}

fn regular_occurrences<Q>(
    context: &mut Context<'_, Q>,
    type_id: TypeId,
    file_id: FileId,
    item: TypeItemId,
    parameters: &[TypeId],
) -> bool
where
    Q: checking::ExternalQueries,
{
    let type_id = context.types.strip_annotations(type_id);
    let (head, arguments) = context.types.spine(type_id);
    if !arguments.is_empty() {
        if let Type::Constructor(head_file, head_item) = *context.types.lookup(head)
            && head_file == file_id
            && head_item == item
        {
            let same = arguments.len() == parameters.len()
                && arguments.iter().zip(parameters).all(|(&argument, &parameter)| {
                    context.types.strip_annotations(argument) == parameter
                });
            if !same {
                return false;
            }
        }
        return arguments
            .iter()
            .all(|&argument| regular_occurrences(context, argument, file_id, item, parameters));
    }
    match context.types.lookup(type_id).clone() {
        Type::Function(argument, result) => {
            regular_occurrences(context, argument, file_id, item, parameters)
                && regular_occurrences(context, result, file_id, item, parameters)
        }
        Type::Row(row) => {
            let row = context.queries.lookup_row_type(row).clone();
            row.fields
                .iter()
                .all(|field| regular_occurrences(context, field.id, file_id, item, parameters))
        }
        _ => true,
    }
}

pub fn is_recursive_newtype<Q>(
    context: &mut Context<'_, Q>,
    file_id: FileId,
    item: TypeItemId,
) -> QueryResult<bool>
where
    Q: checking::ExternalQueries,
{
    if let Some(&recursive) = context.recursive_newtypes.get(&(file_id, item)) {
        return Ok(recursive);
    }
    let mut visited = vec![(file_id, item)];
    let recursive = match declared_underlying(context, file_id, item)? {
        Some(underlying) => mentions_type(context, underlying, (file_id, item), &mut visited, 0)?,
        None => false,
    };
    context.recursive_newtypes.insert((file_id, item), recursive);
    Ok(recursive)
}

fn declared_underlying<Q>(
    context: &mut Context<'_, Q>,
    file_id: FileId,
    item: TypeItemId,
) -> QueryResult<Option<TypeId>>
where
    Q: checking::ExternalQueries,
{
    let module = context.module(file_id)?;
    let IndexedTypeItemKind::Newtype { constructors, .. } = &module.indexed.items[item].kind else {
        return Ok(None);
    };
    let Some(signature) = constructors
        .first()
        .and_then(|&constructor| module.checked.lookup_term_item_type(constructor))
    else {
        return Ok(None);
    };
    let (_, body) = context.types.peel_quantifiers(signature);
    Ok(context.types.function_parts(body).map(|(underlying, _)| underlying))
}

fn mentions_type<Q>(
    context: &mut Context<'_, Q>,
    type_id: TypeId,
    target: (FileId, TypeItemId),
    visited: &mut Vec<(FileId, TypeItemId)>,
    expansions: usize,
) -> QueryResult<bool>
where
    Q: checking::ExternalQueries,
{
    if expansions > NEWTYPE_EXPANSION_LIMIT {
        return Ok(false);
    }
    let type_id = context.types.strip_annotations(type_id);
    match context.types.lookup(type_id).clone() {
        Type::Function(argument, result) => {
            return Ok(mentions_type(context, argument, target, visited, expansions)?
                || mentions_type(context, result, target, visited, expansions)?);
        }
        Type::Row(row) => {
            let row = context.queries.lookup_row_type(row).clone();
            for field in row.fields.iter() {
                if mentions_type(context, field.id, target, visited, expansions)? {
                    return Ok(true);
                }
            }
            return Ok(false);
        }
        Type::Forall(_, inner) | Type::Constrained(_, inner) => {
            return mentions_type(context, inner, target, visited, expansions);
        }
        _ => {}
    }
    let (head, arguments) = context.types.spine(type_id);
    for &argument in &arguments {
        if mentions_type(context, argument, target, visited, expansions)? {
            return Ok(true);
        }
    }
    match context.types.lookup(head).clone() {
        Type::Constructor(file_id, item) => {
            if (file_id, item) == target {
                return Ok(true);
            }
            if visited.contains(&(file_id, item)) {
                return Ok(false);
            }
            visited.push((file_id, item));
            match declared_underlying(context, file_id, item)? {
                Some(underlying) => {
                    mentions_type(context, underlying, target, visited, expansions + 1)
                }
                None => Ok(false),
            }
        }
        Type::Synonym(file_id, item) => {
            let expanded = match expand_synonym(context, file_id, item, &arguments)? {
                Some(expanded) => expanded,
                None => {
                    let module = context.module(file_id)?;
                    match module.checked.lookup_synonym(item) {
                        Some(synonym) => synonym.expansion,
                        None => return Ok(false),
                    }
                }
            };
            mentions_type(context, expanded, target, visited, expansions + 1)
        }
        _ => Ok(false),
    }
}

pub fn is_partial<Q>(context: &mut Context<'_, Q>, constraint: TypeId) -> QueryResult<bool>
where
    Q: checking::ExternalQueries,
{
    let (head, _) = context.types.spine(constraint);
    let Type::Constructor(file_id, item) = *context.types.lookup(head) else {
        return Ok(false);
    };
    context.is_type(file_id, item, "Prim", "Partial")
}

fn newtype_underlying<Q>(
    context: &mut Context<'_, Q>,
    file_id: FileId,
    constructor: TermItemId,
    applied: TypeId,
) -> QueryResult<Option<TypeId>>
where
    Q: checking::ExternalQueries,
{
    let module = context.module(file_id)?;
    let Some(signature) = module.checked.lookup_term_item_type(constructor) else {
        return Ok(None);
    };
    let (variables, body) = context.types.peel_quantifiers(signature);
    let Some((underlying, result)) = context.types.function_parts(body) else {
        return Ok(None);
    };
    let mut bindings = Substitution::default();
    if !context.types.match_type(result, applied, &variables, &mut bindings) {
        return Ok(None);
    }
    Ok(Some(context.types.substitute(underlying, &bindings)))
}

pub fn expand_synonym<Q>(
    context: &mut Context<'_, Q>,
    file_id: FileId,
    item: TypeItemId,
    arguments: &[TypeId],
) -> QueryResult<Option<TypeId>>
where
    Q: checking::ExternalQueries,
{
    let module = context.module(file_id)?;
    let Some(synonym) = module.checked.lookup_synonym(item) else {
        return Ok(None);
    };
    if arguments.len() < synonym.parameters.len() {
        return Ok(None);
    }
    let names: Vec<Name> = synonym.parameters.iter().map(|binder| binder.name).collect();
    let substitution: Substitution = names.iter().copied().zip(arguments.iter().copied()).collect();
    let mut expanded = context.types.substitute(synonym.expansion, &substitution);
    for &argument in &arguments[synonym.parameters.len()..] {
        expanded = context.queries.intern_type(Type::Application(expanded, argument));
    }
    Ok(Some(expanded))
}

fn erased_newtypes<Q>(
    context: &mut Context<'_, Q>,
    arguments: impl IntoIterator<Item = TypeId>,
    expansions: usize,
) -> QueryResult<Arc<[TypeId]>>
where
    Q: checking::ExternalQueries,
{
    arguments
        .into_iter()
        .map(|argument| erase_newtypes(context, argument, expansions, &mut vec![]))
        .collect()
}

fn open_type<Q>(context: &mut Context<'_, Q>, type_id: TypeId) -> QueryResult<Failure>
where
    Q: checking::ExternalQueries,
{
    let prim = context.module(context.queries.prim_id())?;
    let pretty = checking::core::pretty::Pretty::new(context.queries, &prim.checked);
    let rendered = pretty.render(type_id)?.to_string();
    Ok(UnsupportedState::OpenType { rendered }.into())
}
