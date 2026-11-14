use std::sync::Arc;

use building_types::QueryResult;
use checking::TypeId;
use checking::core::{Name, Type};
use files::FileId;
use indexing::{IndexedTypeItemKind, TermItemId, TypeItemId};
use rustc_hash::FxHashMap;
use smol_str::SmolStr;

use crate::context::Context;
use crate::erasure::Erasure;
use crate::error::UnsupportedState;
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
    /// A `foreign import data` type that the project's Go foreign package for
    /// its module declares, as a named Go type of the same name.
    ForeignData(DataType),
    Recursive(DataType),
    Erased(Erasure),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct RecordField {
    pub label: SmolStr,
    pub monotype: MonotypeId,
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
}

const NEWTYPE_EXPANSION_LIMIT: usize = 64;

#[derive(Default)]
pub struct Monotypes {
    interned: Vec<Monotype>,
    lookup: FxHashMap<Monotype, MonotypeId>,
    converted: FxHashMap<TypeId, MonotypeId>,
    constructors: FxHashMap<DataType, Arc<[DataConstructor]>>,
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
    /// Modules whose foreign imports the project implements in Go.
    pub foreign_modules: Vec<String>,
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

    pub fn get(&self, id: MonotypeId) -> &Monotype {
        &self.interned[id.0 as usize]
    }

    /// The one newtype whose representation a function type is, as `Lazy Int`
    /// is `Unit -> Int`.
    pub fn function_newtype(&self, id: MonotypeId) -> Option<&DataType> {
        self.function_newtypes.get(&id)?.as_ref()
    }

    pub fn unit(&mut self) -> MonotypeId {
        self.intern(Monotype::Unit)
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
    ) -> QueryResult<Result<MonotypeId, UnsupportedState>>
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
    ) -> QueryResult<Result<MonotypeId, UnsupportedState>>
    where
        Q: checking::ExternalQueries,
    {
        // Inside a newtype expansion the result depends on the newtypes being
        // expanded, so only conversions outside every expansion are remembered.
        if expansions > 0 || !self.expanding.is_empty() {
            return self.convert_uncached(context, type_id, expansions);
        }
        if let Some(&id) = self.converted.get(&type_id) {
            return Ok(Ok(id));
        }
        let converted = self.convert_uncached(context, type_id, expansions)?;
        if let Ok(id) = converted {
            self.converted.insert(type_id, id);
        }
        Ok(converted)
    }

    fn convert_uncached<Q>(
        &mut self,
        context: &mut Context<'_, Q>,
        type_id: TypeId,
        expansions: usize,
    ) -> QueryResult<Result<MonotypeId, UnsupportedState>>
    where
        Q: checking::ExternalQueries,
    {
        if expansions > NEWTYPE_EXPANSION_LIMIT {
            return Ok(Err(UnsupportedState::Construct {
                construct: "infinitely nested newtypes",
            }));
        }
        let type_id = context.types.strip_annotations(type_id);
        let monotype = match context.types.lookup(type_id).clone() {
            Type::Function(argument, result) => {
                let argument = match self.convert(context, argument, expansions)? {
                    Ok(argument) => argument,
                    Err(error) => return Ok(Err(error)),
                };
                let result = match self.convert(context, result, expansions)? {
                    Ok(result) => result,
                    Err(error) => return Ok(Err(error)),
                };
                Monotype::Function(argument, result)
            }
            Type::Forall(..) => match self.scheme_for(context, type_id)? {
                Some(scheme) => return self.convert_scheme(context, &scheme, expansions),
                None => {
                    // Without constraints there is no instantiation to specialize
                    // on yet: the quantified variables are erased.
                    let (names, inner) = context.types.peel_quantifiers(type_id);
                    let erased = context.types.erased(Erasure::RankN);
                    let substitution: crate::types::Substitution =
                        names.into_iter().map(|name| (name, erased)).collect();
                    let inner = context.types.substitute(inner, &substitution);
                    return self.convert(context, inner, expansions);
                }
            },
            Type::Rigid(..) => {
                Monotype::Erased(context.types.erasure(type_id).unwrap_or(Erasure::TypeVariable))
            }
            Type::Unification(_) => Monotype::Unit,
            Type::Application(..) | Type::Constructor(..) | Type::Synonym(..) => {
                return self.convert_application(context, type_id, expansions);
            }
            Type::Constrained(constraint, inner) => {
                if is_partial(context, constraint)? {
                    return self.convert(context, inner, expansions);
                }
                return Ok(Err(UnsupportedState::Construct {
                    construct: "constrained types in argument positions",
                }));
            }
            Type::Row(_) | Type::Integer(_) | Type::String(..) => {
                return Ok(Err(open_type(context, type_id)?));
            }
            Type::Free(_) | Type::Unknown(_) => return Ok(Err(open_type(context, type_id)?)),
            Type::Kinded(..) | Type::KindApplication(..) | Type::ConstraintOrigin(..) => {
                unreachable!("invariant violated: annotations are stripped before conversion")
            }
        };
        Ok(Ok(self.intern(monotype)))
    }

    fn convert_application<Q>(
        &mut self,
        context: &mut Context<'_, Q>,
        type_id: TypeId,
        expansions: usize,
    ) -> QueryResult<Result<MonotypeId, UnsupportedState>>
    where
        Q: checking::ExternalQueries,
    {
        let (head, arguments) = context.types.spine(type_id);
        let (file_id, item) = match context.types.lookup(head).clone() {
            Type::Constructor(file_id, item) => (file_id, item),
            Type::Synonym(file_id, item) => {
                return match expand_synonym(context, file_id, item, &arguments)? {
                    Some(expanded) => self.convert(context, expanded, expansions + 1),
                    None => Ok(Err(UnsupportedState::UnsaturatedType {
                        name: context.type_name(file_id, item)?.to_string(),
                    })),
                };
            }
            Type::Rigid(..) | Type::Unification(_) => {
                let erasure = context.types.erasure(head).unwrap_or(Erasure::VariableApplication);
                return Ok(Ok(self.intern(Monotype::Erased(erasure))));
            }
            Type::Function(..) if arguments.is_empty() => {
                return self.convert(context, head, expansions);
            }
            _ => return Ok(Err(open_type(context, type_id)?)),
        };

        let module = context.module(file_id)?;
        let name = module.indexed.items[item].name.clone().unwrap_or_default();
        let unary = |monotypes: &mut Monotypes,
                     context: &mut Context<'_, Q>,
                     argument: Option<&TypeId>|
         -> QueryResult<Result<MonotypeId, UnsupportedState>> {
            match argument {
                Some(&argument) => monotypes.convert(context, argument, expansions),
                None => Ok(Err(UnsupportedState::UnsaturatedType { name: name.to_string() })),
            }
        };

        let monotype = match (module.name.as_str(), name.as_str()) {
            ("Prim", "Int") => Monotype::Int,
            ("Prim", "Number") => Monotype::Number,
            ("Prim", "Boolean") => Monotype::Boolean,
            ("Prim", "Char") => Monotype::Char,
            ("Prim", "String") => Monotype::String,
            ("Prim", "Array") => match unary(self, context, arguments.first())? {
                Ok(element) => Monotype::Array(element),
                Err(error) => return Ok(Err(error)),
            },
            ("Prim", "Function") => {
                let [argument, result] = arguments[..] else {
                    return Ok(Err(UnsupportedState::UnsaturatedType { name: name.to_string() }));
                };
                let function = context.queries.intern_type(Type::Function(argument, result));
                return self.convert(context, function, expansions);
            }
            ("Prim", "Record") => {
                let Some(&row) = arguments.first() else {
                    return Ok(Err(UnsupportedState::UnsaturatedType { name: name.to_string() }));
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
                    return Ok(Err(open_type(context, type_id)?));
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
            ("Data.Exists", "Exists") => Monotype::Erased(Erasure::Existential),
            ("Data.Function.Uncurried", name) if name.starts_with("Fn") => {
                let Some((&result, parameters)) = arguments.split_last() else {
                    return Ok(Err(UnsupportedState::UnsaturatedType { name: name.to_string() }));
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
                    return Ok(Err(UnsupportedState::UnsaturatedType { name: name.to_string() }));
                };
                let result = match self.convert(context, result, expansions)? {
                    Ok(result) => self.intern(Monotype::Effect(result)),
                    Err(error) => return Ok(Err(error)),
                };
                return self.curried_function(context, parameters, result, expansions);
            }
            ("Control.Monad.ST.Uncurried", name) if name.starts_with("STFn") => {
                let [parameters @ .., _, result] = &arguments[..] else {
                    return Ok(Err(UnsupportedState::UnsaturatedType { name: name.to_string() }));
                };
                let result = match self.convert(context, *result, expansions)? {
                    Ok(result) => self.intern(Monotype::Effect(result)),
                    Err(error) => return Ok(Err(error)),
                };
                return self.curried_function(context, parameters, result, expansions);
            }
            ("Effect", "Effect") | ("Effect.Aff", "Aff" | "ParAff") => {
                match unary(self, context, arguments.first())? {
                    Ok(result) => Monotype::Effect(result),
                    Err(error) => return Ok(Err(error)),
                }
            }
            ("Control.Monad.ST.Internal", "ST") => match unary(self, context, arguments.get(1))? {
                Ok(result) => Monotype::Effect(result),
                Err(error) => return Ok(Err(error)),
            },
            ("Effect.Ref", "Ref") => match unary(self, context, arguments.first())? {
                Ok(value) => Monotype::Reference(value),
                Err(error) => return Ok(Err(error)),
            },
            ("Data.Array.ST", "STArray") => match unary(self, context, arguments.get(1))? {
                Ok(element) => Monotype::MutableArray(element),
                Err(error) => return Ok(Err(error)),
            },
            ("Effect.Exception", "Error") => Monotype::Error,
            ("Data.String.Regex", "Regex") => Monotype::Regex,
            ("Effect.Synchronized", "Mutex") => Monotype::Mutex,
            ("JS.BigInt", "BigInt") => Monotype::BigInt,
            ("Data.Lazy", "Lazy") => match unary(self, context, arguments.first())? {
                Ok(value) => Monotype::Lazy(value),
                Err(error) => return Ok(Err(error)),
            },
            ("Promise.Internal", "Promise")
            | ("Promise.Rejection", "Rejection")
            | ("Foreign", "Foreign") => Monotype::Opaque,
            ("Data.Nullable", "Nullable") => match unary(self, context, arguments.first())? {
                Ok(element) => Monotype::Nullable(element),
                Err(error) => return Ok(Err(error)),
            },
            ("Foreign.Object", "Object") => match unary(self, context, arguments.first())? {
                Ok(element) => Monotype::Object(element),
                Err(error) => return Ok(Err(error)),
            },
            ("Foreign.Object.ST", "STObject") => match unary(self, context, arguments.get(1))? {
                Ok(element) => Monotype::Object(element),
                Err(error) => return Ok(Err(error)),
            },
            ("Control.Monad.ST.Internal", "STRef") => {
                match unary(self, context, arguments.get(1))? {
                    Ok(value) => Monotype::Reference(value),
                    Err(error) => return Ok(Err(error)),
                }
            }
            _ => match &module.indexed.items[item].kind {
                IndexedTypeItemKind::Newtype { constructors, .. } => {
                    let Some(&constructor) = constructors.first() else {
                        return Ok(Err(open_type(context, type_id)?));
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
                        return Ok(Ok(self.intern(Monotype::Recursive(data))));
                    }
                    if self.expanding.contains(&type_id) {
                        return Ok(Ok(self.intern(Monotype::Erased(Erasure::NewtypeCycle))));
                    }
                    let Some(underlying) =
                        newtype_underlying(context, file_id, constructor, type_id)?
                    else {
                        return Ok(Err(open_type(context, type_id)?));
                    };
                    let owner = format!("{}.{name}", module.name);
                    self.note_rank_n_field(context, underlying, &owner)?;
                    self.expanding.push(type_id);
                    let converted = self.convert(context, underlying, expansions + 1);
                    self.expanding.pop();
                    if let Ok(Ok(converted)) = converted
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
                IndexedTypeItemKind::Data { constructors, .. } if constructors.is_empty() => {
                    Monotype::Erased(Erasure::EmptyData)
                }
                IndexedTypeItemKind::Data { .. } => {
                    let regular = self.is_regular(context, file_id, item)?;
                    let mut canonical = Vec::with_capacity(arguments.len());
                    for argument in arguments {
                        if regular {
                            canonical.push(erase_newtypes(
                                context,
                                argument,
                                expansions,
                                &mut vec![],
                            )?);
                        } else {
                            canonical.push(context.types.erased(Erasure::NonRegular));
                        }
                    }
                    Monotype::Data(DataType { file_id, item, arguments: Arc::from(canonical) })
                }
                _ if crate::foreign::is_opaque_foreign_data(&module.name, &name) => {
                    Monotype::Opaque
                }
                _ if self.foreign_modules.iter().any(|provided| *provided == module.name) => {
                    let mut canonical = Vec::with_capacity(arguments.len());
                    for argument in arguments {
                        canonical.push(erase_newtypes(context, argument, expansions, &mut vec![])?);
                    }
                    Monotype::ForeignData(DataType {
                        file_id,
                        item,
                        arguments: Arc::from(canonical),
                    })
                }
                _ => {
                    let name = format!("{}.{name}", module.name);
                    return Ok(Err(UnsupportedState::ForeignData { name }));
                }
            },
        };
        Ok(Ok(self.intern(monotype)))
    }

    fn curried_function<Q>(
        &mut self,
        context: &mut Context<'_, Q>,
        parameters: &[TypeId],
        result: MonotypeId,
        expansions: usize,
    ) -> QueryResult<Result<MonotypeId, UnsupportedState>>
    where
        Q: checking::ExternalQueries,
    {
        let mut curried = result;
        for &parameter in parameters.iter().rev() {
            let parameter = match self.convert(context, parameter, expansions)? {
                Ok(parameter) => parameter,
                Err(error) => return Ok(Err(error)),
            };
            curried = self.function(parameter, curried);
        }
        Ok(Ok(curried))
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
            return Ok(());
        }
        if context.types.contains_erased(scheme.key.body()) {
            self.new_erased_owners.push(owner.to_string());
            return Ok(());
        }
        if self.schemes.is_rank_n(&scheme.key)
            || self.new_rank_n_keys.iter().any(|(key, _)| *key == scheme.key)
        {
            return Ok(());
        }
        let probes = [context.types.erased(Erasure::RankN), self.probe_type(context)];
        let mut converted = Vec::with_capacity(probes.len());
        for probe in probes {
            let types: Vec<TypeId> = scheme.names.iter().map(|_| probe).collect();
            let instantiated = scheme.instantiate(context, &types);
            match self.convert(context, instantiated, 1)? {
                Ok(monotype) => converted.push(monotype),
                Err(_) => return Ok(()),
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
    ) -> QueryResult<Result<MonotypeId, UnsupportedState>>
    where
        Q: checking::ExternalQueries,
    {
        let instantiations = self.schemes.get(&scheme.key).to_vec();
        let mut fields = Vec::with_capacity(instantiations.len());
        for instantiation in instantiations {
            let instantiated = scheme.instantiate(context, &instantiation.types);
            let monotype = match self.convert(context, instantiated, expansions)? {
                Ok(monotype) => monotype,
                Err(error) => return Ok(Err(error)),
            };
            fields.push(RecordField { label: instantiation.label, monotype });
        }
        fields.sort_by(|left, right| left.label.cmp(&right.label));
        Ok(Ok(self.intern(Monotype::Record(Arc::from(fields)))))
    }

    fn convert_record<Q>(
        &mut self,
        context: &mut Context<'_, Q>,
        row: TypeId,
        expansions: usize,
    ) -> QueryResult<Result<MonotypeId, UnsupportedState>>
    where
        Q: checking::ExternalQueries,
    {
        let row = context.types.strip_annotations(row);
        let Type::Row(row_id) = context.types.lookup(row).clone() else {
            return Ok(Err(open_type(context, row)?));
        };
        let row_type = context.queries.lookup_row_type(row_id).clone();
        if let Some(tail) = row_type.tail
            && !matches!(context.types.lookup(tail), Type::Unification(_))
        {
            return Ok(Err(open_type(context, row)?));
        }
        let mut fields = Vec::with_capacity(row_type.fields.len());
        for field in row_type.fields.iter() {
            let monotype = match self.convert(context, field.id, expansions)? {
                Ok(monotype) => monotype,
                Err(error) => return Ok(Err(error)),
            };
            fields.push(RecordField { label: field.label.clone(), monotype });
        }
        fields.sort_by(|left, right| left.label.cmp(&right.label));
        Ok(Ok(self.intern(Monotype::Record(Arc::from(fields)))))
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
    ) -> QueryResult<Result<MonotypeId, UnsupportedState>>
    where
        Q: checking::ExternalQueries,
    {
        if let Some(&unfolded) = self.unfolded.get(data) {
            return Ok(Ok(unfolded));
        }
        let module = context.module(data.file_id)?;
        let IndexedTypeItemKind::Newtype { constructors, .. } =
            &module.indexed.items[data.item].kind
        else {
            return Ok(Err(UnsupportedState::MissingDeclaration));
        };
        let Some(&constructor) = constructors.first() else {
            return Ok(Err(UnsupportedState::MissingDeclaration));
        };
        let mut applied = context.queries.intern_type(Type::Constructor(data.file_id, data.item));
        for &argument in data.arguments.iter() {
            applied = context.queries.intern_type(Type::Application(applied, argument));
        }
        let Some(underlying) = newtype_underlying(context, data.file_id, constructor, applied)?
        else {
            return Ok(Err(open_type(context, applied)?));
        };
        let unfolded = match self.monotype(context, underlying)? {
            Ok(unfolded) => unfolded,
            Err(error) => return Ok(Err(error)),
        };
        self.unfolded.insert(data.clone(), unfolded);
        Ok(Ok(unfolded))
    }

    pub fn constructors<Q>(
        &mut self,
        context: &mut Context<'_, Q>,
        data: &DataType,
    ) -> QueryResult<Result<Arc<[DataConstructor]>, UnsupportedState>>
    where
        Q: checking::ExternalQueries,
    {
        if let Some(constructors) = self.constructors.get(data) {
            return Ok(Ok(Arc::clone(constructors)));
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
                return Ok(Err(UnsupportedState::MissingDeclaration));
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
            for field_type in field_types {
                let field_type = context.types.substitute(field_type, &substitution);
                let constructor = module.indexed.items[term].name.clone().unwrap_or_default();
                let owner = format!("{}.{constructor}", module.name);
                self.note_rank_n_field(context, field_type, &owner)?;
                match self.monotype(context, field_type)? {
                    Ok(field) => fields.push(field),
                    Err(error) => return Ok(Err(error)),
                }
            }
            let name = module.indexed.items[term].name.clone().unwrap_or_default();
            constructors.push(DataConstructor { term, name, fields });
        }
        let constructors: Arc<[DataConstructor]> = Arc::from(constructors);
        self.constructors.insert(data.clone(), Arc::clone(&constructors));
        Ok(Ok(constructors))
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
                let erased = canonicalise(context, underlying, expansions + 1, expanding, erase);
                expanding.pop();
                return erased;
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

fn open_type<Q>(context: &mut Context<'_, Q>, type_id: TypeId) -> QueryResult<UnsupportedState>
where
    Q: checking::ExternalQueries,
{
    let prim = context.module(context.queries.prim_id())?;
    let pretty = checking::core::pretty::Pretty::new(context.queries, &prim.checked);
    let rendered = pretty.render(type_id)?.to_string();
    Ok(UnsupportedState::OpenType { rendered })
}
