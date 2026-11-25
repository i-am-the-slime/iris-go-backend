use std::sync::Arc;

use building_types::QueryResult;
use checking::TypeId;
use checking::core::Type;
use files::FileId;
use indexing::{IndexedTypeItemKind, TypeItemId};
use rustc_hash::FxHashMap;

use super::longs::signedness;
use super::types::{
    closed_row, erase_newtypes, erased_newtypes, expand_synonym, expand_synonyms, is_partial,
    is_recursive_newtype, newtype_underlying, open_type,
};
use super::{
    Converted, DataType, Failure, Monotype, MonotypeId, Monotypes, NEWTYPE_EXPANSION_LIMIT,
    RecordField, supported,
};
use crate::context::Context;
use crate::erasure::Erasure;
use crate::error::UnsupportedState;
use crate::scheme::{
    ConstrainedScheme, Read, ReifiedValue, constrained_scheme, rank_n_scheme, reified_value,
};

impl Monotypes {
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

    pub(super) fn convert<Q>(
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
            self.schemes.note_cached(Read::Converted(type_id));
            return Ok(id);
        }
        let reads_start = self.schemes.read_count();
        let converted = self.convert_uncached(context, type_id, expansions);
        if let Ok(id) = converted {
            self.converted.insert(type_id, id);
            self.converted_reads.insert(type_id, self.schemes.reads_since(reads_start));
        }
        converted
    }

    /// Whether what a read saw has changed since: the decision was written
    /// after the read, or the cached conversion read something that changed.
    pub fn is_stale(&self, read: &Read, staleness: &mut FxHashMap<Read, bool>) -> bool {
        let reads = match read {
            Read::Decision(decision, version) => {
                return self.schemes.is_written_since(decision, *version);
            }
            Read::Converted(type_id) => self.converted_reads.get(type_id),
            Read::Unfolded(data) => self.unfolded_reads.get(data),
            Read::Constructors(data) => self.constructors_reads.get(data),
        };
        if let Some(&stale) = staleness.get(read) {
            return stale;
        }
        let Some(reads) = reads else { return true };
        staleness.insert(read.clone(), false);
        let stale = reads.iter().any(|read| self.is_stale(read, staleness));
        staleness.insert(read.clone(), stale);
        stale
    }

    /// Forgets the cached conversions that read a decision that changed since,
    /// so that they are converted again under the schemes as they are now.
    pub fn forget_stale_conversions(&mut self) {
        let mut staleness = FxHashMap::default();
        let stale_types: Vec<TypeId> = self
            .converted_reads
            .keys()
            .copied()
            .filter(|&type_id| self.is_stale(&Read::Converted(type_id), &mut staleness))
            .collect();
        let stale_unfolded: Vec<DataType> = self
            .unfolded_reads
            .keys()
            .filter(|data| self.is_stale(&Read::Unfolded((*data).clone()), &mut staleness))
            .cloned()
            .collect();
        let stale_constructors: Vec<DataType> = self
            .constructors_reads
            .keys()
            .filter(|data| self.is_stale(&Read::Constructors((*data).clone()), &mut staleness))
            .cloned()
            .collect();
        for type_id in stale_types {
            self.converted.remove(&type_id);
            self.converted_reads.remove(&type_id);
        }
        for data in stale_unfolded {
            self.unfolded.remove(&data);
            self.unfolded_reads.remove(&data);
        }
        for data in stale_constructors {
            self.constructors.remove(&data);
            self.constructors_reads.remove(&data);
        }
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
                    let accumulator = match rank_n_scheme(context, type_id)? {
                        Some(scheme) => self.schemes.accumulator(&scheme.key),
                        None => None,
                    };
                    if let Some(accumulator) = accumulator {
                        let (names, inner) = context.types.peel_quantifiers(type_id);
                        let substitution: crate::types::Substitution =
                            names.into_iter().map(|name| (name, accumulator)).collect();
                        let inner = context.types.substitute(inner, &substitution);
                        return self.convert(context, inner, expansions);
                    }
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
            Type::Unification(_) => Monotype::Erased(Erasure::Unsolved),
            Type::Application(..) | Type::Constructor(..) | Type::Synonym(..) => {
                return self.convert_application(context, type_id, expansions);
            }
            Type::Constrained(constraint, inner) => {
                if is_partial(context, constraint)? {
                    return self.convert(context, inner, expansions);
                }
                if let Some(scheme) = constrained_scheme(context, type_id)? {
                    return self.convert_scheme(context, &scheme, expansions);
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
            Type::Rigid(..) if context.types.is_cons_list(head) => {
                let [element] = arguments[..] else {
                    let name = "ConsList".into();
                    return Err(UnsupportedState::UnsaturatedType { name }.into());
                };
                let element = self.convert(context, element, expansions)?;
                return Ok(self.intern(Monotype::ConsList(element)));
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

        match crate::primitives::known_type(&module.name, &name) {
            Some(crate::primitives::KnownType::SignedLong) => {
                let Some(&phantom) = arguments.first() else {
                    return Err(UnsupportedState::UnsaturatedType { name: name.to_string() }.into());
                };
                let monotype = match signedness(context, phantom)? {
                    Some(crate::primitives::Signedness::Signed) => Monotype::Int64,
                    Some(crate::primitives::Signedness::Unsigned) => Monotype::UInt64,
                    None => {
                        let Failure::Unsupported(UnsupportedState::OpenType { rendered }) =
                            open_type(context, phantom)?
                        else {
                            unreachable!("invariant violated: open_type reports an open type")
                        };
                        return Err(UnsupportedState::OpenSignedness { rendered }.into());
                    }
                };
                return Ok(self.intern(monotype));
            }
            // Where the definition's signedness is known its Longs were
            // spelled `Long' Signed` or `Long' Unsigned` before conversion.
            Some(crate::primitives::KnownType::Long) => {
                return Err(UnsupportedState::UnknownSignedness.into());
            }
            _ => {}
        }

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
                let Some(&row) = arguments.first() else {
                    return Err(UnsupportedState::UnsaturatedType { name: name.to_string() }.into());
                };
                let closed = closed_row(context, row)?;
                if let Some(row) = closed {
                    self.schemes.note_variant_read(row);
                }
                if let Some(row) = closed
                    && !context.erased_variant_rows.contains(&row)
                    && self.converts_every_field(context, row, expansions)
                {
                    self.variant = Some((file_id, item));
                    let data = self.data_type(context, file_id, item, Arc::from([row]))?;
                    return Ok(self.intern(Monotype::Data(data)));
                }
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
            ("Data.Exists", "Exists") => {
                let Some(&family) = arguments.first() else {
                    return Err(UnsupportedState::UnsaturatedType { name: name.to_string() }.into());
                };
                let family = erase_newtypes(context, family, expansions, &mut vec![])?;
                if context.types.contains_erased(family) {
                    Monotype::Erased(Erasure::Existential)
                } else if let Some(erasure) = self.schemes.family_erasure(family) {
                    Monotype::Erased(erasure)
                } else {
                    self.existential = Some((file_id, item));
                    Monotype::Data(DataType { file_id, item, arguments: Arc::from([family]) })
                }
            }
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
            ("Data.HashMap", "HashMap") => {
                self.hash_map(context, (file_id, item), &arguments, expansions)?
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
                        let data = self.data_type(context, file_id, item, Arc::from(canonical))?;
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
                    self.declared_go_type(&module, &name)?;
                    let arguments = erased_newtypes(context, arguments, expansions)?;
                    Monotype::ForeignData(DataType { file_id, item, arguments })
                }
                IndexedTypeItemKind::Data { constructors, .. } if constructors.is_empty() => {
                    let free = crate::primitives::known_type(&module.name, &name)
                        == Some(crate::primitives::KnownType::FreeValue);
                    Monotype::Erased(if free { Erasure::FreeValue } else { Erasure::EmptyData })
                }
                IndexedTypeItemKind::Data { .. } => {
                    let regular = self.is_regular(context, file_id, item)?;
                    let arguments = if regular {
                        erased_newtypes(context, arguments, expansions)?
                    } else {
                        arguments
                            .iter()
                            .map(|_| context.types.erased(Erasure::NonRegular))
                            .collect()
                    };
                    Monotype::Data(self.data_type(context, file_id, item, arguments)?)
                }
                _ if crate::foreign::is_opaque_foreign_data(&module.name, &name) => {
                    Monotype::Opaque
                }
                _ if crate::foreign::support_data(&module.name, &name).is_some()
                    || self.foreign_modules.iter().any(|provided| *provided == module.name) =>
                {
                    if crate::foreign::support_data(&module.name, &name).is_none() {
                        self.declared_go_type(&module, &name)?;
                    }
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
                return Ok(scheme
                    .filter(|scheme| scheme.constraints.is_empty())
                    .map(|scheme| scheme.key));
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
    pub(super) fn note_rank_n_field<Q>(
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
        if self.schemes.is_erased_owner(owner)
            || self.new_erased_owners.iter().any(|erased| erased == owner)
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
            let mut monotype = self.convert(context, instantiated, expansions)?;
            for reified in scheme.reified_constraints(context, &instantiation).into_iter().rev() {
                let reified = match reified_value(context, reified)? {
                    Some(ReifiedValue::Symbol) => self.intern(Monotype::String),
                    Some(ReifiedValue::Reflected(reflected)) => {
                        self.convert(context, reflected, expansions)?
                    }
                    None => return Err(UnsupportedState::UnboundEvidence.into()),
                };
                monotype = self.intern(Monotype::Function(reified, monotype));
            }
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
    /// Checks that the Go files next to the module's source declare the Go type of its foreign
    /// data type `name`: the name capitalised, with `Type` added if one of the module's values
    /// takes that name.
    fn declared_go_type(&self, module: &crate::context::ModuleData, name: &str) -> Converted<()> {
        let Some(source) =
            self.foreign_sources.iter().find(|source| *source.module == *module.name)
        else {
            return Ok(());
        };
        let mut type_name = crate::naming::capitalise(name);
        let taken = module.indexed.items.iter_terms().any(|(_, term)| {
            term.name.as_deref().is_some_and(|term| crate::naming::capitalise(term) == type_name)
        });
        if taken {
            type_name.push_str("Type");
        }
        if source.types.contains(&type_name) {
            return Ok(());
        }
        let name = format!("{}.{name}", module.name);
        let files = source.files.join(", ");
        Err(UnsupportedState::MissingGoType { name, files, type_name }.into())
    }

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
}
