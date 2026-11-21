use std::sync::Arc;

use checking::TypeId;
use files::FileId;
use indexing::TermItemId;
use smol_str::SmolStr;

use super::{Scope, Specializer};
use crate::erasure::Erasure;
use crate::error::{GoResult, UnsupportedState};
use crate::mono::{Alternative, Expression, ExpressionKind, Guarded, Pattern, PatternKind};
use crate::monotype::{DataType, Monotype, MonotypeId, RecordField};
use crate::primitives::Primitive;
use crate::scheme::{SCHEME_INSTANTIATION_LIMIT, SchemeInstantiation, SchemeKey, rank_n_scheme};
use crate::types::Substitution;

const WITNESS_LIMIT: usize = SCHEME_INSTANTIATION_LIMIT / 2;

const PENDING: &str = "existential family grown in this pass";

impl<'q, Q> Specializer<'q, Q>
where
    Q: checking::ExternalQueries,
{
    pub(super) fn primitive(
        &mut self,
        scope: &Scope,
        primitive: Primitive,
        (file_id, term): (FileId, TermItemId),
        types: &[TypeId],
        instantiations: &Substitution,
        monotype: MonotypeId,
    ) -> GoResult<Option<Expression>> {
        match (primitive, types) {
            (Primitive::MakeExists, &[.., family, witness]) => {
                self.make_exists(scope, family, witness, monotype)
            }
            (Primitive::RunExists, &[.., family, _]) => {
                let continuation = self.continuation_type((file_id, term), 0, instantiations)?;
                self.run_exists(scope, family, continuation, monotype)
            }
            (Primitive::MakeExists | Primitive::RunExists, _) => Ok(None),
            (Primitive::ReifyType, _) => {
                self.reify_type(scope, (file_id, term), instantiations, monotype)
            }
            (Primitive::ToSigned | Primitive::ToUnsigned, _) => Ok(self.int64_conversion(monotype)),
            _ => self.variant_primitive(scope, primitive, types, monotype),
        }
    }

    fn make_exists(
        &mut self,
        scope: &Scope,
        family: TypeId,
        witness: TypeId,
        monotype: MonotypeId,
    ) -> GoResult<Option<Expression>> {
        let Some((payload, existential)) = self.monotypes.function_parts(monotype) else {
            return Ok(None);
        };
        let Some(data) = self.existential_data(existential) else { return Ok(None) };
        let family = crate::monotype::data_argument(&mut self.context, family)?;
        let witness = crate::monotype::data_argument(&mut self.context, witness)?;
        let Some(index) = self.witness(scope, family, witness)? else {
            return Ok(Some(self.pending(monotype)));
        };
        let constructors = self
            .monotypes
            .constructors(&mut self.context, &data)
            .map_err(|failure| failure.at(&scope.definition))?;
        let field = constructors[index].fields[0];
        let parameter = self.fresh_local(self.monotypes.value_name(payload), payload);
        let argument = self.coerce(parameter.expression(), field);
        let kind =
            ExpressionKind::Construct { data, constructor: index, arguments: vec![argument] };
        let body = Expression::new(kind, existential);
        Ok(Some(self.lambda(vec![parameter], body)))
    }

    fn run_exists(
        &mut self,
        scope: &Scope,
        family: TypeId,
        continuation: TypeId,
        monotype: MonotypeId,
    ) -> GoResult<Option<Expression>> {
        let Some((continuation_monotype, rest)) = self.monotypes.function_parts(monotype) else {
            return Ok(None);
        };
        let Some((existential, result)) = self.monotypes.function_parts(rest) else {
            return Ok(None);
        };
        let Some(data) = self.existential_data(existential) else { return Ok(None) };
        let family = crate::monotype::data_argument(&mut self.context, family)?;
        let Some(scheme) = rank_n_scheme(&mut self.context, continuation)? else {
            return Ok(None);
        };
        let key = scheme.key;
        if self.is_erased_family(family) {
            return Ok(Some(self.pending(monotype)));
        }
        if self.monotypes.schemes.continuation_family(&key) != Some(family) {
            self.monotypes.schemes.add_continuation(family, key.clone());
            self.specialize_continuation(scope, family, &key)?;
            self.grown = true;
            return Ok(Some(self.pending(monotype)));
        }
        self.specialize_continuation(scope, family, &key)?;
        self.note_construction(&key);
        let witnesses = self.monotypes.schemes.witnesses(family).to_vec();
        let fields = match self.continuation_fields(continuation_monotype) {
            Some(fields) => fields,
            None if witnesses.is_empty() => Arc::from([]),
            None => return self.pending_or_unsupported(scope, monotype),
        };
        let constructors = self
            .monotypes
            .constructors(&mut self.context, &data)
            .map_err(|failure| failure.at(&scope.definition))?;
        let handler = self.fresh_local(SmolStr::new_static("handler"), continuation_monotype);
        let value = self.fresh_local(self.monotypes.value_name(existential), existential);
        let mut alternatives = Vec::with_capacity(witnesses.len());
        for (index, witness) in witnesses.iter().enumerate() {
            let Some(instantiation) = self.monotypes.schemes.find(&key, &witness.types) else {
                return self.pending_or_unsupported(scope, monotype);
            };
            let label = instantiation.label.clone();
            let Some(field) = fields.iter().find(|field| field.label == label) else {
                return self.pending_or_unsupported(scope, monotype);
            };
            let Some((parameter, answer)) = self.monotypes.function_parts(field.monotype) else {
                return self.pending_or_unsupported(scope, monotype);
            };
            let payload = constructors[index].fields[0];
            let hidden = self.fresh_local(self.monotypes.value_name(payload), payload);
            let function = ExpressionKind::Access { record: Box::new(handler.expression()), label };
            let function = Expression::new(function, field.monotype);
            let argument = self.coerce(hidden.expression(), parameter);
            let kind =
                ExpressionKind::Apply { function: Box::new(function), arguments: vec![argument] };
            let applied = self.coerce(Expression::new(kind, answer), result);
            let arguments =
                vec![Pattern { kind: PatternKind::Variable(hidden), monotype: payload }];
            let pattern =
                PatternKind::Constructor { data: data.clone(), constructor: index, arguments };
            let patterns = vec![Pattern { kind: pattern, monotype: existential }];
            let body = Guarded::Unconditional(applied);
            alternatives.push(Alternative { patterns, body, position: None });
        }
        let scrutinees = vec![value.expression()];
        if alternatives.is_empty() {
            alternatives.push(Alternative::match_failure(&scrutinees, result));
        }
        let body = Expression::new(ExpressionKind::Case { scrutinees, alternatives }, result);
        Ok(Some(self.lambda(vec![handler, value], body)))
    }

    /// The type of a primitive's argument at `position`, its continuation, in the primitive's
    /// signature closed by the reference's instantiations.
    pub(super) fn continuation_type(
        &mut self,
        (file_id, term): (FileId, TermItemId),
        position: usize,
        instantiations: &Substitution,
    ) -> GoResult<TypeId> {
        let module = self.context.module(file_id)?;
        let declared = module.checked.lookup_term_item_type(term).ok_or_else(|| {
            crate::error::GoError::unsupported_construct("a primitive without its signature")
        })?;
        let mut declared = self.outer_body(declared, &mut vec![]);
        declared = self.context.types.substitute(declared, instantiations);
        let without = || crate::error::GoError::unsupported_construct("a primitive's continuation");
        for _ in 0..position {
            declared = self.context.types.function_parts(declared).ok_or_else(without)?.1;
        }
        Ok(self.context.types.function_parts(declared).ok_or_else(without)?.0)
    }

    fn existential_data(&self, monotype: MonotypeId) -> Option<DataType> {
        match self.monotypes.get(monotype) {
            Monotype::Data(data) if self.monotypes.exists_family(data).is_some() => {
                Some(data.clone())
            }
            _ => None,
        }
    }

    fn continuation_fields(&self, monotype: MonotypeId) -> Option<Arc<[RecordField]>> {
        if !self.monotypes.is_instantiated_record(monotype) {
            return None;
        }
        match self.monotypes.get(monotype) {
            Monotype::Record(fields) => Some(Arc::clone(fields)),
            _ => None,
        }
    }

    fn witness(
        &mut self,
        scope: &Scope,
        family: TypeId,
        witness: TypeId,
    ) -> GoResult<Option<usize>> {
        if self.is_erased_family(family) {
            return Ok(None);
        }
        let witnesses = self.monotypes.schemes.witnesses(family);
        let requested = self.context.types.without_causes(witness);
        let known_witness = |known: &SchemeInstantiation| {
            self.context.types.without_causes(known.types[0]) == requested
        };
        if let Some(index) = witnesses.iter().position(known_witness) {
            return Ok(Some(index));
        }
        if witnesses.len() >= WITNESS_LIMIT || self.grows_family(family, witness) {
            self.erase_family(family, Erasure::UnboundedWitnesses);
            return Ok(None);
        }
        let labels: Vec<SmolStr> = witnesses.iter().map(|known| known.label.clone()).collect();
        let index = labels.len();
        let label = self.fresh_instantiation_label(&[witness], &labels)?;
        let instantiation =
            SchemeInstantiation { types: Arc::from([witness]), dictionaries: Arc::from([]), label };
        self.monotypes.schemes.add_witness(family, instantiation);
        self.grown = true;
        for key in self.monotypes.schemes.continuations(family).to_vec() {
            self.specialize_continuation(scope, family, &key)?;
        }
        Ok(Some(index))
    }

    fn specialize_continuation(
        &mut self,
        scope: &Scope,
        family: TypeId,
        key: &SchemeKey,
    ) -> GoResult<()> {
        for witness in self.monotypes.schemes.witnesses(family).to_vec() {
            if self.monotypes.schemes.find(key, &witness.types).is_some() {
                continue;
            }
            let types = witness.types.to_vec();
            self.discover_labelled(scope, key.clone(), types, vec![], Some(witness.label))?;
        }
        Ok(())
    }

    fn grows_family(&self, family: TypeId, witness: TypeId) -> bool {
        self.constructing.iter().any(|(key, enclosing)| {
            self.monotypes.schemes.continuation_family(key) == Some(family)
                && enclosing
                    .first()
                    .is_some_and(|&enclosing| self.context.types.grows(witness, enclosing))
        })
    }

    fn is_erased_family(&self, family: TypeId) -> bool {
        self.monotypes.schemes.family_erasure(family).is_some()
            || self.erased_families.iter().any(|(erased, _)| *erased == family)
    }

    pub(super) fn erase_family(&mut self, family: TypeId, erasure: Erasure) {
        if self.is_erased_family(family) {
            return;
        }
        self.erased_families.push((family, erasure));
        self.grown = true;
    }

    fn pending(&mut self, monotype: MonotypeId) -> Expression {
        self.note_pending();
        Expression::new(ExpressionKind::Fail(SmolStr::new_static(PENDING)), monotype)
    }

    fn pending_or_unsupported(
        &mut self,
        scope: &Scope,
        monotype: MonotypeId,
    ) -> GoResult<Option<Expression>> {
        if self.grown {
            return Ok(Some(self.pending(monotype)));
        }
        Err(self.unsupported(
            scope,
            UnsupportedState::Construct { construct: "runExists without its continuations" },
        ))
    }

    pub(super) fn note_crossings(&mut self, from: MonotypeId, to: MonotypeId) {
        if from == to || !self.crossings.insert((from, to)) {
            return;
        }
        match (self.monotypes.get(from).clone(), self.monotypes.get(to).clone()) {
            (Monotype::Data(source), Monotype::Data(target))
                if self.monotypes.variant_row(&source).is_some()
                    && self.monotypes.variant_row(&target).is_some() =>
            {
                self.note_variant_crossing(&source, &target);
            }
            (Monotype::Record(_), Monotype::Data(target))
                if self.monotypes.variant_row(&target).is_some() =>
            {
                self.note_variant_narrowing(&target);
            }
            (Monotype::Data(source), Monotype::Data(target)) => {
                let families =
                    (self.monotypes.exists_family(&source), self.monotypes.exists_family(&target));
                match families {
                    (None, None)
                        if (source.file_id, source.item) == (target.file_id, target.item) =>
                    {
                        self.note_field_crossings(&source, &target)
                    }
                    (None, None) => {}
                    (source, target) => {
                        for family in [source, target].into_iter().flatten() {
                            self.erase_family(family, Erasure::Existential);
                        }
                    }
                }
            }
            (Monotype::Data(source), Monotype::Erased(_) | Monotype::Opaque)
                if self.monotypes.exists_family(&source).is_some() =>
            {
                for payload in self.payloads(&source) {
                    self.note_crossings(payload, to);
                }
            }
            (Monotype::Erased(_) | Monotype::Opaque, Monotype::Data(target))
                if let Some(family) = self.monotypes.exists_family(&target) =>
            {
                self.erase_family(family, Erasure::Existential);
            }
            (Monotype::Erased(_) | Monotype::Opaque, Monotype::Erased(_) | Monotype::Opaque) => {}
            (_, Monotype::Erased(_) | Monotype::Opaque) => {
                let canonical = self.canonical(from);
                self.note_crossings(from, canonical);
            }
            (Monotype::Erased(_) | Monotype::Opaque, _) => {
                let canonical = self.canonical(to);
                self.note_crossings(canonical, to);
            }
            (Monotype::Recursive(data), _) => {
                if let Ok(unfolded) = self.monotypes.unfold(&mut self.context, &data) {
                    self.note_crossings(unfolded, to);
                }
            }
            (_, Monotype::Recursive(data)) => {
                if let Ok(unfolded) = self.monotypes.unfold(&mut self.context, &data) {
                    self.note_crossings(from, unfolded);
                }
            }
            (Monotype::Function(argument, result), Monotype::Function(target, answer)) => {
                self.note_crossings(target, argument);
                self.note_crossings(result, answer);
            }
            (Monotype::Function(..), Monotype::Record(fields)) => {
                for field in fields.iter() {
                    self.note_crossings(from, field.monotype);
                }
            }
            (Monotype::Record(sources), Monotype::Record(targets)) => {
                for target in targets.iter() {
                    if let Some(source) = sources.iter().find(|source| source.label == target.label)
                    {
                        self.note_crossings(source.monotype, target.monotype);
                    }
                }
            }
            (Monotype::Array(source), Monotype::Array(target))
            | (Monotype::Effect(source), Monotype::Effect(target))
            | (Monotype::Lazy(source), Monotype::Lazy(target))
            | (Monotype::ConsList(source), Monotype::ConsList(target))
            | (Monotype::Nullable(source), Monotype::Nullable(target)) => {
                self.note_crossings(source, target);
            }
            (Monotype::Reference(source), Monotype::Reference(target))
            | (Monotype::MutableArray(source), Monotype::MutableArray(target))
            | (Monotype::Object(source), Monotype::Object(target)) => {
                self.note_crossings(source, target);
                self.note_crossings(target, source);
            }
            _ => {}
        }
    }

    fn note_field_crossings(&mut self, source: &DataType, target: &DataType) {
        let constructors = (
            self.monotypes.constructors(&mut self.context, source),
            self.monotypes.constructors(&mut self.context, target),
        );
        let (Ok(sources), Ok(targets)) = constructors else { return };
        for (source, target) in sources.iter().zip(targets.iter()) {
            for (&from, &to) in source.fields.iter().zip(target.fields.iter()) {
                self.note_crossings(from, to);
            }
        }
    }

    fn payloads(&mut self, data: &DataType) -> Vec<MonotypeId> {
        let Ok(constructors) = self.monotypes.constructors(&mut self.context, data) else {
            return vec![];
        };
        constructors.iter().flat_map(|constructor| constructor.fields.iter().copied()).collect()
    }

    fn canonical(&mut self, monotype: MonotypeId) -> MonotypeId {
        let erased = self.monotypes.intern(Monotype::Erased(Erasure::Boxing));
        let canonical = match self.monotypes.get(monotype).clone() {
            Monotype::Function(..) => Monotype::Function(erased, erased),
            Monotype::Effect(_) => Monotype::Effect(erased),
            Monotype::Array(_) => Monotype::Array(erased),
            Monotype::MutableArray(_) => Monotype::MutableArray(erased),
            Monotype::Object(_) => Monotype::Object(erased),
            Monotype::Nullable(_) => Monotype::Nullable(erased),
            Monotype::Lazy(_) => Monotype::Lazy(erased),
            Monotype::ConsList(_) => Monotype::ConsList(erased),
            Monotype::Record(fields) => {
                let fields = fields
                    .iter()
                    .map(|field| RecordField { label: field.label.clone(), monotype: erased });
                Monotype::Record(fields.collect())
            }
            Monotype::Data(data) if self.monotypes.variant_row(&data).is_some() => return monotype,
            Monotype::Data(data) => Monotype::Data(self.erased_arguments(&data)),
            Monotype::Recursive(data) => Monotype::Recursive(self.erased_arguments(&data)),
            _ => return monotype,
        };
        self.monotypes.intern(canonical)
    }

    fn erased_arguments(&self, data: &DataType) -> DataType {
        let erased = self.context.types.erased(Erasure::Boxing);
        let arguments = data.arguments.iter().map(|_| erased).collect();
        DataType { file_id: data.file_id, item: data.item, arguments }
    }
}
