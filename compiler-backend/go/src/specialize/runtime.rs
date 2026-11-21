use std::sync::Arc;

use checking::TypeId;
use checking::core::{CheckedClass, Type};
use checking::evidence::SuperclassId;
use checking::tree::{DeclarationAbstraction, TermDeclarationKind};
use files::FileId;
use indexing::TypeItemId;
use smol_str::SmolStr;

use super::{Definition, Scope, SpecializationKey, Specializer};
use crate::dictionary::{Dictionary, InstanceDictionary, RuntimeDictionary};
use crate::error::{GoError, GoResult, UnsupportedState};
use crate::mono::{Expression, ExpressionKind, Local};
use crate::monotype::{Monotype, MonotypeId, RecordField};
use crate::types::Substitution;

pub(super) struct Promotion {
    position: usize,
    dictionary: Dictionary,
    constraint: TypeId,
}

struct ClassEnvironment {
    file_id: FileId,
    item: TypeItemId,
    class: CheckedClass,
    substitution: Substitution,
}

impl<'q, Q> Specializer<'q, Q>
where
    Q: checking::ExternalQueries,
{
    pub(super) fn promote_growing_evidence(
        &mut self,
        key: &mut SpecializationKey,
        requested: &[TypeId],
    ) -> GoResult<Vec<Promotion>> {
        let definition = self.describe_definition(key.definition.clone())?;
        let growing = || GoError::Unsupported {
            definition: definition.clone(),
            state: UnsupportedState::GrowingEvidence,
        };
        let Definition::Value { file_id, term } = key.definition else { return Err(growing()) };
        let module = self.context.module(file_id)?;
        let declaration = module.checked.tree.lookup_term(term).ok_or_else(growing)?;
        let TermDeclarationKind::Value(value) = &module.checked.tree[declaration].kind else {
            return Err(growing());
        };
        let mut erased = Substitution::default();
        let mut instantiated = Substitution::default();
        let mut constraints = vec![];
        let mut types = key.types.iter().zip(requested.iter());
        for abstraction in value.abstractions.iter() {
            match abstraction {
                DeclarationAbstraction::Type { binder, rigid } => {
                    let Some((&erased_type, &requested_type)) = types.next() else {
                        return Err(growing());
                    };
                    let mut names = vec![self.context.queries.lookup_forall_binder(*binder).name];
                    if let Type::Rigid(name, _, _) = self.context.types.lookup(*rigid) {
                        names.push(*name);
                    }
                    for name in names {
                        erased.insert(name, erased_type);
                        instantiated.insert(name, requested_type);
                    }
                }
                DeclarationAbstraction::Evidence { constraint, .. } => {
                    constraints.push(*constraint)
                }
                DeclarationAbstraction::Argument => {}
            }
        }
        let mut dictionaries = key.dictionaries.to_vec();
        let mut promotions = vec![];
        for (position, &constraint) in constraints.iter().enumerate() {
            let erased_constraint = self.context.types.substitute(constraint, &erased);
            if !self.context.types.contains_erased(erased_constraint) {
                continue;
            }
            let Some(dictionary) = dictionaries.get_mut(position) else { return Err(growing()) };
            let runtime = RuntimeDictionary { constraint: erased_constraint, value: None };
            let dictionary = std::mem::replace(dictionary, Dictionary::Runtime(runtime));
            let constraint = self.context.types.substitute(constraint, &instantiated);
            promotions.push(Promotion { position, dictionary, constraint });
        }
        if promotions.is_empty() {
            return Err(growing());
        }
        key.dictionaries = Arc::from(dictionaries);
        Ok(promotions)
    }

    pub(super) fn request_reference(
        &mut self,
        scope: &mut Scope,
        key: SpecializationKey,
        name: SmolStr,
        monotype: MonotypeId,
    ) -> GoResult<Expression> {
        let (mut key, promotions) = self.terminate_growth(key)?;
        let promoted = !promotions.is_empty();
        if promoted {
            let mut dictionaries = key.dictionaries.to_vec();
            for promotion in promotions {
                let Dictionary::Runtime(runtime) = &dictionaries[promotion.position] else {
                    unreachable!(
                        "invariant violated: a promoted dictionary is not passed at run time"
                    )
                };
                let erased = runtime.constraint;
                let value =
                    self.runtime_value(scope, promotion.dictionary, promotion.constraint, erased)?;
                let value = Some(Box::new(value));
                dictionaries[promotion.position] =
                    Dictionary::Runtime(RuntimeDictionary { constraint: erased, value });
            }
            key.dictionaries = Arc::from(dictionaries);
        }
        let mut arguments = vec![];
        let key = map_key(&key, &mut |runtime| {
            if let Some(value) = &runtime.value {
                arguments.push((**value).clone());
            }
            RuntimeDictionary { constraint: runtime.constraint, value: None }
        });
        let erased = if promoted { self.erased_reference_monotype(scope, &key)? } else { None };
        let id = self.enqueue(key, name)?;
        if arguments.is_empty() {
            return Ok(Expression::new(ExpressionKind::Function(id), monotype));
        }
        let Some(erased) = erased else {
            return Ok(self.applied_function(id, arguments, monotype));
        };
        let mut parameters = vec![];
        let mut expected = monotype;
        let mut source = erased;
        while let (Some((parameter, expected_rest)), Some((erased_parameter, erased_rest))) =
            (self.monotypes.function_parts(expected), self.monotypes.function_parts(source))
        {
            let parameter = self.fresh_local(SmolStr::new_static("argument"), parameter);
            arguments.push(self.coerce(parameter.expression(), erased_parameter));
            parameters.push(parameter);
            expected = expected_rest;
            source = erased_rest;
        }
        let applied = self.applied_function(id, arguments, source);
        let applied = self.coerce(applied, expected);
        Ok(self.lambda(parameters, applied))
    }

    fn applied_function(
        &mut self,
        id: crate::mono::FunctionId,
        arguments: Vec<Expression>,
        monotype: MonotypeId,
    ) -> Expression {
        let mut function_monotype = monotype;
        for argument in arguments.iter().rev() {
            function_monotype = self.monotypes.function(argument.monotype, function_monotype);
        }
        let function = Expression::new(ExpressionKind::Function(id), function_monotype);
        let kind = ExpressionKind::Apply { function: Box::new(function), arguments };
        Expression::new(kind, monotype)
    }

    fn erased_reference_monotype(
        &mut self,
        scope: &Scope,
        key: &SpecializationKey,
    ) -> GoResult<Option<MonotypeId>> {
        let Definition::Value { file_id, term } = key.definition else { return Ok(None) };
        let module = self.context.module(file_id)?;
        let Some(declared) = module.checked.lookup_term_item_type(term) else { return Ok(None) };
        let (names, body) = self.context.types.peel_quantifiers(declared);
        if names.len() != key.types.len() {
            return Ok(None);
        }
        let (_, body) = self.context.types.peel_constraints(body);
        let substitution: Substitution = names.into_iter().zip(key.types.iter().copied()).collect();
        let closed = self.context.types.substitute(body, &substitution);
        Ok(Some(self.closed_monotype(scope, closed)?))
    }

    pub(super) fn bind_runtime_dictionaries(
        &mut self,
        key: &SpecializationKey,
        definition: &str,
    ) -> GoResult<(SpecializationKey, Vec<Local>)> {
        if !key_mentions_runtime(key) {
            return Ok((key.clone(), vec![]));
        }
        let mut constraints = vec![];
        map_key(key, &mut |runtime| {
            constraints.push(runtime.constraint);
            runtime.clone()
        });
        let mut parameters = Vec::with_capacity(constraints.len());
        for constraint in constraints {
            let monotype = self.runtime_monotype(definition, constraint)?;
            let class = self.class_environment(definition, constraint)?;
            let class =
                crate::naming::lower_first(&self.context.type_name(class.file_id, class.item)?);
            let name = smol_str::format_smolstr!("{class}Dictionary");
            parameters.push(self.fresh_local(name, monotype));
        }
        let mut next = parameters.iter();
        let key = map_key(key, &mut |runtime| {
            let parameter =
                next.next().expect("invariant violated: a run-time dictionary has no parameter");
            let value = Some(Box::new(parameter.expression()));
            RuntimeDictionary { constraint: runtime.constraint, value }
        });
        Ok((key, parameters))
    }

    /// The parameters a local specialization takes for its run-time dictionaries, which its
    /// references pass (`detach_runtime_values`), and its dictionaries bound to them.
    pub(super) fn bind_local_runtime_dictionaries(
        &mut self,
        definition: &str,
        dictionaries: &[Dictionary],
    ) -> GoResult<(Vec<Dictionary>, Vec<Local>)> {
        if !dictionaries.iter().any(mentions_runtime) {
            return Ok((dictionaries.to_vec(), vec![]));
        }
        let mut constraints = vec![];
        for dictionary in dictionaries {
            map_dictionary(dictionary, &mut |runtime| {
                constraints.push(runtime.constraint);
                runtime.clone()
            });
        }
        let mut parameters = Vec::with_capacity(constraints.len());
        for constraint in constraints {
            let monotype = self.runtime_monotype(definition, constraint)?;
            parameters.push(self.fresh_local(SmolStr::new_static("dictionary"), monotype));
        }
        let mut next = parameters.iter();
        let mut bind = |runtime: &RuntimeDictionary| {
            let parameter =
                next.next().expect("invariant violated: a run-time dictionary has no parameter");
            let value = Some(Box::new(parameter.expression()));
            RuntimeDictionary { constraint: runtime.constraint, value }
        };
        let bound = dictionaries.iter().map(|dictionary| map_dictionary(dictionary, &mut bind));
        Ok((bound.collect(), parameters))
    }

    pub(super) fn runtime_member(
        &mut self,
        scope: &Scope,
        runtime: RuntimeDictionary,
        member: SmolStr,
        monotype: MonotypeId,
    ) -> GoResult<Expression> {
        let value = runtime.value.expect("invariant violated: a run-time dictionary has no value");
        let field = self.record_field(*value, &member).ok_or_else(|| {
            self.unsupported(
                scope,
                UnsupportedState::MissingInstanceMember { member: member.to_string() },
            )
        })?;
        Ok(self.coerce(field, monotype))
    }

    pub(super) fn runtime_superclass(
        &mut self,
        definition: &str,
        runtime: RuntimeDictionary,
        superclass: SuperclassId,
    ) -> GoResult<Dictionary> {
        let class = self.class_environment(definition, runtime.constraint)?;
        let position = class.class.superclasses.iter().position(|entry| {
            entry.source_id == superclass.source_id && entry.member == superclass.member
        });
        let Some(position) = position else {
            let superclass = format!("{superclass:?}");
            return Err(GoError::Unsupported {
                definition: definition.to_string(),
                state: UnsupportedState::MissingSuperclass { superclass },
            });
        };
        let entry = &class.class.superclasses[position];
        let constraint = self.context.types.substitute(entry.constraint, &class.substitution);
        let label = self.superclass_label(definition, entry.constraint, position)?;
        let value = runtime.value.expect("invariant violated: a run-time dictionary has no value");
        let value = self.record_field(*value, &label).ok_or_else(|| GoError::Unsupported {
            definition: definition.to_string(),
            state: UnsupportedState::MissingSuperclass { superclass: label.to_string() },
        })?;
        Ok(Dictionary::Runtime(RuntimeDictionary { constraint, value: Some(Box::new(value)) }))
    }

    fn runtime_value(
        &mut self,
        scope: &mut Scope,
        dictionary: Dictionary,
        constraint: TypeId,
        erased: TypeId,
    ) -> GoResult<Expression> {
        let instance = match dictionary {
            Dictionary::Runtime(RuntimeDictionary { value: Some(value), .. }) => {
                let monotype = self.runtime_monotype(&scope.definition, erased)?;
                return Ok(self.coerce(*value, monotype));
            }
            Dictionary::Instance(instance) => instance,
            Dictionary::Symbol(_)
            | Dictionary::Reflectable(_)
            | Dictionary::Trivial
            | Dictionary::Runtime(RuntimeDictionary { value: None, .. }) => {
                return Err(self.unsupported(
                    scope,
                    UnsupportedState::Construct {
                        construct: "growing evidence of compiler-solved constraints",
                    },
                ));
            }
        };
        let monotype = self.runtime_monotype(&scope.definition, erased)?;
        let Monotype::Record(record) = self.monotypes.get(monotype).clone() else {
            unreachable!("invariant violated: a run-time dictionary is not a record")
        };
        let class = self.class_environment(&scope.definition, constraint)?;
        let erased_class = self.class_environment(&scope.definition, erased)?;
        let mut fields = vec![];
        for member in &class.class.members {
            let label = self.context.term_name(class.file_id, member.item_id)?;
            let member_type = self.context.types.substitute(member.field_type, &class.substitution);
            let member_monotype = self.closed_monotype(scope, member_type)?;
            let field = record.iter().find(|field| field.label == label);
            let field = field.expect("invariant violated: a member is not in its dictionary");
            let reference = self.member_reference(
                scope,
                (class.file_id, member.item_id),
                Dictionary::Instance(Arc::clone(&instance)),
                &Substitution::default(),
                vec![],
                member_monotype,
            )?;
            fields.push((label, self.coerce(reference, field.monotype)));
        }
        for (position, entry) in class.class.superclasses.iter().enumerate() {
            let label = self.superclass_label(&scope.definition, entry.constraint, position)?;
            let superclass = SuperclassId {
                file_id: class.file_id,
                type_id: class.item,
                source_id: entry.source_id,
                member: entry.member,
            };
            let dictionary = self.resolve_superclass(&scope.evidence(), &instance, superclass)?;
            let constraint = self.context.types.substitute(entry.constraint, &class.substitution);
            let erased =
                self.context.types.substitute(entry.constraint, &erased_class.substitution);
            fields.push((label, self.runtime_value(scope, dictionary, constraint, erased)?));
        }
        fields.sort_by(|left, right| left.0.cmp(&right.0));
        Ok(Expression::new(ExpressionKind::Record(fields), monotype))
    }

    /// The run-time dictionary of `Reflectable v t` that reflects a value known only at run
    /// time, the dictionary `Data.Reflectable.reifyType` builds.
    pub(super) fn reified_dictionary(
        &mut self,
        definition: &str,
        constraint: TypeId,
        value: Expression,
    ) -> GoResult<Dictionary> {
        let monotype = self.runtime_monotype(definition, constraint)?;
        let Monotype::Record(fields) = self.monotypes.get(monotype).clone() else {
            unreachable!("invariant violated: a run-time dictionary is not a record")
        };
        let [member] = &fields[..] else {
            return Err(GoError::Unsupported {
                definition: definition.to_string(),
                state: UnsupportedState::Construct {
                    construct: "reifying a class other than Reflectable",
                },
            });
        };
        let reflect = self.constant_function(value.kind, member.monotype);
        let record = ExpressionKind::Record(vec![(member.label.clone(), reflect)]);
        let value = Some(Box::new(Expression::new(record, monotype)));
        Ok(Dictionary::Runtime(RuntimeDictionary { constraint, value }))
    }

    fn runtime_monotype(&mut self, definition: &str, constraint: TypeId) -> GoResult<MonotypeId> {
        let class = self.class_environment(definition, constraint)?;
        let mut fields = vec![];
        for member in &class.class.members {
            let label = self.context.term_name(class.file_id, member.item_id)?;
            let member_type = self.context.types.substitute(member.field_type, &class.substitution);
            let (quantifiers, inner) = self.context.types.peel_quantifiers(member_type);
            let (constraints, _) = self.context.types.peel_constraints(inner);
            if !quantifiers.is_empty() || !constraints.is_empty() {
                return Err(GoError::Unsupported {
                    definition: definition.to_string(),
                    state: UnsupportedState::Construct {
                        construct: "growing evidence of classes with polymorphic members",
                    },
                });
            }
            let monotype = self.monotypes.monotype(&mut self.context, member_type);
            let monotype = monotype.map_err(|failure| failure.at(definition))?;
            fields.push(RecordField { label, monotype });
        }
        for (position, entry) in class.class.superclasses.iter().enumerate() {
            let label = self.superclass_label(definition, entry.constraint, position)?;
            let constraint = self.context.types.substitute(entry.constraint, &class.substitution);
            let monotype = self.runtime_monotype(definition, constraint)?;
            fields.push(RecordField { label, monotype });
        }
        fields.sort_by(|left, right| left.label.cmp(&right.label));
        let monotype = self.monotypes.intern(Monotype::Record(Arc::from(fields)));
        let spelling = (class.file_id, class.item, Arc::from([]));
        let spellings = self.monotypes.record_spellings.entry(monotype).or_default();
        if !spellings.contains(&spelling) {
            spellings.push(spelling);
        }
        Ok(monotype)
    }

    fn class_environment(
        &mut self,
        definition: &str,
        constraint: TypeId,
    ) -> GoResult<ClassEnvironment> {
        let (file_id, item) = self.class_head(definition, constraint)?;
        let module = self.context.module(file_id)?;
        let class = module.checked.lookup_class(item).ok_or_else(|| non_class(definition))?;
        let (_, arguments) = self.context.types.spine(constraint);
        let mut substitution = Substitution::default();
        for (&binder, &argument) in class.type_parameters.iter().zip(arguments.iter()) {
            substitution.insert(self.context.queries.lookup_forall_binder(binder).name, argument);
        }
        let (_, canonical) = self.context.types.spine(class.canonical);
        for (&parameter, &argument) in canonical.iter().zip(arguments.iter()) {
            if let Type::Rigid(name, _, _) = self.context.types.lookup(parameter) {
                substitution.insert(*name, argument);
            }
        }
        Ok(ClassEnvironment { file_id, item, class, substitution })
    }

    fn superclass_label(
        &mut self,
        definition: &str,
        constraint: TypeId,
        position: usize,
    ) -> GoResult<SmolStr> {
        let (file_id, item) = self.class_head(definition, constraint)?;
        let name = self.context.type_name(file_id, item)?;
        Ok(smol_str::format_smolstr!("{name}{position}"))
    }

    fn class_head(&self, definition: &str, constraint: TypeId) -> GoResult<(FileId, TypeItemId)> {
        let (head, _) = self.context.types.spine(constraint);
        match self.context.types.lookup(head) {
            &Type::Constructor(file_id, item) => Ok((file_id, item)),
            _ => Err(non_class(definition)),
        }
    }

    fn record_field(&mut self, record: Expression, label: &str) -> Option<Expression> {
        let Monotype::Record(fields) = self.monotypes.get(record.monotype) else { return None };
        let field = fields.iter().find(|field| field.label == label)?;
        let monotype = field.monotype;
        let label = field.label.clone();
        let kind = ExpressionKind::Access { record: Box::new(record), label };
        Some(Expression::new(kind, monotype))
    }
}

fn non_class(definition: &str) -> GoError {
    GoError::Unsupported {
        definition: definition.to_string(),
        state: UnsupportedState::Construct {
            construct: "growing evidence of a non-class constraint",
        },
    }
}

fn key_mentions_runtime(key: &SpecializationKey) -> bool {
    let definition = match &key.definition {
        Definition::Member { dictionary, .. } => instance_mentions_runtime(dictionary),
        Definition::Value { .. } => false,
    };
    definition || key.dictionaries.iter().any(mentions_runtime)
}

fn mentions_runtime(dictionary: &Dictionary) -> bool {
    match dictionary {
        Dictionary::Runtime(_) => true,
        Dictionary::Instance(instance) => instance_mentions_runtime(instance),
        Dictionary::Symbol(_) | Dictionary::Reflectable(_) | Dictionary::Trivial => false,
    }
}

fn instance_mentions_runtime(instance: &InstanceDictionary) -> bool {
    instance.context.iter().any(mentions_runtime)
}

fn map_key(
    key: &SpecializationKey,
    visit: &mut impl FnMut(&RuntimeDictionary) -> RuntimeDictionary,
) -> SpecializationKey {
    if !key_mentions_runtime(key) {
        return key.clone();
    }
    let definition = match &key.definition {
        Definition::Member { dictionary, member } => {
            Definition::Member { dictionary: map_instance(dictionary, visit), member: *member }
        }
        Definition::Value { file_id, term } => Definition::Value { file_id: *file_id, term: *term },
    };
    let dictionaries = key.dictionaries.iter().map(|dictionary| map_dictionary(dictionary, visit));
    let dictionaries = dictionaries.collect();
    SpecializationKey {
        definition,
        types: Arc::clone(&key.types),
        dictionaries,
        signedness: key.signedness,
    }
}

fn map_dictionary(
    dictionary: &Dictionary,
    visit: &mut impl FnMut(&RuntimeDictionary) -> RuntimeDictionary,
) -> Dictionary {
    match dictionary {
        Dictionary::Runtime(runtime) => Dictionary::Runtime(visit(runtime)),
        Dictionary::Instance(instance) => Dictionary::Instance(map_instance(instance, visit)),
        Dictionary::Symbol(_) | Dictionary::Reflectable(_) | Dictionary::Trivial => {
            dictionary.clone()
        }
    }
}

fn map_instance(
    instance: &Arc<InstanceDictionary>,
    visit: &mut impl FnMut(&RuntimeDictionary) -> RuntimeDictionary,
) -> Arc<InstanceDictionary> {
    if !instance_mentions_runtime(instance) {
        return Arc::clone(instance);
    }
    let context = instance.context.iter().map(|dictionary| map_dictionary(dictionary, visit));
    let context = context.collect();
    Arc::new(InstanceDictionary {
        origin: instance.origin,
        types: Arc::clone(&instance.types),
        context,
    })
}

/// The values of run-time dictionaries, taken out of the dictionaries that hold them: a local
/// specialization is made where the local is bound, out of reach of the values its reference
/// sees (a dictionary `reifyType` builds), so the reference passes them as arguments.
pub(super) fn detach_runtime_values(
    dictionaries: &[Dictionary],
) -> (Vec<Dictionary>, Vec<Expression>) {
    let mut values = vec![];
    let mut detach = |runtime: &RuntimeDictionary| {
        if let Some(value) = &runtime.value {
            values.push((**value).clone());
        }
        RuntimeDictionary { constraint: runtime.constraint, value: None }
    };
    let detached = dictionaries.iter().map(|dictionary| map_dictionary(dictionary, &mut detach));
    let detached = detached.collect();
    (detached, values)
}
