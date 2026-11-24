use std::sync::Arc;

use checking::TypeId;
use checking::core::{CheckedClass, Type};
use checking::evidence::{InstanceCandidateOrigin, SuperclassId};
use checking::tree::{DeclarationAbstraction, TermDeclarationKind};
use files::FileId;
use indexing::{TermItemId, TypeItemId};
use smol_str::SmolStr;

use super::{Definition, Scope, SpecializationKey, Specializer};
use crate::dictionary::{Dictionary, InstanceDictionary, RuntimeDictionary};
use crate::erasure::Erasure;
use crate::error::{GoError, GoResult, UnsupportedState};
use crate::monomorphic::{Expression, ExpressionKind, Local};
use crate::monotype::{Monotype, MonotypeId, RecordField};
use crate::types::Substitution;

pub(super) struct Promotion {
    place: EvidencePlace,
    dictionary: Dictionary,
    constraint: TypeId,
}

/// Where a promoted dictionary sits in a specialization key: among the definition's own
/// constraints, or among the context of the instance whose member it is.
#[derive(Clone, Copy)]
enum EvidencePlace {
    Abstraction(usize),
    InstanceContext(usize),
}

struct ErasedMember {
    instantiations: Substitution,
    constraints: Vec<TypeId>,
    body: TypeId,
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
            let place = EvidencePlace::Abstraction(position);
            promotions.push(Promotion { place, dictionary, constraint });
        }
        if promotions.is_empty() {
            return Err(growing());
        }
        key.dictionaries = Arc::from(dictionaries);
        Ok(promotions)
    }

    /// The instance at its erased types, with the context dictionaries that mention an erased
    /// type passed at run time, and the dictionaries those stand for at this request.
    pub(super) fn promote_growing_context(
        &mut self,
        definition: &Definition,
        dictionary: &InstanceDictionary,
        erased_types: &[TypeId],
    ) -> GoResult<(Arc<InstanceDictionary>, Vec<Promotion>)> {
        let (module, declaration) = self.instance_declaration(dictionary.origin)?;
        let signature = module.checked.tree[declaration].type_id;
        let (names, body) = self.context.types.peel_quantifiers(signature);
        let (contexts, _) = self.context.types.peel_constraints(body);
        let TermDeclarationKind::Instance(instance) = &module.checked.tree[declaration].kind else {
            unreachable!("invariant violated: instance origin has a non-instance declaration")
        };
        let mut erased = Substitution::default();
        let mut instantiated = Substitution::default();
        for (position, (&erased_type, &requested_type)) in
            erased_types.iter().zip(dictionary.types.iter()).enumerate()
        {
            let mut variables = vec![];
            variables.extend(names.get(position).copied());
            if let Some(&rigid) = instance.rigid_parameters.get(position)
                && let Type::Rigid(name, _, _) = self.context.types.lookup(rigid)
            {
                variables.push(*name);
            }
            for name in variables {
                erased.insert(name, erased_type);
                instantiated.insert(name, requested_type);
            }
        }
        let mut context = dictionary.context.to_vec();
        let mut promotions = vec![];
        for (position, &constraint) in contexts.iter().enumerate() {
            let erased_constraint = self.context.types.substitute(constraint, &erased);
            if !self.context.types.contains_erased(erased_constraint) {
                continue;
            }
            let Some(slot) = context.get_mut(position) else {
                return Err(GoError::Unsupported {
                    definition: self.describe_definition(definition.clone())?,
                    state: UnsupportedState::GrowingEvidence,
                });
            };
            let runtime = RuntimeDictionary { constraint: erased_constraint, value: None };
            let dictionary = std::mem::replace(slot, Dictionary::Runtime(runtime));
            let constraint = self.context.types.substitute(constraint, &instantiated);
            let place = EvidencePlace::InstanceContext(position);
            promotions.push(Promotion { place, dictionary, constraint });
        }
        let instance = InstanceDictionary {
            origin: dictionary.origin,
            types: Arc::from(erased_types),
            context: Arc::from(context),
        };
        Ok((Arc::new(instance), promotions))
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
            self.note_runtime_dictionaries(&key, &promotions)?;
            let mut dictionaries = key.dictionaries.to_vec();
            let instance = match &key.definition {
                Definition::Member { dictionary, .. } => Some((**dictionary).clone()),
                Definition::Value { .. } => None,
            };
            let mut context = instance.as_ref().map(|instance| instance.context.to_vec());
            for promotion in promotions {
                let slot = match promotion.place {
                    EvidencePlace::Abstraction(position) => &mut dictionaries[position],
                    EvidencePlace::InstanceContext(position) => {
                        let context = context.as_mut().expect(
                            "invariant violated: an instance context is promoted outside a member",
                        );
                        &mut context[position]
                    }
                };
                let Dictionary::Runtime(runtime) = &*slot else {
                    unreachable!(
                        "invariant violated: a promoted dictionary is not passed at run time"
                    )
                };
                let erased = runtime.constraint;
                let value =
                    self.runtime_value(scope, promotion.dictionary, promotion.constraint, erased)?;
                let value = Some(Box::new(value));
                *slot = Dictionary::Runtime(RuntimeDictionary { constraint: erased, value });
            }
            key.dictionaries = Arc::from(dictionaries);
            if let (Some(mut instance), Some(context)) = (instance, context)
                && let Definition::Member { member, .. } = key.definition
            {
                instance.context = Arc::from(context);
                key.definition = Definition::Member { dictionary: Arc::new(instance), member };
            }
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

    /// Run-time dictionaries are slower than specialized code, so where they are used is told.
    fn note_runtime_dictionaries(
        &mut self,
        key: &SpecializationKey,
        promotions: &[Promotion],
    ) -> GoResult<()> {
        let definition = match &key.definition {
            Definition::Member { dictionary, member } => {
                let member = self.context.qualified_term_name(member.0, member.1)?;
                format!("{member} of instance {}", self.instance_head_text(dictionary.origin)?)
            }
            Definition::Value { .. } => self.describe_definition(key.definition.clone())?,
        };
        for promotion in promotions {
            let (file_id, item) = self.class_head(&definition, promotion.constraint)?;
            let class = self.context.type_name(file_id, item)?;
            let note = format!(
                "{definition} takes its {class} dictionary at run time, because polymorphic \
                 recursion reaches it at ever larger types; only this definition is slower"
            );
            if !self.runtime_dictionary_notes.contains(&note) {
                self.runtime_dictionary_notes.push(note);
            }
        }
        Ok(())
    }

    /// An instance as its declaration writes its head, `Show (Nested a)`, which names it even
    /// when the source gives it no name.
    fn instance_head_text(&mut self, origin: InstanceCandidateOrigin) -> GoResult<String> {
        let (module, declaration) = self.instance_declaration(origin)?;
        let signature = module.checked.tree[declaration].type_id;
        let (_, body) = self.context.types.peel_quantifiers(signature);
        let (_, head) = self.context.types.peel_constraints(body);
        let pretty = checking::core::pretty::Pretty::new(self.context.queries, &module.checked);
        match pretty.render(head) {
            Ok(rendered) => Ok(rendered.to_string()),
            Err(_) => Ok(self.instance_name(origin)?.to_string()),
        }
    }

    fn applied_function(
        &mut self,
        id: crate::monomorphic::FunctionId,
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

    /// A member read from a run-time dictionary, given the dictionaries for the member's own
    /// constraints at this use.
    pub(super) fn runtime_member(
        &mut self,
        scope: &mut Scope,
        runtime: RuntimeDictionary,
        (member, name): ((FileId, TermItemId), SmolStr),
        instantiations: &Substitution,
        dictionaries: Vec<Dictionary>,
        monotype: MonotypeId,
    ) -> GoResult<Expression> {
        let missing = |name: &SmolStr| UnsupportedState::MissingInstanceMember {
            member: name.to_string(),
        };
        let constraint = runtime.constraint;
        let value = runtime.value.expect("invariant violated: a run-time dictionary has no value");
        let Some(field) = self.record_field(*value, &name) else {
            return Err(self.unsupported(scope, missing(&name)));
        };
        if dictionaries.is_empty() {
            return Ok(self.coerce(field, monotype));
        }
        let class = self.class_environment(&scope.definition, constraint)?;
        let Some(declared) = class.class.members.iter().find(|declared| {
            class.file_id == member.0 && declared.item_id == member.1
        }) else {
            return Err(self.unsupported(scope, missing(&name)));
        };
        let field_type = declared.field_type;
        let erased = self.erased_member(&class, field_type, &Substitution::default());
        let instantiated = self.erased_member(&class, field_type, instantiations);
        let mut arguments = Vec::with_capacity(dictionaries.len());
        let constraints = erased.constraints.iter().zip(instantiated.constraints.iter());
        for (dictionary, (&erased, &instantiated)) in dictionaries.into_iter().zip(constraints) {
            arguments.push(self.runtime_value(scope, dictionary, instantiated, erased)?);
        }
        let mut result = field.monotype;
        for _ in &arguments {
            let Some((_, rest)) = self.monotypes.function_parts(result) else {
                return Err(self.unsupported(scope, missing(&name)));
            };
            result = rest;
        }
        let kind = ExpressionKind::Apply { function: Box::new(field), arguments };
        let applied = Expression::new(kind, result);
        Ok(self.coerce(applied, monotype))
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
            let erased_member = self.erased_member(&class, member.field_type, &Substitution::default());
            let member_monotype = self.closed_monotype(scope, erased_member.body)?;
            let field = record.iter().find(|field| field.label == label);
            let field = field.expect("invariant violated: a member is not in its dictionary");
            let mut parameters = vec![];
            let mut dictionaries = vec![];
            for &member_constraint in &erased_member.constraints {
                let monotype = self.runtime_monotype(&scope.definition, member_constraint)?;
                let parameter = self.fresh_local(SmolStr::new_static("dictionary"), monotype);
                let value = Some(Box::new(parameter.expression()));
                dictionaries.push(Dictionary::Runtime(RuntimeDictionary {
                    constraint: member_constraint,
                    value,
                }));
                parameters.push(parameter);
            }
            let reference = self.member_reference(
                scope,
                (class.file_id, member.item_id),
                Dictionary::Instance(Arc::clone(&instance)),
                &erased_member.instantiations,
                dictionaries,
                member_monotype,
            )?;
            let value =
                if parameters.is_empty() { reference } else { self.lambda(parameters, reference) };
            fields.push((label, self.coerce(value, field.monotype)));
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
            let erased = self.erased_member(&class, member.field_type, &Substitution::default());
            let monotype = self.monotypes.monotype(&mut self.context, erased.body);
            let mut monotype = monotype.map_err(|failure| failure.at(definition))?;
            for &member_constraint in erased.constraints.iter().rev() {
                if self.class_head(definition, member_constraint)? == (class.file_id, class.item) {
                    return Err(GoError::Unsupported {
                        definition: definition.to_string(),
                        state: UnsupportedState::Construct {
                            construct: "growing evidence of a class whose members require it",
                        },
                    });
                }
                let dictionary = self.runtime_monotype(definition, member_constraint)?;
                monotype = self.monotypes.function(dictionary, monotype);
            }
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

    /// A member's type in a run-time dictionary: its own type variables are those `chosen`
    /// gives, or else erased, so that one closure serves every use, and its own constraints
    /// become dictionary parameters in front of it.
    fn erased_member(
        &mut self,
        class: &ClassEnvironment,
        field_type: TypeId,
        chosen: &Substitution,
    ) -> ErasedMember {
        let member_type = self.context.types.substitute(field_type, &class.substitution);
        let (quantifiers, inner) = self.context.types.peel_quantifiers(member_type);
        let erased = self.context.types.erased(Erasure::PolymorphicRecursion);
        let instantiations: Substitution = quantifiers
            .iter()
            .map(|name| (*name, chosen.get(name).copied().unwrap_or(erased)))
            .collect();
        let inner = self.context.types.substitute(inner, &instantiations);
        let (constraints, body) = self.context.types.peel_constraints(inner);
        ErasedMember { instantiations, constraints, body }
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
