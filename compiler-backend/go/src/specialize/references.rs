use std::sync::Arc;

use checking::TypeId;
use checking::core::Type;
use checking::tree::{self, TermDeclarationKind};
use files::FileId;
use indexing::{IndexedTermItemKind, TermItemId};
use smol_str::SmolStr;

use super::{Definition, Reference, Scope, SpecializationKey, Specializer, int64};
use crate::dictionary::{Dictionary, Reflected};
use crate::error::{GoResult, UnsupportedState};
use crate::foreign::{self, Foreign, JsonCodec};
use crate::monomorphic::{Expression, ExpressionKind, FunctionSpelling, Literal, Local};
use crate::monotype::{Monotype, MonotypeId};
use crate::primitives::Primitive;
use crate::types::Substitution;

impl<'q, Q> Specializer<'q, Q>
where
    Q: checking::ExternalQueries,
{
    pub(super) fn global_reference(
        &mut self,
        scope: &mut Scope,
        reference: Reference,
        instantiations: &Substitution,
        dictionaries: Vec<Dictionary>,
        monotype: MonotypeId,
    ) -> GoResult<Expression> {
        let Reference { file_id, term, expression } = reference;
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
                if crate::primitives::int64_foreign(&module.name, &name).is_some() {
                    let Some(signedness) = scope.signedness else {
                        return Err(self.unsupported(scope, UnsupportedState::UnknownSignedness));
                    };
                    let foreign = foreign::int64_import(&module.name, &name, signedness)
                        .expect("invariant violated: int64_foreign lists the foreign");
                    return Ok(self.foreign(foreign, monotype));
                }
                if let Some(foreign) = foreign::foreign_import(&module.name, &name) {
                    if let Foreign::UnsafeCoerce = foreign {
                        self.link_coerced_rank_n(scope, file_id, term, instantiations)?;
                        if let Some((from, to)) = self.monotypes.function_parts(monotype) {
                            self.note_crossings(from, to);
                            self.note_coercion_site(scope, expression, from, to)?;
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
                if let Some(source) = self.foreign_packages.source(&module.name) {
                    let function = crate::naming::capitalise(&name);
                    if !source.values.contains(&function) {
                        let state = UnsupportedState::MissingGoFunction {
                            name: format!("{}.{name}", module.name),
                            files: source.files.join(", "),
                            function,
                        };
                        return Err(self.unsupported(scope, state));
                    }
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
                let codec = match crate::primitives::known(&module.name, &name) {
                    Some(Primitive::ReadJson) => Some(JsonCodec::Read),
                    Some(Primitive::WriteJson) => Some(JsonCodec::Write),
                    _ => None,
                };
                let codec = match codec {
                    Some(codec) if self.json_codec_known(codec, &dictionaries)? => Some(codec),
                    _ => None,
                };
                if codec == Some(JsonCodec::Write) {
                    return Ok(self.json_write(monotype));
                }
                if crate::primitives::known(&module.name, &name) == Some(Primitive::GenericShow)
                    && let Some(shown) = self.generic_show(scope, &dictionaries, monotype)?
                {
                    return Ok(shown);
                }
                let declared = module.checked.lookup_term_item_type(term);
                let (signedness, inherited) = self.key_signedness(scope, &types, &[], declared)?;
                let name = self.specialized_name(name, &[], &types)?;
                let name = int64::inherited_name(name, signedness.filter(|_| inherited));
                let key = SpecializationKey {
                    definition: Definition::Value { file_id, term },
                    types: Arc::from(types),
                    dictionaries: Arc::from(dictionaries),
                    signedness,
                };
                let reference = self.request_reference(scope, key, name, monotype)?;
                match codec {
                    Some(_) => Ok(self.json_read(reference)),
                    None => Ok(reference),
                }
            }
        }
    }

    pub(super) fn member_reference(
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
        let head = module.checked.tree[declaration].type_id;
        let (signedness, inherited) =
            self.key_signedness(scope, &types, &instance.types, Some(head))?;
        let head_types = self.instance_head_types(head, instance.types.is_empty());
        let name = self.specialized_name(member_name, &head_types, &instance.types)?;
        let name = int64::inherited_name(name, signedness.filter(|_| inherited));
        let key = SpecializationKey {
            definition: Definition::Member { dictionary: instance, member },
            types: Arc::from(types),
            dictionaries: Arc::from(dictionaries),
            signedness,
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
    pub(super) fn constant_function(
        &mut self,
        constant: ExpressionKind,
        monotype: MonotypeId,
    ) -> Expression {
        let Some((argument, result)) = self.monotypes.function_parts(monotype) else {
            return Expression::new(constant, monotype);
        };
        let parameter = self.fresh_local(SmolStr::new_static("proxy"), argument);
        let body = Expression::new(constant, result);
        self.lambda(vec![parameter], body)
    }

    pub(super) fn constructor(
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

    /// The types that tell an instance's members apart from another instance's: the types its
    /// head applies the class to, `Int` in `Show Int`, or where the head has variables, which the
    /// instance's types fill in, the constructors of those types, `Array` in `Show (Array a)`.
    fn instance_head_types(&mut self, head: TypeId, closed: bool) -> Vec<TypeId> {
        let (_, mut body) = self.context.types.peel_quantifiers(head);
        while let Type::Constrained(_, inner) = self.context.types.lookup(body).clone() {
            body = inner;
        }
        let arguments = self.context.types.spine(body).1.to_vec();
        if closed {
            return arguments;
        }
        arguments
            .into_iter()
            .map(|argument| self.context.types.spine(argument).0)
            .filter(|&constructor| {
                matches!(self.context.types.lookup(constructor), Type::Constructor(..))
            })
            .collect()
    }

    /// A definition's name followed by the types it is specialized at, which
    /// the emitter spells again once it has named their records.
    fn specialized_name(
        &mut self,
        name: SmolStr,
        head: &[TypeId],
        types: &[TypeId],
    ) -> GoResult<SmolStr> {
        let mut spelled = name.to_string();
        for &type_id in head.iter().chain(types) {
            self.context.type_suffix(type_id, &mut spelled)?;
        }
        let spelled = SmolStr::from(spelled);
        let spelling =
            FunctionSpelling::Specialized { name, head: Arc::from(head), types: Arc::from(types) };
        self.monotypes.function_spellings.entry(spelled.clone()).or_insert(spelling);
        Ok(spelled)
    }
}
