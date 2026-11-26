use std::sync::Arc;

use checking::core::{Name, Type};
use checking::{TypeId, tree};
use files::FileId;
use indexing::{IndexedTermItemKind, TermItemId};
use smol_str::{SmolStr, format_smolstr};

use super::{LocalSource, Scope, Specializer};
use crate::dictionary::{Dictionary, Reflected};
use crate::error::{GoResult, UnsupportedState};
use crate::monomorphic::{Expression, ExpressionKind, Local};
use crate::monotype::{Monotype, MonotypeId, supported};
use crate::scheme::{
    ReifiedValue, SCHEME_INSTANTIATION_LIMIT, SchemeInstantiation, SchemeKey, constrained_scheme,
    reified_value,
};
use crate::types::Substitution;

impl<'q, Q> Specializer<'q, Q>
where
    Q: checking::ExternalQueries,
{
    pub(super) fn variable_text(&mut self, name: Name) -> GoResult<String> {
        let module = self.context.module(name.file)?;
        let text = match module.checked.lookup_name(name) {
            Some(text) => self.context.queries.lookup_smol_str(text).to_string(),
            None => name.as_text().to_string(),
        };
        Ok(text)
    }

    pub(super) fn superclass_text(
        &mut self,
        superclass: checking::evidence::SuperclassId,
    ) -> GoResult<String> {
        let module = self.context.module(superclass.file_id)?;
        let class = module.indexed.items[superclass.type_id].name.clone().unwrap_or_default();
        Ok(format!("superclass {} of {class}", superclass.member + 1))
    }

    pub(super) fn is_continuation(&mut self, scope: &Scope, expected: TypeId) -> GoResult<bool> {
        let closed = self.context.types.substitute(expected, &scope.substitution);
        let Some(scheme) = crate::scheme::rank_n_scheme(&mut self.context, closed)? else {
            return Ok(false);
        };
        Ok(self.monotypes.schemes.continuation_family(&scheme.key).is_some())
    }

    /// The type a reference node stands at. The checker gives the node the
    /// declared type and records the instantiations of its quantifiers apart,
    /// on the node, its evidence applications, and the applications of it.
    pub(super) fn instantiated_node_type(
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
        let node_type = self.context.types.substitute(node_type, &scope.substitution);
        self.without_floating_constraints(node_type)
    }

    /// The instantiations recorded at a reference and its evidence applications.
    pub(super) fn recorded_instantiations(
        &self,
        scope: &Scope,
        node: tree::ExpressionId,
    ) -> Substitution {
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
    pub(super) fn closed_instantiations(
        &self,
        scope: &Scope,
        mut recorded: Substitution,
    ) -> Substitution {
        self.context.types.close(&mut recorded);
        for argument in recorded.values_mut() {
            let closed = self.context.types.substitute(*argument, &scope.substitution);
            *argument = self.without_floating_constraints(closed);
        }
        recorded
    }

    pub(super) fn instantiated_result_monotype(
        &mut self,
        scope: &Scope,
        type_id: TypeId,
        result_instantiations: &Substitution,
    ) -> GoResult<MonotypeId> {
        let type_id = match self.floating.is_empty() {
            true => type_id,
            false => {
                let closed = self.context.types.substitute(type_id, &scope.substitution);
                self.without_floating_constraints(closed)
            }
        };
        if result_instantiations.is_empty() {
            return self.monotype(scope, type_id);
        }
        let stripped =
            self.strip_instantiated_result_quantifiers(type_id, result_instantiations)?;
        let instantiated = self.context.types.substitute(stripped, result_instantiations);
        self.monotype(scope, instantiated)
    }
    pub(super) fn coerce(
        &mut self,
        mut expression: Expression,
        monotype: MonotypeId,
    ) -> Expression {
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
    pub(super) fn changes_representation(&self, from: MonotypeId, to: MonotypeId) -> bool {
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

    pub(super) fn mentions_erased(&self, monotype: MonotypeId) -> bool {
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

    pub(super) fn is_newtype_constructor(
        &mut self,
        (file_id, term): (FileId, TermItemId),
    ) -> GoResult<bool> {
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

    pub(super) fn checked_binder_source(
        &self,
        scope: &Scope,
        binder: tree::BinderId,
    ) -> LocalSource {
        match scope.module.checked.tree[binder].source {
            tree::BinderSource::Binder(source) => LocalSource::Binder(source),
            _ => LocalSource::Checked(binder),
        }
    }

    pub(super) fn scheme_construction(
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

    pub(super) fn instantiated_local_reference(
        &mut self,
        scope: &mut Scope,
        source: LocalSource,
        instantiations: &Substitution,
        dictionaries: Vec<Dictionary>,
    ) -> GoResult<Expression> {
        let local = self.local_reference(scope, source)?;
        let closed = scope.scheme_locals.get(&source).copied();
        self.instantiated_scheme_value(scope, local, closed, instantiations, dictionaries)
    }

    pub(super) fn instantiated_scheme_value(
        &mut self,
        scope: &mut Scope,
        local: Expression,
        closed: Option<TypeId>,
        instantiations: &Substitution,
        dictionaries: Vec<Dictionary>,
    ) -> GoResult<Expression> {
        let scheme = match closed {
            Some(closed) => self.monotypes.scheme_for(&mut self.context, closed)?,
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
            let variable = self.variable_text(name)?;
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
            let monotype = match reified_value(&mut self.context, constraint)? {
                Some(ReifiedValue::Symbol) => self.monotypes.intern(Monotype::String),
                Some(ReifiedValue::Reflected(reflected)) => {
                    self.closed_monotype(scope, reflected)?
                }
                None => return Err(self.unsupported(scope, UnsupportedState::UnboundEvidence)),
            };
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

    pub(super) fn discover_labelled(
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

    pub(super) fn fresh_instantiation_label(
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

    pub(super) fn link_coerced_rank_n(
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

    pub(super) fn outer_body(&self, mut current: TypeId, names: &mut Vec<Name>) -> TypeId {
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

    pub(super) fn strip_inner_quantifiers(
        &mut self,
        type_id: TypeId,
        names: &mut Vec<Name>,
    ) -> GoResult<TypeId> {
        let type_id = crate::monotype::expand_synonyms(&mut self.context, type_id)?;
        let (bound, body) = self.context.types.peel_quantifiers(type_id);
        let (constraints, body) = self.context.types.peel_constraints(body);
        let peeled = !bound.is_empty() || !constraints.is_empty();
        names.extend(bound);
        if peeled {
            return self.strip_inner_quantifiers(body, names);
        }
        let Some((argument, result)) = self.context.types.function_parts(body) else {
            return Ok(body);
        };
        let result = self.strip_inner_quantifiers(result, names)?;
        Ok(self.context.queries.intern_type(Type::Function(argument, result)))
    }

    /// The type of a reference after the checker's implicit instantiation: the
    /// declared type with its quantifiers replaced and its constraints discharged.
    pub(super) fn instantiated_monotype(
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

    pub(super) fn declared_monotype(
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
                let variable = self.variable_text(*name)?;
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
    pub(super) fn strip_instantiated_result_quantifiers(
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
}
