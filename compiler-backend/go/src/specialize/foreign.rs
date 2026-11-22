use std::sync::Arc;

use checking::TypeId;
use checking::core::Type;
use checking::tree::DeclarationAbstraction;
use files::FileId;
use indexing::TermItemId;
use smol_str::SmolStr;

use super::{Scope, Specializer};
use crate::error::{GoError, GoResult, UnsupportedState};
use crate::foreign::{Accumulator, Boundary, Foreign, ForeignPackages, Signature, Spelled};
use crate::mono::{Expression, ExpressionKind, Local};
use crate::monotype::{Monotype, MonotypeId, supported};
use crate::scheme::rank_n_scheme;
use crate::types::Substitution;

impl<'q, Q> Specializer<'q, Q>
where
    Q: checking::ExternalQueries,
{
    /// Records the records that foreign packages' structs represent: a struct named like a
    /// record synonym without parameters of its module stands for that synonym's record.
    pub fn adopt_foreign_structs(&mut self) -> GoResult<()> {
        for (module_name, struct_name) in &self.foreign_packages.structs {
            let Some(file_id) = self.context.queries.module_file(module_name) else { continue };
            let module = self.context.module(file_id)?;
            let synonym = module.indexed.items.iter_types().find_map(|(item, indexed)| {
                (indexed.name.as_deref() == Some(struct_name.as_str())).then_some(item)
            });
            let Some(synonym) = synonym.and_then(|item| module.checked.lookup_synonym(item)) else {
                continue;
            };
            if !synonym.parameters.is_empty() {
                continue;
            }
            let expansion = crate::monotype::expand_synonyms(&mut self.context, synonym.expansion)?;
            let Some(record) = supported(self.monotypes.monotype(&mut self.context, expansion))?
            else {
                continue;
            };
            if !matches!(self.monotypes.get(record), Monotype::Record(_)) {
                continue;
            }
            let uncurried = self.uncurried_fields(expansion)?;
            if !uncurried.is_empty() {
                self.monotypes.uncurried_fields.insert(record, uncurried);
            }
            let owner = (module_name.clone(), struct_name.clone());
            if let Some((other_module, other_struct)) =
                self.monotypes.foreign_records.insert(record, owner)
            {
                return Err(GoError::SharedRecordStruct {
                    first: format!(
                        "{}.{other_struct}",
                        ForeignPackages::package_name(&other_module)
                    ),
                    second: format!("{}.{struct_name}", ForeignPackages::package_name(module_name)),
                });
            }
        }
        Ok(())
    }

    fn uncurried_fields(&mut self, record: TypeId) -> GoResult<Vec<(SmolStr, Arc<[usize]>)>> {
        let (_, arguments) = self.context.types.spine(record);
        let Some(&row) = arguments.first() else { return Ok(vec![]) };
        let row = crate::monotype::expand_synonyms(&mut self.context, row)?;
        let Type::Row(row) = self.context.types.lookup(row).clone() else { return Ok(vec![]) };
        let row = self.context.queries.lookup_row_type(row).clone();
        let mut uncurried = vec![];
        for field in row.fields.iter() {
            if let Some(groups) = self.context.argument_groups(field.id)? {
                uncurried.push((field.label.clone(), Arc::from(groups)));
            }
        }
        Ok(uncurried)
    }

    pub(super) fn abstraction_types(
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
    pub(super) fn with_callback_arities(
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

    pub(super) fn accumulated_monotype(
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
        let module = self.context.module(file_id)?;
        let name = module.indexed.items[item].name.clone().unwrap_or_default();
        Ok(match (module.name.as_str(), name.as_str(), &arguments[..]) {
            ("Prim", "Int" | "Number" | "Char", []) => Spelled::Scalar,
            ("Prim", "Array", &[argument]) => Spelled::Array(Box::new(self.spelled(argument)?)),
            ("Effect", "Effect", &[argument]) => Spelled::Effect(Box::new(self.spelled(argument)?)),
            _ => Spelled::Opaque,
        })
    }

    pub(super) fn project_foreign(
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

    pub(super) fn foreign(
        &mut self,
        foreign: &'static Foreign,
        monotype: MonotypeId,
    ) -> Expression {
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
}
