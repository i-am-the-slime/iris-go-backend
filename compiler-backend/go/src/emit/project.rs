use super::build::unit_value;
use super::{Crossing, Emitter, call, identifier_expression, returning};
use crate::error::GoResult;
use crate::foreign::{Foreign, ForeignPackages};
use crate::monomorphic::Expression;
use crate::monotype::{Monotype, MonotypeId};
use crate::syntax::{GoExpression, GoStatement, GoType};
use checking::TypeId;
use checking::core::{Name, Type};
use rustc_hash::FxHashMap;

/// How many arrows, effects and newtypes `returns_variable` looks through.
const RETURNS_VARIABLE_DEPTH: usize = 32;

impl<'q, Q> Emitter<'_, '_, 'q, Q>
where
    Q: checking::ExternalQueries,
{
    /// A call of a project's Go foreign. A quantified one without arguments is
    /// instantiated, which nothing else would tell Go: as the effect of an
    /// effectful foreign, and called for the value of any other.
    pub(super) fn project_call(
        &mut self,
        foreign: Foreign,
        arguments: &[Expression],
        out: &mut Vec<GoStatement>,
    ) -> GoResult<GoExpression> {
        let Foreign::Project { effectful, type_arguments, .. } = foreign else {
            unreachable!("invariant violated: a project call of another foreign");
        };
        let function = self.project_function(foreign)?;
        let crossing = self.project_crossing(foreign);
        if arguments.is_empty() {
            if type_arguments.is_empty() {
                return Ok(function);
            }
            let types =
                type_arguments.iter().map(|&type_| self.convention_or_native(type_, crossing));
            let arguments = types.collect::<GoResult<Vec<_>>>()?;
            let function = Box::new(function);
            let instantiated = GoExpression::Instantiation { function, arguments };
            return Ok(if effectful { instantiated } else { call(instantiated, vec![]) });
        }
        let function = self.instantiated(function, type_arguments, crossing)?;
        let generic = self.project_generic_parameters(foreign)?;
        let variable_results = self.project_variable_results(foreign)?;
        let uncurried = self.project_uncurried_parameters(foreign)?;
        let variable_effect_functions = self.project_variable_effect_functions(foreign)?;
        let erased = self.project_erased_arguments(foreign, arguments)?;
        let mut values = vec![];
        for (position, argument) in arguments.iter().enumerate() {
            let value = match uncurried.get(position).cloned().flatten() {
                Some(groups) => {
                    let value = self.grouped_value(argument, &groups, out)?;
                    match variable_effect_functions.get(&position) {
                        Some(&arity) if self.returns_unit_after(argument.monotype, arity) => {
                            self.unit_valued_uncurried(value, argument.monotype, arity, out)?
                        }
                        _ => value,
                    }
                }
                None => {
                    let generic = generic.contains(&position);
                    let erased = erased.get(&position).copied();
                    let value = self.project_argument(argument, generic, erased, crossing, out)?;
                    match variable_results.get(&position) {
                        Some(&layers) => {
                            self.unit_valued_within(value, argument.monotype, layers, out)?
                        }
                        None => value,
                    }
                }
            };
            values.push(value);
        }
        Ok(call(function, values))
    }

    fn instantiated(
        &mut self,
        function: GoExpression,
        type_arguments: &[MonotypeId],
        crossing: Crossing,
    ) -> GoResult<GoExpression> {
        if type_arguments.is_empty() {
            return Ok(function);
        }
        let types = type_arguments.iter().map(|&type_| self.convention_or_native(type_, crossing));
        let arguments = types.collect::<GoResult<Vec<_>>>()?;
        Ok(GoExpression::Instantiation { function: Box::new(function), arguments })
    }

    pub(super) fn project_crossing(&self, foreign: Foreign) -> Crossing {
        let Foreign::Project { file_id, term, .. } = foreign else {
            unreachable!("invariant violated: the crossing of another foreign");
        };
        if self.monotypes.native_foreigns.contains(&(file_id, term)) {
            return Crossing::Native;
        }
        if self.monotypes.row_free_foreigns.contains(&(file_id, term)) {
            return Crossing::BoxedWithoutRows;
        }
        Crossing::Boxed
    }

    /// A foreign's argument as its Go function takes it. Go infers a generic function's type
    /// arguments from its arguments, and an untyped integer constant as an `int`, so an `Int`
    /// constant passed for a type parameter is typed: `int32(2)`.
    fn project_argument(
        &mut self,
        argument: &Expression,
        generic: bool,
        erased: Option<MonotypeId>,
        crossing: Crossing,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<GoExpression> {
        let value = self.value(argument, out)?;
        if let Some(erased) = erased {
            let value = self.coerce(value, argument.monotype, erased, out)?;
            return self.in_convention(value, erased, crossing, out);
        }
        let value = match self.monotypes.get(argument.monotype) {
            Monotype::Int if generic => self.typed_constant(value, argument.monotype)?,
            _ if generic => self.typed_argument(value, argument)?,
            _ => value,
        };
        self.in_convention(value, argument.monotype, crossing, out)
    }

    /// The positions of a foreign's parameters whose declared type is one of its quantified
    /// variables, which its Go function takes as a type parameter. A parameter declared `Int` is
    /// an `int32` in Go, even in a generic function.
    fn project_generic_parameters(&mut self, foreign: Foreign) -> GoResult<Vec<usize>> {
        let Foreign::Project { file_id, term, .. } = foreign else {
            unreachable!("invariant violated: the declared type of another foreign");
        };
        let module = self.context.module(file_id)?;
        let Some(declared) = module.checked.lookup_term_item_type(term) else { return Ok(vec![]) };
        let declared = crate::monotype::expand_synonyms(&mut self.context, declared)?;
        let (variables, mut current) = self.context.types.peel_quantifiers(declared);
        if variables.is_empty() {
            return Ok(vec![]);
        }
        let mut generic = vec![];
        let mut position = 0;
        while let Some((parameter, result)) = self.context.types.function_parts(current) {
            let parameter = self.context.types.strip_annotations(parameter);
            let declared = self.context.types.lookup(parameter);
            if !matches!(declared, checking::core::Type::Constructor(..)) {
                generic.push(position);
            }
            position += 1;
            current = result;
        }
        Ok(generic)
    }

    /// The parameters of a foreign that return one of its quantified variables after their
    /// arrows and effects, through the newtypes that wrap them, `Effect a` or `Error -> IO a`, by
    /// position, with how many applications or performances reach the variable. Go spells such a
    /// parameter `func() A`. An `Effect Unit` of Iris's is a `func()`, which Go can't instantiate
    /// `A` from, so at `Unit` the argument returns Unit's value, `struct{}{}`.
    fn project_variable_results(&mut self, foreign: Foreign) -> GoResult<FxHashMap<usize, usize>> {
        let Foreign::Project { file_id, term, .. } = foreign else {
            unreachable!("invariant violated: the declared type of another foreign");
        };
        let module = self.context.module(file_id)?;
        let Some(declared) = module.checked.lookup_term_item_type(term) else {
            return Ok(FxHashMap::default());
        };
        let declared = crate::monotype::expand_synonyms(&mut self.context, declared)?;
        let (variables, mut current) = self.context.types.peel_quantifiers(declared);
        let mut layers_by_position = FxHashMap::default();
        if variables.is_empty() {
            return Ok(layers_by_position);
        }
        let mut position = 0;
        while let Some((parameter, result)) = self.context.types.function_parts(current) {
            if let Some(layers) = self.layers_to_variable(parameter, &variables)? {
                layers_by_position.insert(position, layers);
            }
            position += 1;
            current = result;
        }
        Ok(layers_by_position)
    }

    /// How many applications or performances a type takes to return one of the variables, as
    /// Iris's Go calls it: `a -> Effect b` is one call.
    fn layers_to_variable(
        &mut self,
        mut type_id: TypeId,
        variables: &[Name],
    ) -> GoResult<Option<usize>> {
        let mut layers = 0;
        let mut after_arrow = false;
        for _ in 0..RETURNS_VARIABLE_DEPTH {
            type_id = self.context.types.strip_annotations(type_id);
            if let Some((_, result)) = self.context.types.function_parts(type_id) {
                layers += 1;
                after_arrow = true;
                type_id = result;
                continue;
            }
            let (head, arguments) = self.context.types.spine(type_id);
            match *self.context.types.lookup(head) {
                Type::Rigid(name, _, _) if arguments.is_empty() && variables.contains(&name) => {
                    return Ok((layers > 0).then_some(layers));
                }
                Type::Constructor(file_id, item)
                    if self.context.is_type(file_id, item, "Effect", "Effect")? =>
                {
                    let [result] = arguments[..] else { return Ok(None) };
                    if !after_arrow {
                        layers += 1;
                    }
                    after_arrow = false;
                    type_id = result;
                }
                Type::Constructor(..) => {
                    match crate::monotype::newtype_unwrapped(&mut self.context, type_id)? {
                        Some(underlying) => type_id = underlying,
                        None => return Ok(None),
                    }
                }
                _ => return Ok(None),
            }
        }
        Ok(None)
    }

    /// The parameters of a foreign declared `EffectFnN … r` for one of its quantified variables
    /// `r`, by position, with their arity. Go spells such a parameter `func(…) R`, and an
    /// `EffectFnN` of Iris's that returns Unit is a `func(…)`, which Go can't instantiate `R`
    /// from, so at `Unit` the argument returns Unit's value, `struct{}{}`.
    fn project_variable_effect_functions(
        &mut self,
        foreign: Foreign,
    ) -> GoResult<FxHashMap<usize, usize>> {
        let Foreign::Project { file_id, term, .. } = foreign else {
            unreachable!("invariant violated: the declared type of another foreign");
        };
        let module = self.context.module(file_id)?;
        let Some(declared) = module.checked.lookup_term_item_type(term) else {
            return Ok(FxHashMap::default());
        };
        let declared = crate::monotype::expand_synonyms(&mut self.context, declared)?;
        let (variables, mut current) = self.context.types.peel_quantifiers(declared);
        let mut arities = FxHashMap::default();
        let mut position = 0;
        while let Some((parameter, result)) = self.context.types.function_parts(current) {
            if let Some(arity) = self.context.effect_function_arity(parameter)? {
                let (_, arguments) = self.context.types.spine(parameter);
                let returned = arguments.last().map(|&returned| {
                    let returned = self.context.types.strip_annotations(returned);
                    self.context.types.lookup(returned).clone()
                });
                if let Some(Type::Rigid(name, _, _)) = returned
                    && variables.contains(&name)
                {
                    arities.insert(position, arity);
                }
            }
            position += 1;
            current = result;
        }
        Ok(arities)
    }

    fn returns_unit_after(&self, monotype: MonotypeId, arity: usize) -> bool {
        let mut current = monotype;
        for _ in 0..arity {
            let Some((_, result)) = self.monotypes.function_parts(current) else { return false };
            current = result;
        }
        self.is_unit(self.monotypes.effect_result(current).unwrap_or(current))
    }

    /// The uncurried callback, returning Unit's value after it performs.
    fn unit_valued_uncurried(
        &mut self,
        callback: GoExpression,
        monotype: MonotypeId,
        arity: usize,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<GoExpression> {
        let callback = self.shared(callback, "function", out);
        let (parameters, _) = self.fresh_parameters(monotype, arity)?;
        let arguments = parameters.iter().map(|(name, _)| identifier_expression(name)).collect();
        Ok(GoExpression::Function {
            parameters,
            result: Some(GoType::EmptyStruct),
            body: vec![
                GoStatement::Expression(call(callback, arguments)),
                GoStatement::Return(Some(unit_value())),
            ],
        })
    }

    pub(super) fn project_takes_polymorphic_arguments(
        &mut self,
        foreign: Foreign,
    ) -> GoResult<bool> {
        let Foreign::Project { file_id, term, .. } = foreign else {
            unreachable!("invariant violated: the declared type of another foreign");
        };
        let module = self.context.module(file_id)?;
        let Some(declared) = module.checked.lookup_term_item_type(term) else { return Ok(false) };
        let declared = crate::monotype::expand_synonyms(&mut self.context, declared)?;
        let (_, inner) = self.context.types.peel_quantifiers(declared);
        Ok(self.context.types.quantifies_within(inner))
    }

    pub(super) fn project_result(
        &mut self,
        foreign: Foreign,
        called: GoExpression,
        monotype: MonotypeId,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<GoExpression> {
        let crossing = self.project_crossing(foreign);
        let value = self.out_of_convention(called, monotype, crossing, out)?;
        if !matches!(self.monotypes.get(monotype), Monotype::Data(_))
            || !self.project_takes_polymorphic_arguments(foreign)?
        {
            return Ok(value);
        }
        let erased = self.canonical(monotype)?;
        self.coerce(value, erased, monotype, out)
    }

    fn project_erased_arguments(
        &mut self,
        foreign: Foreign,
        arguments: &[Expression],
    ) -> GoResult<FxHashMap<usize, MonotypeId>> {
        let Foreign::Project { file_id, term, .. } = foreign else {
            unreachable!("invariant violated: the declared type of another foreign");
        };
        let mut erased = FxHashMap::default();
        let module = self.context.module(file_id)?;
        let Some(declared) = module.checked.lookup_term_item_type(term) else { return Ok(erased) };
        let declared = crate::monotype::expand_synonyms(&mut self.context, declared)?;
        let (variables, inner) = self.context.types.peel_quantifiers(declared);
        let parameters = self.declared_parameters(inner)?;
        if variables.is_empty() || parameters.len() != arguments.len() {
            return Ok(erased);
        }
        let (polymorphic, monomorphic): (Vec<_>, Vec<_>) = parameters
            .into_iter()
            .zip(arguments)
            .enumerate()
            .partition(|(_, (parameter, _))| self.context.types.quantifies_within(*parameter));
        let mut shared = vec![];
        for (_, (parameter, _)) in polymorphic {
            self.applied_variables(parameter, &variables, &mut shared);
        }
        if shared.is_empty() {
            return Ok(erased);
        }
        for (position, (parameter, argument)) in monomorphic {
            let monotype = self.erased_where_shared(parameter, argument.monotype, &shared)?;
            if monotype != argument.monotype {
                erased.insert(position, monotype);
            }
        }
        Ok(erased)
    }

    fn declared_parameters(&mut self, mut current: TypeId) -> GoResult<Vec<TypeId>> {
        let mut parameters = vec![];
        loop {
            if let Some(arity) = self.context.uncurried_function_arity(current)? {
                let (_, arguments) = self.context.types.spine(current);
                parameters.extend(arguments.into_iter().take(arity));
                return Ok(parameters);
            }
            let Some((parameter, result)) = self.context.types.function_parts(current) else {
                return Ok(parameters);
            };
            parameters.push(parameter);
            current = result;
        }
    }

    fn applied_variables(&self, type_id: TypeId, variables: &[Name], found: &mut Vec<Name>) {
        let type_id = self.context.types.strip_annotations(type_id);
        match *self.context.types.lookup(type_id) {
            Type::Application(function, argument) => {
                let (head, _) = self.context.types.spine(type_id);
                if let Type::Rigid(name, _, _) = *self.context.types.lookup(head)
                    && variables.contains(&name)
                    && !found.contains(&name)
                {
                    found.push(name);
                }
                self.applied_variables(function, variables, found);
                self.applied_variables(argument, variables, found);
            }
            Type::Function(parameter, result) => {
                self.applied_variables(parameter, variables, found);
                self.applied_variables(result, variables, found);
            }
            Type::Forall(_, inner) | Type::Constrained(_, inner) => {
                self.applied_variables(inner, variables, found);
            }
            _ => {}
        }
    }

    fn erased_where_shared(
        &mut self,
        declared: TypeId,
        monotype: MonotypeId,
        shared: &[Name],
    ) -> GoResult<MonotypeId> {
        let (head, arguments) = self.context.types.spine(declared);
        if let Type::Rigid(name, _, _) = *self.context.types.lookup(head)
            && shared.contains(&name)
            && !arguments.is_empty()
        {
            return match self.monotypes.get(monotype) {
                Monotype::Data(_) | Monotype::Recursive(_) => self.canonical(monotype),
                _ => Ok(monotype),
            };
        }
        match (self.monotypes.get(monotype).clone(), &arguments[..]) {
            (Monotype::Function(from, to), _) => {
                let Some((parameter, result)) = self.context.types.function_parts(declared) else {
                    return Ok(monotype);
                };
                let from = self.erased_where_shared(parameter, from, shared)?;
                let to = self.erased_where_shared(result, to, shared)?;
                Ok(self.monotypes.intern(Monotype::Function(from, to)))
            }
            (Monotype::Array(element), &[declared_element]) => {
                let element = self.erased_where_shared(declared_element, element, shared)?;
                Ok(self.monotypes.intern(Monotype::Array(element)))
            }
            _ => Ok(monotype),
        }
    }

    fn project_uncurried_parameters(
        &mut self,
        foreign: Foreign,
    ) -> GoResult<Vec<Option<Vec<usize>>>> {
        let Foreign::Project { file_id, term, .. } = foreign else {
            unreachable!("invariant violated: the declared type of another foreign");
        };
        let module = self.context.module(file_id)?;
        let Some(declared) = module.checked.lookup_term_item_type(term) else { return Ok(vec![]) };
        let declared = crate::monotype::expand_synonyms(&mut self.context, declared)?;
        let (_, mut current) = self.context.types.peel_quantifiers(declared);
        let mut uncurried = vec![];
        while let Some((parameter, result)) = self.context.types.function_parts(current) {
            uncurried.push(self.context.argument_groups(parameter)?);
            current = result;
        }
        Ok(uncurried)
    }

    /// The Go function of a foreign package that implements a foreign import.
    fn project_function(&mut self, foreign: Foreign) -> GoResult<GoExpression> {
        let Foreign::Project { file_id, term, effectful, .. } = foreign else {
            unreachable!("invariant violated: a project function of another foreign");
        };
        let module_name = self.context.module(file_id)?.name.clone();
        let name = self.context.term_name(file_id, term)?;
        self.imports.insert(self.foreign_packages.import_path(&module_name));
        let package = ForeignPackages::package_name(&module_name);
        let name = crate::naming::exported(&name);
        if effectful {
            self.effects.insert((package.clone(), name.clone()));
        }
        Ok(GoExpression::Qualified { package, name })
    }

    /// The effect of an effectful foreign applied to its arguments, not yet performed: a
    /// function that calls the foreign. The arguments are evaluated now, as the effect value is
    /// made.
    pub(super) fn project_effect(
        &mut self,
        foreign: Foreign,
        arguments: &[Expression],
        monotype: MonotypeId,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<GoExpression> {
        let Foreign::Project { type_arguments, .. } = foreign else {
            unreachable!("invariant violated: a project effect of another foreign");
        };
        let crossing = self.project_crossing(foreign);
        let function = self.project_function(foreign)?;
        let function = self.instantiated(function, type_arguments, crossing)?;
        let generic = self.project_generic_parameters(foreign)?;
        let erased = self.project_erased_arguments(foreign, arguments)?;
        let mut bound = Vec::with_capacity(arguments.len());
        for (position, argument) in arguments.iter().enumerate() {
            let generic = generic.contains(&position);
            let erased = erased.get(&position).copied();
            let value = self.project_argument(argument, generic, erased, crossing, out)?;
            let base = self.value_base(argument.monotype);
            let name = self.temporary(&base);
            out.push(GoStatement::Define { names: vec![name.clone()], values: vec![value] });
            bound.push(identifier_expression(&name));
        }
        let inner = self
            .monotypes
            .effect_result(monotype)
            .expect("invariant violated: an effectful foreign returns an effect");
        let result = self.convention_result(inner, crossing)?;
        let body = vec![returning(call(function, bound), result.is_some())];
        let thunk = GoExpression::Function { parameters: vec![], result, body };
        self.out_of_convention(thunk, monotype, crossing, out)
    }
}
