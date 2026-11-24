use super::{Crossing, Emitter, call, identifier_expression, returning};
use crate::error::GoResult;
use crate::foreign::{Foreign, ForeignPackages};
use crate::monomorphic::Expression;
use crate::monotype::{Monotype, MonotypeId};
use crate::naming::capitalise;
use crate::syntax::{GoExpression, GoStatement};
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
        let mut values = vec![];
        for (position, argument) in arguments.iter().enumerate() {
            let value = match uncurried.get(position).cloned().flatten() {
                Some(groups) => self.grouped_value(argument, &groups, out)?,
                None => {
                    let generic = generic.contains(&position);
                    let value = self.project_argument(argument, generic, crossing, out)?;
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
        Crossing::native_when(self.monotypes.native_foreigns.contains(&(file_id, term)))
    }

    /// A foreign's argument as its Go function takes it. Go infers a generic function's type
    /// arguments from its arguments, and an untyped integer constant as an `int`, so an `Int`
    /// constant passed for a type parameter is typed: `int32(2)`.
    fn project_argument(
        &mut self,
        argument: &Expression,
        generic: bool,
        crossing: Crossing,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<GoExpression> {
        let value = self.value(argument, out)?;
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
        let name = capitalise(&name);
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
        let mut bound = Vec::with_capacity(arguments.len());
        for (position, argument) in arguments.iter().enumerate() {
            let generic = generic.contains(&position);
            let value = self.project_argument(argument, generic, crossing, out)?;
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
