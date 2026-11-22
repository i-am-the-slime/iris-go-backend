use super::{Emitter, call, identifier_expression, returning};
use crate::error::GoResult;
use crate::foreign::{Foreign, ForeignPackages};
use crate::monomorphic::Expression;
use crate::monotype::{Monotype, MonotypeId};
use crate::naming::capitalise;
use crate::syntax::{GoExpression, GoStatement};

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
        if arguments.is_empty() {
            if type_arguments.is_empty() {
                return Ok(function);
            }
            let types = type_arguments.iter().map(|&type_| self.convention_or_native(type_));
            let arguments = types.collect::<GoResult<Vec<_>>>()?;
            let function = Box::new(function);
            let instantiated = GoExpression::Instantiation { function, arguments };
            return Ok(if effectful { instantiated } else { call(instantiated, vec![]) });
        }
        let generic = self.project_generic_parameters(foreign)?;
        let uncurried = self.project_uncurried_parameters(foreign)?;
        let mut values = vec![];
        for (position, argument) in arguments.iter().enumerate() {
            let value = match uncurried.get(position).cloned().flatten() {
                Some(groups) => self.grouped_value(argument, &groups, out)?,
                None => self.project_argument(argument, generic.contains(&position), out)?,
            };
            values.push(value);
        }
        Ok(call(function, values))
    }

    /// A foreign's argument as its Go function takes it. Go infers a generic function's type
    /// arguments from its arguments, and an untyped integer constant as an `int`, so an `Int`
    /// constant passed for a type parameter is typed: `int32(2)`.
    fn project_argument(
        &mut self,
        argument: &Expression,
        generic: bool,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<GoExpression> {
        let value = self.value(argument, out)?;
        let value = match self.monotypes.get(argument.monotype) {
            Monotype::Int if generic => self.typed_constant(value, argument.monotype)?,
            _ if generic => self.typed_argument(value, argument)?,
            _ => value,
        };
        self.in_convention(value, argument.monotype, out)
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
        let function = self.project_function(foreign)?;
        let generic = self.project_generic_parameters(foreign)?;
        let mut bound = Vec::with_capacity(arguments.len());
        for (position, argument) in arguments.iter().enumerate() {
            let value = self.project_argument(argument, generic.contains(&position), out)?;
            let base = self.value_base(argument.monotype);
            let name = self.temporary(&base);
            out.push(GoStatement::Define { names: vec![name.clone()], values: vec![value] });
            bound.push(identifier_expression(&name));
        }
        let inner = self
            .monotypes
            .effect_result(monotype)
            .expect("invariant violated: an effectful foreign returns an effect");
        let result = self.convention_result(inner)?;
        let body = vec![returning(call(function, bound), result.is_some())];
        let thunk = GoExpression::Function { parameters: vec![], result, body };
        self.out_of_convention(thunk, monotype, out)
    }
}
