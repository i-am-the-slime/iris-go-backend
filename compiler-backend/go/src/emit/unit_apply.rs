use super::build::binary;
use super::{Emitter, call, identifier_expression, length};
use crate::error::GoResult;
use crate::monomorphic::Expression;
use crate::monotype::{Monotype, MonotypeId};
use crate::syntax::{GoExpression, GoStatement};

impl<'q, Q> Emitter<'_, '_, 'q, Q>
where
    Q: checking::ExternalQueries,
{
    /// `functions <*> values` where the functions return Unit, whose Go functions return nothing,
    /// so Go's generic `array.Apply` cannot take them: every function applied to every value in
    /// turn, and one Unit for each application.
    pub(super) fn unit_apply(
        &mut self,
        arguments: &[Expression],
        monotype: MonotypeId,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<Option<GoExpression>> {
        let Monotype::Array(applied) = *self.monotypes.get(monotype) else { return Ok(None) };
        let Monotype::Array(function_monotype) = *self.monotypes.get(arguments[0].monotype) else {
            return Ok(None);
        };
        if !matches!(self.monotypes.get(applied), Monotype::Unit) {
            return Ok(None);
        }
        let functions = self.value(&arguments[0], out)?;
        let functions = self.hoist(functions, "functions", out);
        let values = self.value(&arguments[1], out)?;
        let values = self.hoist(values, "values", out);
        let units = self.temporary("units");
        let array_type = self.go_type(monotype)?;
        let count = binary("*", length(functions.clone()), length(values.clone()));
        let made = call(identifier_expression("make"), vec![GoExpression::Type(array_type), count]);
        out.push(GoStatement::Define { names: vec![units.clone()], values: vec![made] });
        let function = self.temporary("function");
        let value = self.temporary("value");
        let callable = self.value_callable(identifier_expression(&function), function_monotype);
        let mut body = vec![];
        let application =
            self.apply_arguments(callable, vec![identifier_expression(&value)], &mut body)?;
        body.push(GoStatement::Expression(application));
        let inner = GoStatement::Range { index: None, element: value, iterable: values, body };
        out.push(GoStatement::Range {
            index: None,
            element: function,
            iterable: functions,
            body: vec![inner],
        });
        Ok(Some(identifier_expression(&units)))
    }
}
