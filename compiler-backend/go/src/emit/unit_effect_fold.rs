use super::{Emitter, call, identifier_expression};
use crate::error::GoResult;
use crate::monomorphic::Expression;
use crate::monotype::{Monotype, MonotypeId};
use crate::syntax::{GoExpression, GoStatement};

impl<'q, Q> Emitter<'_, '_, 'q, Q>
where
    Q: checking::ExternalQueries,
{
    /// A left fold in Effect whose accumulator is an `Effect Unit`, a `func()` that Go's generic
    /// `direct.FoldlEffect` cannot take: the effect each element's step builds from the one
    /// before, as a loop that leaves the last of them.
    pub(super) fn unit_effect_fold(
        &mut self,
        arguments: &[Expression],
        monotype: MonotypeId,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<Option<GoExpression>> {
        let Monotype::Effect(result) = *self.monotypes.get(monotype) else { return Ok(None) };
        if !matches!(self.monotypes.get(result), Monotype::Unit) {
            return Ok(None);
        }
        let step = self.uncurried_callback(&arguments[0], 2, true, out)?;
        let step = self.hoist(step, "step", out);
        let initial = self.value(&arguments[1], out)?;
        let elements = self.value(&arguments[2], out)?;
        let elements = self.hoist(elements, "elements", out);
        let accumulator = self.temporary("accumulator");
        out.push(GoStatement::Define { names: vec![accumulator.clone()], values: vec![initial] });
        let element = self.temporary("element");
        let previous = self.temporary("previous");
        let previous_value = identifier_expression(&previous);
        let stepped = call(step, vec![previous_value, identifier_expression(&element)]);
        let chained = GoExpression::Function {
            parameters: vec![],
            result: None,
            body: vec![GoStatement::Expression(stepped)],
        };
        let body = vec![
            GoStatement::Define {
                names: vec![previous],
                values: vec![identifier_expression(&accumulator)],
            },
            GoStatement::Assign {
                targets: vec![identifier_expression(&accumulator)],
                values: vec![chained],
            },
        ];
        out.push(GoStatement::Range { index: None, element, iterable: elements, body });
        Ok(Some(identifier_expression(&accumulator)))
    }
}
