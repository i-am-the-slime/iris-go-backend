use super::Simplifier;
use super::choice::operation;
use crate::foreign::{self, ARRAY_UNCONS, Comparison, Foreign, Operator};
use crate::monomorphic::{Binding, Expression, ExpressionKind, Literal};
use crate::monotype::{Monotype, MonotypeId};

impl Simplifier<'_> {
    pub(super) fn unconsed(
        &mut self,
        foreign: &'static Foreign,
        arguments: Vec<Expression>,
        monotype: MonotypeId,
    ) -> Result<Expression, Vec<Expression>> {
        if !foreign.calls(ARRAY_UNCONS) {
            return Err(arguments);
        }
        let [empty, split, array] = <[Expression; 3]>::try_from(arguments)
            .unwrap_or_else(|_| unreachable!("invariant violated: uncons has three arguments"));
        let Monotype::Array(element) = *self.monotypes.get(array.monotype) else {
            unreachable!("invariant violated: uncons takes an array apart")
        };
        let integer = self.monotypes.intern(Monotype::Int);
        let boolean = self.monotypes.intern(Monotype::Boolean);
        let unit = self.monotypes.intern(Monotype::Unit);
        let array_local = self.named_local("array", array.monotype);
        let literal = |value| {
            let kind = ExpressionKind::Literal(Literal::Int(value));
            Expression::new(kind, integer)
        };
        let length = operation(Operator::ArrayLength, vec![array_local.expression()], integer);
        let compared = vec![length, literal(0)];
        let condition = operation(Operator::Compare(Comparison::Equal), compared, boolean);
        let first = vec![array_local.expression(), literal(0)];
        let head = operation(Operator::ArrayIndex, first, element);
        let tail = ExpressionKind::Foreign {
            foreign: &foreign::ARRAY_TAIL,
            arguments: vec![array_local.expression()],
        };
        let tail = Expression::new(tail, array.monotype);
        let then = self.apply(empty, vec![Expression::new(ExpressionKind::Unit, unit)], monotype);
        let otherwise = self.apply(split, vec![head, tail], monotype);
        let chosen = ExpressionKind::If {
            condition: Box::new(condition),
            then: Box::new(then),
            otherwise: Box::new(otherwise),
        };
        let chosen = Expression::new(chosen, monotype);
        Ok(self.let_bindings(vec![Binding { local: array_local, value: array }], chosen))
    }
}
