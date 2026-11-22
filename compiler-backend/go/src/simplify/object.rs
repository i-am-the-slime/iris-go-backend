use super::Simplifier;
use crate::foreign;
use crate::monomorphic::{Binding, Expression, ExpressionKind, Local, LocalId};
use crate::monotype::{Monotype, MonotypeId};

impl Simplifier<'_> {
    pub(super) fn object_fold(
        &mut self,
        arguments: Vec<Expression>,
        monotype: MonotypeId,
    ) -> Expression {
        let [bind, function, initial, object] = <[Expression; 4]>::try_from(arguments)
            .unwrap_or_else(|_| unreachable!("invariant violated: _foldM has four arguments"));
        let Monotype::Object(value) = *self.monotypes.get(object.monotype) else {
            unreachable!("invariant violated: _foldM folds an object")
        };
        let string = self.monotypes.intern(Monotype::String);
        let keys = self.monotypes.intern(Monotype::Array(string));
        let (state, _) = self
            .monotypes
            .function_parts(function.monotype)
            .expect("invariant violated: _foldM folds with a function");

        let bind = (self.named_local("bind", bind.monotype), bind);
        let function = (self.named_local("step", function.monotype), function);
        let object = (self.named_local("object", object.monotype), object);
        let accumulator = self.named_local("accumulator", monotype);
        let key = self.named_local("key", string);
        let current = self.named_local("state", state);

        let looked_up = ExpressionKind::Foreign {
            foreign: &foreign::OBJECT_INDEX,
            arguments: vec![object.0.expression(), key.expression()],
        };
        let looked_up = Expression::new(looked_up, value);
        let stepped = ExpressionKind::Apply {
            function: Box::new(function.0.expression()),
            arguments: vec![current.expression(), key.expression(), looked_up],
        };
        let stepped = Expression::new(stepped, monotype);
        let continuation = self.monotypes.function(state, monotype);
        let continuation = Expression::new(
            ExpressionKind::Lambda { parameters: vec![current], body: Box::new(stepped) },
            continuation,
        );
        let bound = ExpressionKind::Apply {
            function: Box::new(bind.0.expression()),
            arguments: vec![accumulator.expression(), continuation],
        };
        let bound = Expression::new(bound, monotype);
        let step = self.monotypes.function(string, monotype);
        let step = self.monotypes.function(monotype, step);
        let step = Expression::new(
            ExpressionKind::Lambda { parameters: vec![accumulator, key], body: Box::new(bound) },
            step,
        );
        let object_keys = ExpressionKind::Foreign {
            foreign: &foreign::OBJECT_KEYS,
            arguments: vec![object.0.expression()],
        };
        let object_keys = Expression::new(object_keys, keys);
        let fold = match self.monotypes.get(monotype) {
            Monotype::Effect(_) => foreign::effect_fold(),
            _ => foreign::array_fold(),
        };
        let fold =
            ExpressionKind::Foreign { foreign: fold, arguments: vec![step, initial, object_keys] };
        let fold = Expression::new(fold, monotype);
        let bindings = [bind, function, object]
            .into_iter()
            .map(|(local, value)| Binding { local, value })
            .collect();
        let folded =
            Expression::new(ExpressionKind::Let { bindings, body: Box::new(fold) }, monotype);
        self.expression(folded)
    }

    fn named_local(&mut self, name: &str, monotype: MonotypeId) -> Local {
        let template = Local { id: LocalId(0), name: name.into(), monotype };
        self.fresh(&template)
    }
}
