use super::iteration::Found;
use super::{Emitter, Mode, Sink, binary, builtin_call, call, identifier_expression, unit_value};
use crate::error::GoResult;
use crate::monomorphic::Expression;
use crate::monotype::MonotypeId;
use crate::syntax::{
    GoBinaryOperator, GoBuiltin, GoExpression, GoStatement, GoType, GoUnaryOperator,
};

pub(super) const ACCESSES: &[&str] = &[
    "Peek",
    "Poke",
    "PeekUnsafe",
    "PokeUnsafe",
    "Length",
    "Within",
    "Push",
    "Pop",
    "Shift",
    "Freeze",
    "UnsafeFreeze",
];

const FROZEN_SOURCE: &str = "func {name}[T any](elements []T) []T {
\treturn elements[:len(elements):len(elements)]
}
";

const COPIED_SOURCE: &str = "func {name}[T any](elements []T) []T {
\tcopied := make([]T, len(elements))
\tcopy(copied, elements)
\treturn copied
}
";

#[derive(Clone, Copy)]
enum End {
    Last,
    First,
}

impl End {
    fn support(self) -> (&'static str, &'static str) {
        match self {
            End::Last => ("withoutLast", WITHOUT_LAST_SOURCE),
            End::First => ("withoutFirst", WITHOUT_FIRST_SOURCE),
        }
    }
}

const WITHOUT_LAST_SOURCE: &str = "func {name}[T any](elements []T) []T {
\tvar zero T
\telements[len(elements)-1] = zero
\treturn elements[:len(elements)-1]
}
";

const WITHOUT_FIRST_SOURCE: &str = "func {name}[T any](elements []T) []T {
\tvar zero T
\telements[0] = zero
\treturn elements[1:]
}
";

impl<Q> Emitter<'_, '_, '_, Q>
where
    Q: checking::ExternalQueries,
{
    pub(super) fn mutable_access(
        &mut self,
        name: &str,
        arguments: &[Expression],
        result: MonotypeId,
        sink: Sink,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<()> {
        match name {
            "Peek" => self.mutable_peek(arguments, result, sink, out),
            "Poke" => self.mutable_poke(arguments, result, sink, out),
            "Pop" => self.mutable_removal(End::Last, arguments, result, sink, out),
            "Shift" => self.mutable_removal(End::First, arguments, result, sink, out),
            "Freeze" | "UnsafeFreeze" => {
                let (base, template) = match name {
                    "Freeze" => ("copied", COPIED_SOURCE),
                    _ => ("frozen", FROZEN_SOURCE),
                };
                let function = identifier_expression(&self.support_function(base, template));
                let elements = self.elements(&arguments[0], out)?;
                self.deliver(call(function, vec![elements]), result, sink, out)
            }
            "PeekUnsafe" => {
                let index = self.value(&arguments[0], out)?;
                let elements = self.elements(&arguments[1], out)?;
                self.deliver(indexed(elements, index), result, sink, out)
            }
            "Within" => {
                let index = self.value(&arguments[0], out)?;
                let elements = self.elements(&arguments[1], out)?;
                self.deliver(in_bounds(&index, elements), result, sink, out)
            }
            "Push" => {
                let value = self.value(&arguments[0], out)?;
                let elements = self.elements(&arguments[1], out)?;
                let appended = builtin_call(GoBuiltin::Append, vec![elements.clone(), value]);
                let targets = vec![elements.clone()];
                out.push(GoStatement::Assign { targets, values: vec![appended] });
                if let Sink::Discard = sink {
                    return Ok(());
                }
                self.deliver(call_length(elements), result, sink, out)
            }
            "PokeUnsafe" => {
                let index = self.value(&arguments[0], out)?;
                let value = self.value(&arguments[1], out)?;
                let elements = self.elements(&arguments[2], out)?;
                let targets = vec![indexed(elements, index)];
                out.push(GoStatement::Assign { targets, values: vec![value] });
                self.deliver(unit_value(), result, sink, out)
            }
            _ => {
                let elements = self.elements(&arguments[0], out)?;
                self.deliver(call_length(elements), result, sink, out)
            }
        }
    }

    fn mutable_peek(
        &mut self,
        arguments: &[Expression],
        result: MonotypeId,
        sink: Sink,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<()> {
        let found = self.callback(&arguments[0], 1);
        let just = match &found {
            Some(Found::Inline { .. }) => None,
            Some(Found::Direct { function, leading, .. }) => {
                let mut all = self.values(leading, out)?;
                all.push(function.clone());
                Some(all)
            }
            None => Some(vec![self.value(&arguments[0], out)?]),
        };
        let nothing = self.value(&arguments[1], out)?;
        let index = self.value(&arguments[2], out)?;
        let index = self.hoist(index, "index", out);
        let elements = self.elements(&arguments[3], out)?;
        if let GoExpression::Integer(constant) = index
            && constant < 0
        {
            return self.deliver(nothing, result, sink, out);
        }
        let name = self.temporary("peeked");
        let type_ = self.go_type(result)?;
        out.push(GoStatement::Variable { name: name.clone(), type_, value: None });
        let element = indexed(elements.clone(), index.clone());
        let target = vec![identifier_expression(&name)];
        let mut then = vec![];
        match (found, just) {
            (Some(Found::Inline { parameters, body }), _) => {
                self.locals.insert(parameters[0].id, element);
                self.sink(body, Mode::Value, Sink::Assign(name.clone()), &mut then)?;
            }
            (_, Some(mut values)) => {
                let function = values.pop().expect("the callback's function");
                values.push(element);
                let applied = call(function, values);
                then.push(GoStatement::Assign { targets: target.clone(), values: vec![applied] });
            }
            (Some(Found::Direct { .. }) | None, None) => unreachable!("a callback is known"),
        }
        let otherwise = vec![GoStatement::Assign { targets: target, values: vec![nothing] }];
        out.push(GoStatement::If { condition: in_bounds(&index, elements), then, otherwise });
        self.deliver(identifier_expression(&name), result, sink, out)
    }

    fn mutable_removal(
        &mut self,
        end: End,
        arguments: &[Expression],
        result: MonotypeId,
        sink: Sink,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<()> {
        let (base, template) = end.support();
        let without = identifier_expression(&self.support_function(base, template));
        if let Sink::Discard = sink {
            let elements = self.elements(&arguments[2], out)?;
            let shortened = shortened(&without, elements.clone());
            let condition = non_empty(elements);
            out.push(GoStatement::If { condition, then: vec![shortened], otherwise: vec![] });
            return Ok(());
        }
        let elements = self.elements(&arguments[2], out)?;
        let name = self.temporary("removed");
        let type_ = self.go_type(result)?;
        out.push(GoStatement::Variable { name: name.clone(), type_, value: None });
        let position = match end {
            End::Last => binary(
                GoBinaryOperator::Subtract,
                call_length(elements.clone()),
                GoExpression::Integer(1),
            ),
            End::First => GoExpression::Integer(0),
        };
        let (data, just) = self.constructor_named(result, "Just")?;
        let removed = self.construct(&data, just, vec![indexed(elements.clone(), position)])?;
        let nothing = self.nothing_value(result)?;
        let target = vec![identifier_expression(&name)];
        let then = vec![
            GoStatement::Assign { targets: target.clone(), values: vec![removed] },
            shortened(&without, elements.clone()),
        ];
        let otherwise = vec![GoStatement::Assign { targets: target, values: vec![nothing] }];
        out.push(GoStatement::If { condition: non_empty(elements), then, otherwise });
        self.deliver(identifier_expression(&name), result, sink, out)
    }

    fn mutable_poke(
        &mut self,
        arguments: &[Expression],
        result: MonotypeId,
        sink: Sink,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<()> {
        let index = self.value(&arguments[0], out)?;
        let index = self.hoist(index, "index", out);
        let value = self.value(&arguments[1], out)?;
        let elements = self.elements(&arguments[2], out)?;
        if let GoExpression::Integer(constant) = index
            && constant < 0
        {
            return self.deliver(GoExpression::Boolean(false), result, sink, out);
        }
        let targets = vec![indexed(elements.clone(), index.clone())];
        let store = GoStatement::Assign { targets, values: vec![value] };
        let condition = in_bounds(&index, elements);
        if let Sink::Discard = sink {
            out.push(GoStatement::If { condition, then: vec![store], otherwise: vec![] });
            return Ok(());
        }
        let name = self.temporary("poked");
        out.push(GoStatement::Variable { name: name.clone(), type_: GoType::Bool, value: None });
        let target = vec![identifier_expression(&name)];
        let outcome = |value: bool, targets: Vec<GoExpression>| GoStatement::Assign {
            targets,
            values: vec![GoExpression::Boolean(value)],
        };
        let then = vec![store, outcome(true, target.clone())];
        let otherwise = vec![outcome(false, target)];
        out.push(GoStatement::If { condition, then, otherwise });
        self.deliver(identifier_expression(&name), result, sink, out)
    }

    fn elements(
        &mut self,
        array: &Expression,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<GoExpression> {
        let array = self.value(array, out)?;
        let array = self.hoist(array, "array", out);
        Ok(GoExpression::Unary { operator: GoUnaryOperator::Dereference, operand: Box::new(array) })
    }
}

/// The length of the elements, which is a PureScript Int as Go gives it.
fn call_length(elements: GoExpression) -> GoExpression {
    builtin_call(GoBuiltin::Len, vec![elements])
}

fn non_empty(elements: GoExpression) -> GoExpression {
    binary(GoBinaryOperator::GreaterThan, call_length(elements), GoExpression::Integer(0))
}

fn shortened(without: &GoExpression, elements: GoExpression) -> GoStatement {
    let values = vec![call(without.clone(), vec![elements.clone()])];
    GoStatement::Assign { targets: vec![elements], values }
}

fn indexed(elements: GoExpression, index: GoExpression) -> GoExpression {
    GoExpression::Index { value: Box::new(elements), index: Box::new(index) }
}

pub(super) fn in_bounds(index: &GoExpression, elements: GoExpression) -> GoExpression {
    let length = builtin_call(GoBuiltin::Len, vec![elements]);
    let below = binary(GoBinaryOperator::LessThan, index.clone(), length);
    match index {
        GoExpression::Integer(constant) if *constant >= 0 => below,
        _ => binary(
            GoBinaryOperator::LogicalAnd,
            binary(GoBinaryOperator::GreaterThanOrEqual, index.clone(), GoExpression::Integer(0)),
            below,
        ),
    }
}
