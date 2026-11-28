use smol_str::SmolStr;

use super::conditions::negated;
use super::{Emitter, builtin_call, conjunction, identifier_expression};
use crate::error::GoResult;
use crate::monomorphic::{Expression, Local, LocalId, Pattern, PatternKind};
use crate::monotype::{Monotype, MonotypeId};
use crate::syntax::{GoBuiltin, GoExpression, GoStatement};

impl<'q, Q> Emitter<'_, '_, 'q, Q>
where
    Q: checking::ExternalQueries,
{
    pub(super) fn array_from_list(
        &mut self,
        list: &Expression,
        monotype: MonotypeId,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<Option<GoExpression>> {
        let Monotype::Data(data) = self.monotypes.get(list.monotype).clone() else {
            return Ok(None);
        };
        let constructors = self
            .monotypes
            .constructors(&mut self.context, &data)
            .map_err(|failure| failure.at(&self.current_definition()))?;
        let Some(cons) = constructors.iter().position(|constructor| constructor.name == "Cons")
        else {
            return Ok(None);
        };
        let [head, tail] = constructors[cons].fields[..] else { return Ok(None) };
        let fields = [("head", head), ("tail", tail)].map(|(name, monotype)| Pattern {
            kind: PatternKind::Variable(Local {
                id: LocalId(0),
                name: SmolStr::new(name),
                monotype,
            }),
            monotype,
        });
        let kind = PatternKind::Constructor { data, constructor: cons, arguments: fields.into() };
        let cell = self.temporary("cell");
        let list_value = self.value(list, out)?;
        out.push(self.define(cell.clone(), list_value, list.monotype)?);
        let mut tests = vec![];
        let mut bindings = vec![];
        let pattern = Pattern { kind, monotype: list.monotype };
        self.pattern_tests(&pattern, identifier_expression(&cell), &mut tests, &mut bindings)?;
        let [(_, head), (_, tail)] = <[_; 2]>::try_from(bindings)
            .unwrap_or_else(|_| unreachable!("invariant violated: a cons cell binds two fields"));
        let Some(is_cons) = conjunction(tests) else { return Ok(None) };
        let elements = self.temporary("elements");
        let array_type = self.go_type(monotype)?;
        out.push(GoStatement::Define {
            names: vec![elements.clone()],
            values: vec![GoExpression::Composite { type_: array_type, fields: vec![] }],
        });
        let appended =
            builtin_call(GoBuiltin::Append, vec![identifier_expression(&elements), head]);
        let body = vec![
            GoStatement::If {
                condition: negated(&is_cons),
                then: vec![GoStatement::Break],
                otherwise: vec![],
            },
            GoStatement::Assign {
                targets: vec![identifier_expression(&elements)],
                values: vec![appended],
            },
            GoStatement::Assign { targets: vec![identifier_expression(&cell)], values: vec![tail] },
        ];
        out.push(GoStatement::Loop(body));
        Ok(Some(identifier_expression(&elements)))
    }
}
