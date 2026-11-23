use smol_str::SmolStr;

use super::{Emitter, call, identifier_expression, length};
use crate::error::GoResult;
use crate::monomorphic::{Expression, Local, LocalId, Pattern, PatternKind};
use crate::monotype::{DataType, Monotype, MonotypeId};
use crate::syntax::{GoExpression, GoStatement};

impl<'q, Q> Emitter<'_, '_, 'q, Q>
where
    Q: checking::ExternalQueries,
{
    pub(super) fn unzip(
        &mut self,
        pairs: &Expression,
        monotype: MonotypeId,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<Option<GoExpression>> {
        let Monotype::Data(unzipped) = self.monotypes.get(monotype).clone() else {
            return Ok(None);
        };
        let Monotype::Array(pair) = *self.monotypes.get(pairs.monotype) else { return Ok(None) };
        let Monotype::Data(zipped) = self.monotypes.get(pair).clone() else { return Ok(None) };
        let [first, second] = self.only_constructor_fields(&zipped)?[..] else {
            return Ok(None);
        };
        let pairs = self.value(pairs, out)?;
        let pairs = self.hoist(pairs, "pairs", out);
        let firsts = self.allocated_like(&pairs, first, "firsts", out)?;
        let seconds = self.allocated_like(&pairs, second, "seconds", out)?;
        let index = self.temporary("index");
        let element = self.temporary("pair");
        let fields = [("first", first), ("second", second)].map(|(name, monotype)| Pattern {
            kind: PatternKind::Variable(Local {
                id: LocalId(0),
                name: SmolStr::new(name),
                monotype,
            }),
            monotype,
        });
        let kind =
            PatternKind::Constructor { data: zipped, constructor: 0, arguments: fields.into() };
        let mut bindings = vec![];
        self.pattern_tests(
            &Pattern { kind, monotype: pair },
            identifier_expression(&element),
            &mut vec![],
            &mut bindings,
        )?;
        let [(_, first), (_, second)] = <[_; 2]>::try_from(bindings)
            .unwrap_or_else(|_| unreachable!("invariant violated: a pair binds two fields"));
        let slot = |array: &str| GoExpression::Index {
            value: Box::new(identifier_expression(array)),
            index: Box::new(identifier_expression(&index)),
        };
        let body = vec![
            GoStatement::Assign { targets: vec![slot(&firsts)], values: vec![first] },
            GoStatement::Assign { targets: vec![slot(&seconds)], values: vec![second] },
        ];
        out.push(GoStatement::Range { index: Some(index), element, iterable: pairs, body });
        let arrays = vec![identifier_expression(&firsts), identifier_expression(&seconds)];
        self.construct(&unzipped, 0, arrays).map(Some)
    }

    fn only_constructor_fields(&mut self, data: &DataType) -> GoResult<Vec<MonotypeId>> {
        let constructors = self
            .monotypes
            .constructors(&mut self.context, data)
            .map_err(|failure| failure.at(&self.current_definition()))?;
        Ok(match &constructors[..] {
            [constructor] => constructor.fields.clone(),
            _ => vec![],
        })
    }

    fn allocated_like(
        &mut self,
        pairs: &GoExpression,
        element: MonotypeId,
        name: &str,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<String> {
        let array = self.monotypes.intern(Monotype::Array(element));
        let array_type = self.go_type(array)?;
        let allocated = self.temporary(name);
        let made = call(
            identifier_expression("make"),
            vec![GoExpression::Type(array_type), length(pairs.clone())],
        );
        out.push(GoStatement::Define { names: vec![allocated.clone()], values: vec![made] });
        Ok(allocated)
    }
}
