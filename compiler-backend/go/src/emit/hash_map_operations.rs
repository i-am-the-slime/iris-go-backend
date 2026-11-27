//! The Go of the operations on a `Data.Map` that is a Go map ([`crate::maps`]): `m[k] = v`,
//! `delete(m, k)`, `v, found := m[k]`, `len(m)`, and the sorted keys that the tree's ordered
//! walks read.
//!
//! A write changes the map in place and answers it. The map is the only version anyone holds
//! ([`super::hash_maps`] decided so), so the program cannot tell.

use super::{Emitter, binary, call, identifier_expression};
use crate::error::GoResult;
use crate::foreign::{GoFunction, GoPackage};
use crate::maps::HashMapOperation;
use crate::monomorphic::Expression;
use crate::monotype::{Monotype, MonotypeId};
use crate::syntax::{GoExpression, GoStatement};

impl<Q> Emitter<'_, '_, '_, Q>
where
    Q: checking::ExternalQueries,
{
    pub(super) fn hash_map_operation(
        &mut self,
        operation: HashMapOperation,
        arguments: &[Expression],
        monotype: MonotypeId,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<GoExpression> {
        Ok(match operation {
            HashMapOperation::New => {
                let hint = self.value(&arguments[0], out)?;
                self.made(monotype, hint)?
            }
            HashMapOperation::Singleton => {
                let key = self.value(&arguments[0], out)?;
                let value = self.value(&arguments[1], out)?;
                let made = self.made(monotype, GoExpression::Integer(1))?;
                let table = self.named(made, out);
                out.push(store(table.clone(), key, value));
                table
            }
            HashMapOperation::Insert => {
                let key = self.value(&arguments[0], out)?;
                let value = self.value(&arguments[1], out)?;
                let table = self.value(&arguments[2], out)?;
                let table = self.named(table, out);
                out.push(store(table.clone(), key, value));
                table
            }
            HashMapOperation::Delete => {
                let key = self.value(&arguments[0], out)?;
                let table = self.value(&arguments[1], out)?;
                let table = self.named(table, out);
                let delete = call(identifier_expression("delete"), vec![table.clone(), key]);
                out.push(GoStatement::Expression(delete));
                table
            }
            HashMapOperation::Difference => {
                let table = self.value(&arguments[0], out)?;
                let table = self.named(table, out);
                let other = self.value(&arguments[1], out)?;
                let key = self.temporary("key");
                let delete = call(
                    identifier_expression("delete"),
                    vec![table.clone(), identifier_expression(&key)],
                );
                out.push(GoStatement::Range {
                    index: Some(key),
                    element: "_".into(),
                    iterable: other,
                    body: vec![GoStatement::Expression(delete)],
                });
                table
            }
            HashMapOperation::Lookup => self.looked_up(arguments, monotype, out)?,
            HashMapOperation::Member => {
                let key = self.value(&arguments[0], out)?;
                let table = self.value(&arguments[1], out)?;
                let found = self.temporary("found");
                out.push(GoStatement::Define {
                    names: vec!["_".into(), found.clone()],
                    values: vec![entry(table, key)],
                });
                identifier_expression(&found)
            }
            HashMapOperation::Size => super::length(self.value(&arguments[0], out)?),
            HashMapOperation::IsEmpty => {
                let size = super::length(self.value(&arguments[0], out)?);
                binary("==", size, GoExpression::Integer(0))
            }
            HashMapOperation::Get => {
                let key = self.value(&arguments[0], out)?;
                let table = self.value(&arguments[1], out)?;
                entry(table, key)
            }
            HashMapOperation::SortedKeys => {
                let table_type = arguments[0].monotype;
                let table = self.value(&arguments[0], out)?;
                self.sorted_keys(table, table_type)
            }
            HashMapOperation::BalancedHeight => {
                let count = self.value(&arguments[0], out)?;
                self.imports.insert("math/bits".into());
                let length = GoExpression::Qualified { package: "bits".into(), name: "Len".into() };
                let unsigned = call(identifier_expression("uint"), vec![count]);
                call(length, vec![unsigned])
            }
        })
    }

    /// `make(map[K]V, hint)`, without the hint when it is none.
    fn made(&mut self, monotype: MonotypeId, hint: GoExpression) -> GoResult<GoExpression> {
        let type_ = GoExpression::Type(self.go_type(monotype)?);
        let arguments = match hint {
            GoExpression::Integer(0) => vec![type_],
            hint => vec![type_, hint],
        };
        Ok(call(identifier_expression("make"), arguments))
    }

    fn named(&mut self, table: GoExpression, out: &mut Vec<GoStatement>) -> GoExpression {
        self.hoist(table, "table", out)
    }

    /// `value, found := m[k]` as the `Maybe` a lookup answers.
    fn looked_up(
        &mut self,
        arguments: &[Expression],
        monotype: MonotypeId,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<GoExpression> {
        let (data, just) = self.constructor_named(monotype, "Just")?;
        let (_, nothing) = self.constructor_named(monotype, "Nothing")?;
        let key = self.value(&arguments[0], out)?;
        let table = self.value(&arguments[1], out)?;
        let value = self.temporary("value");
        let found = self.temporary("found");
        out.push(GoStatement::Define {
            names: vec![value.clone(), found.clone()],
            values: vec![entry(table, key)],
        });
        let present = self.construct(&data, just, vec![identifier_expression(&value)])?;
        let missing = self.construct(&data, nothing, vec![])?;
        let name = self.temporary("entry");
        let type_ = self.go_type(monotype)?;
        out.push(GoStatement::Variable { name: name.clone(), type_, value: None });
        let target = vec![identifier_expression(&name)];
        out.push(GoStatement::If {
            condition: identifier_expression(&found),
            then: vec![GoStatement::Assign { targets: target.clone(), values: vec![present] }],
            otherwise: vec![GoStatement::Assign { targets: target, values: vec![missing] }],
        });
        Ok(identifier_expression(&name))
    }

    /// The keys in the order of their `Ord`: Go's own for Ints and Chars, JavaScript's code-unit
    /// order for Strings.
    fn sorted_keys(&mut self, table: GoExpression, table_type: MonotypeId) -> GoExpression {
        self.imports.insert("slices".into());
        self.imports.insert("maps".into());
        let keys = call(
            GoExpression::Qualified { package: "maps".into(), name: "Keys".into() },
            vec![table],
        );
        let key = match self.monotypes.get(table_type) {
            Monotype::HashMap(key, _) => *key,
            _ => unreachable!("invariant violated: sorted keys of a value that is no Go map"),
        };
        match self.monotypes.get(key) {
            Monotype::String => {
                let compare = GoFunction { package: GoPackage::Prim, name: "CompareString" };
                let compare = self.go_function(compare);
                let sorted =
                    GoExpression::Qualified { package: "slices".into(), name: "SortedFunc".into() };
                call(sorted, vec![keys, compare])
            }
            _ => {
                let sorted =
                    GoExpression::Qualified { package: "slices".into(), name: "Sorted".into() };
                call(sorted, vec![keys])
            }
        }
    }
}

fn entry(table: GoExpression, key: GoExpression) -> GoExpression {
    GoExpression::Index { value: Box::new(table), index: Box::new(key) }
}

fn store(table: GoExpression, key: GoExpression, value: GoExpression) -> GoStatement {
    GoStatement::Assign { targets: vec![entry(table, key)], values: vec![value] }
}
