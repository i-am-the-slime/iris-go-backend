//! The Go of the operations on a `Data.Map` that is a Go map ([`crate::maps`]): `m[k] = v`,
//! `delete(m, k)`, `v, found := m[k]`, `len(m)`, and the entries sorted by key that the tree is
//! built of.
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
            HashMapOperation::SortedEntries => {
                let table_type = arguments[0].monotype;
                let table = self.value(&arguments[0], out)?;
                self.sorted_entries(table, table_type, monotype, out)?
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

    /// The keys in the order of their `Ord`, Go's own for Ints and Chars, JavaScript's code-unit
    /// order for Strings, and the values in their order, as the record `entries` of the two.
    fn sorted_entries(
        &mut self,
        table: GoExpression,
        table_type: MonotypeId,
        entries: MonotypeId,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<GoExpression> {
        let key = match self.monotypes.get(table_type) {
            Monotype::HashMap(key, _) => *key,
            _ => unreachable!("invariant violated: sorted entries of a value that is no Go map"),
        };
        let sorted = match self.monotypes.get(key) {
            Monotype::String => {
                self.imports.insert("slices".into());
                let function = self.support_function("sortedStringEntries", STRING_ENTRIES_SOURCE);
                let compare = GoFunction { package: GoPackage::Prim, name: "CompareString" };
                let compare = self.go_function(compare);
                call(identifier_expression(&function), vec![table, compare])
            }
            _ => {
                let function =
                    self.support_function("sortedIntegerEntries", INTEGER_ENTRIES_SOURCE);
                call(identifier_expression(&function), vec![table])
            }
        };
        let keys = self.temporary("keys");
        let values = self.temporary("values");
        out.push(GoStatement::Define {
            names: vec![keys.clone(), values.clone()],
            values: vec![sorted],
        });
        let fields = vec![
            ("keys".into(), identifier_expression(&keys)),
            ("values".into(), identifier_expression(&values)),
        ];
        self.record_value(entries, fields)
    }
}

const INTEGER_ENTRIES_SOURCE: &str =
    "func {name}[K ~int | ~int32, V any](table map[K]V) ([]K, []V) {
\tcount := len(table)
\tkeys := make([]K, 0, count)
\tvalues := make([]V, 0, count)
\tfor key, value := range table {
\t\tkeys = append(keys, key)
\t\tvalues = append(values, value)
\t}
\tif count <= 32 {
\t\tfor index := 1; index < count; index++ {
\t\t\tkey, value := keys[index], values[index]
\t\t\tat := index
\t\t\tfor ; at > 0 && keys[at-1] > key; at-- {
\t\t\t\tkeys[at], values[at] = keys[at-1], values[at-1]
\t\t\t}
\t\t\tkeys[at], values[at] = key, value
\t\t}
\t\treturn keys, values
\t}
\tlowest, highest := keys[0], keys[0]
\tfor _, key := range keys {
\t\tlowest = min(lowest, key)
\t\thighest = max(highest, key)
\t}
\tbase := uint64(int64(lowest))
\tspan := uint64(int64(highest)) - base
\tspareKeys := make([]K, count)
\tspareValues := make([]V, count)
\tfor shift := 0; shift < 64 && span>>shift != 0; shift += 8 {
\t\tvar starts [256]int
\t\tfor _, key := range keys {
\t\t\tstarts[byte((uint64(int64(key))-base)>>shift)]++
\t\t}
\t\ttotal := 0
\t\tfor digit := range starts {
\t\t\tstarts[digit], total = total, total+starts[digit]
\t\t}
\t\tfor index, key := range keys {
\t\t\tdigit := byte((uint64(int64(key)) - base) >> shift)
\t\t\tat := starts[digit]
\t\t\tspareKeys[at], spareValues[at] = key, values[index]
\t\t\tstarts[digit] = at + 1
\t\t}
\t\tkeys, spareKeys = spareKeys, keys
\t\tvalues, spareValues = spareValues, values
\t}
\treturn keys, values
}
";

const STRING_ENTRIES_SOURCE: &str = "func {name}[V any](table map[string]V, compare func(string, string) int) ([]string, []V) {
\tcount := len(table)
\tkeys := make([]string, 0, count)
\tvalues := make([]V, 0, count)
\tfor key, value := range table {
\t\tkeys = append(keys, key)
\t\tvalues = append(values, value)
\t}
\tfor _, key := range keys {
\t\tfor at := 0; at < len(key); at++ {
\t\t\tif key[at] >= 0xEE {
\t\t\t\tslices.SortFunc(keys, compare)
\t\t\t\tfor index, key := range keys {
\t\t\t\t\tvalues[index] = table[key]
\t\t\t\t}
\t\t\t\treturn keys, values
\t\t\t}
\t\t}
\t}
\tinsertion := func(keys []string, values []V) {
\t\tfor index := 1; index < len(keys); index++ {
\t\t\tkey, value := keys[index], values[index]
\t\t\tat := index
\t\t\tfor ; at > 0 && keys[at-1] > key; at-- {
\t\t\t\tkeys[at], values[at] = keys[at-1], values[at-1]
\t\t\t}
\t\t\tkeys[at], values[at] = key, value
\t\t}
\t}
\tif count <= 32 {
\t\tinsertion(keys, values)
\t\treturn keys, values
\t}
\tprefixes := make([]uint64, count)
\tvar counts [8][256]int
\tfor index, key := range keys {
\t\tvar prefix uint64
\t\tfor at := 0; at < 8 && at < len(key); at++ {
\t\t\tprefix |= uint64(key[at]) << (56 - 8*at)
\t\t}
\t\tprefixes[index] = prefix
\t\tfor digit := range 8 {
\t\t\tcounts[digit][byte(prefix>>(8*digit))]++
\t\t}
\t}
\tsparePrefixes := make([]uint64, count)
\tspareKeys := make([]string, count)
\tspareValues := make([]V, count)
\tfor digit := range 8 {
\t\tstarts := &counts[digit]
\t\tshift := 8 * digit
\t\tif starts[byte(prefixes[0]>>shift)] == count {
\t\t\tcontinue
\t\t}
\t\ttotal := 0
\t\tfor bucket := range starts {
\t\t\tstarts[bucket], total = total, total+starts[bucket]
\t\t}
\t\tfor index, prefix := range prefixes {
\t\t\tbucket := byte(prefix >> shift)
\t\t\tat := starts[bucket]
\t\t\tsparePrefixes[at], spareKeys[at], spareValues[at] = prefix, keys[index], values[index]
\t\t\tstarts[bucket] = at + 1
\t\t}
\t\tprefixes, sparePrefixes = sparePrefixes, prefixes
\t\tkeys, spareKeys = spareKeys, keys
\t\tvalues, spareValues = spareValues, values
\t}
\tfor low := 0; low < count; {
\t\thigh := low + 1
\t\tfor high < count && prefixes[high] == prefixes[low] {
\t\t\thigh++
\t\t}
\t\tif high-low <= 16 {
\t\t\tinsertion(keys[low:high], values[low:high])
\t\t} else {
\t\t\torder := make([]int, high-low)
\t\t\tfor index := range order {
\t\t\t\torder[index] = low + index
\t\t\t}
\t\t\tslices.SortFunc(order, func(left int, right int) int { return compare(keys[left], keys[right]) })
\t\t\tfor index, from := range order {
\t\t\t\tspareKeys[index], spareValues[index] = keys[from], values[from]
\t\t\t}
\t\t\tcopy(keys[low:high], spareKeys[:high-low])
\t\t\tcopy(values[low:high], spareValues[:high-low])
\t\t}
\t\tlow = high
\t}
\treturn keys, values
}
";

fn entry(table: GoExpression, key: GoExpression) -> GoExpression {
    GoExpression::Index { value: Box::new(table), index: Box::new(key) }
}

fn store(table: GoExpression, key: GoExpression, value: GoExpression) -> GoStatement {
    GoStatement::Assign { targets: vec![entry(table, key)], values: vec![value] }
}
