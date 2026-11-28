//! The Go of the operations on a `Data.Map` kept in order ([`crate::maps`]): a B-tree that the
//! generated program declares once per key kind, whose writes change it in place and answer it.
//! A map whose keys come in ascending order, as clocks and sorted input do, is a run of its
//! entries instead until a key comes out of order, so that its writes and its least and greatest
//! keys cost no search.
//!
//! The map is the only version anyone holds ([`super::hash_maps`] decided so), so the program
//! cannot tell. It is a pointer, as a Go map is a reference, so that every Go variable holding
//! it sees its writes. Its keys are in the order of their `Ord`: Go's own for Ints and Chars,
//! JavaScript's code-unit order for Strings, as `prim.CompareString` has it.

use super::{Emitter, binary, call, identifier_expression};
use crate::error::GoResult;
use crate::foreign::{GoFunction, GoPackage};
use crate::maps::HashMapOperation;
use crate::monomorphic::Expression;
use crate::monotype::{Monotype, MonotypeId};
use crate::syntax::{GoExpression, GoStatement, GoType};
use smol_str::SmolStr;

impl<Q> Emitter<'_, '_, '_, Q>
where
    Q: checking::ExternalQueries,
{
    /// `*orderedMap[K, V]`, the B-tree of the key kind, declared at first need.
    pub(super) fn ordered_map_type(
        &mut self,
        key: MonotypeId,
        value: MonotypeId,
    ) -> GoResult<GoType> {
        let name = match self.monotypes.get(key) {
            Monotype::String => {
                // The template compares by code units with it once a key needs that.
                self.go_function(GoFunction { package: GoPackage::Prim, name: "CompareString" });
                self.support_function("orderedStringMap", STRING_SOURCE)
            }
            Monotype::Data(_) | Monotype::Record(_) => {
                self.support_function("orderedKeyMap", KEYED_SOURCE)
            }
            _ => self.support_function("orderedMap", INTEGER_SOURCE),
        };
        let arguments = vec![self.go_type(key)?, self.go_type(value)?];
        Ok(GoType::Pointer(Box::new(GoType::Generic { name, arguments })))
    }

    /// Whether a [`HashMapOperation`] works on a map kept in order rather than a Go map.
    pub(super) fn is_ordered_map_operation(
        &self,
        operation: HashMapOperation,
        arguments: &[Expression],
        monotype: MonotypeId,
    ) -> bool {
        let map = match operation {
            HashMapOperation::New | HashMapOperation::Singleton => monotype,
            HashMapOperation::BalancedHeight => return false,
            HashMapOperation::Insert | HashMapOperation::Add => arguments[2].monotype,
            HashMapOperation::Delete
            | HashMapOperation::Lookup
            | HashMapOperation::Member
            | HashMapOperation::Get
            | HashMapOperation::AtMost
            | HashMapOperation::Below
            | HashMapOperation::AtLeast
            | HashMapOperation::Above => arguments[1].monotype,
            HashMapOperation::Size
            | HashMapOperation::IsEmpty
            | HashMapOperation::SortedEntries
            | HashMapOperation::Difference
            | HashMapOperation::Min
            | HashMapOperation::Max
            | HashMapOperation::Copy => arguments[0].monotype,
        };
        matches!(self.monotypes.get(map), Monotype::OrderedMap(..))
    }

    pub(super) fn ordered_map_operation(
        &mut self,
        operation: HashMapOperation,
        arguments: &[Expression],
        monotype: MonotypeId,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<GoExpression> {
        Ok(match operation {
            // The size a Go map is made for, which the rewrite reads off values without effects,
            // is no use to a B-tree that grows as it goes.
            HashMapOperation::New => self.new_ordered_map(monotype)?,
            HashMapOperation::Singleton => {
                let key = self.value(&arguments[0], out)?;
                let value = self.value(&arguments[1], out)?;
                let made = self.new_ordered_map(monotype)?;
                let table = self.hoist_table(made, out);
                out.push(written(&table, "Insert", vec![key, value]));
                table
            }
            HashMapOperation::Insert => {
                let key = self.value(&arguments[0], out)?;
                let value = self.value(&arguments[1], out)?;
                let table = self.value(&arguments[2], out)?;
                let table = self.hoist_table(table, out);
                out.push(written(&table, "Insert", vec![key, value]));
                table
            }
            HashMapOperation::Delete => {
                let key = self.value(&arguments[0], out)?;
                let table = self.value(&arguments[1], out)?;
                let table = self.hoist_table(table, out);
                out.push(written(&table, "Delete", vec![key]));
                table
            }
            HashMapOperation::Difference => {
                let table = self.value(&arguments[0], out)?;
                let table = self.hoist_table(table, out);
                let other = self.value(&arguments[1], out)?;
                out.push(written(&table, "Difference", vec![other]));
                table
            }
            HashMapOperation::Lookup => {
                let key = self.value(&arguments[0], out)?;
                let table = self.value(&arguments[1], out)?;
                let found = method(table, "Lookup", vec![key]);
                self.maybe_of_found(found, monotype, out)?
            }
            HashMapOperation::Member => {
                let key = self.value(&arguments[0], out)?;
                let table = self.value(&arguments[1], out)?;
                let found = self.temporary("found");
                out.push(GoStatement::Define {
                    names: vec![found.clone()],
                    values: vec![method(table, "Member", vec![key])],
                });
                identifier_expression(&found)
            }
            HashMapOperation::Get => {
                let key = self.value(&arguments[0], out)?;
                let table = self.value(&arguments[1], out)?;
                method(table, "Get", vec![key])
            }
            HashMapOperation::Size => {
                let table = self.value(&arguments[0], out)?;
                method(table, "Len", vec![])
            }
            HashMapOperation::IsEmpty => {
                let table = self.value(&arguments[0], out)?;
                binary("==", method(table, "Len", vec![]), GoExpression::Integer(0))
            }
            HashMapOperation::SortedEntries => {
                let table = self.value(&arguments[0], out)?;
                let keys = self.temporary("keys");
                let values = self.temporary("values");
                out.push(GoStatement::Define {
                    names: vec![keys.clone(), values.clone()],
                    values: vec![method(table, "Entries", vec![])],
                });
                let fields = vec![
                    ("keys".into(), identifier_expression(&keys)),
                    ("values".into(), identifier_expression(&values)),
                ];
                self.record_value(monotype, fields)?
            }
            HashMapOperation::Min | HashMapOperation::Max => {
                let table = self.value(&arguments[0], out)?;
                let name = if operation == HashMapOperation::Min { "Min" } else { "Max" };
                self.maybe_entry(method(table, name, vec![]), monotype, out)?
            }
            HashMapOperation::AtMost
            | HashMapOperation::Below
            | HashMapOperation::AtLeast
            | HashMapOperation::Above => {
                let key = self.value(&arguments[0], out)?;
                let table = self.value(&arguments[1], out)?;
                let (name, counts) = match operation {
                    HashMapOperation::AtMost => ("AtMost", true),
                    HashMapOperation::Below => ("AtMost", false),
                    HashMapOperation::AtLeast => ("AtLeast", true),
                    _ => ("AtLeast", false),
                };
                let near = method(table, name, vec![key, GoExpression::Boolean(counts)]);
                self.maybe_entry(near, monotype, out)?
            }
            HashMapOperation::BalancedHeight => {
                unreachable!("invariant violated: the height of a tree as an ordered map's")
            }
            HashMapOperation::Copy => {
                unreachable!("invariant violated: a map kept in order copied as a Go map")
            }
            HashMapOperation::Add => {
                unreachable!("invariant violated: a map kept in order added to as a Go map")
            }
        })
    }

    /// `new(orderedMap[K, V])`, an empty map of the type.
    fn new_ordered_map(&mut self, monotype: MonotypeId) -> GoResult<GoExpression> {
        let GoType::Pointer(map) = self.go_type(monotype)? else {
            unreachable!("invariant violated: a map kept in order that is no pointer")
        };
        let Monotype::OrderedMap(key, _) = *self.monotypes.get(monotype) else {
            unreachable!("invariant violated: a map kept in order of no ordered map type")
        };
        if !matches!(self.monotypes.get(key), Monotype::Data(_) | Monotype::Record(_)) {
            return Ok(call(identifier_expression("new"), vec![GoExpression::Type(*map)]));
        }
        let leaves = self.key_leaves(key)?;
        let compare = identifier_expression(&self.map_key_comparison(key, &leaves)?);
        let fields = vec![(Some("Compare".to_string()), compare)];
        Ok(GoExpression::Address(Box::new(GoExpression::Composite { type_: *map, fields })))
    }

    fn hoist_table(&mut self, table: GoExpression, out: &mut Vec<GoStatement>) -> GoExpression {
        self.hoist(table, "table", out)
    }

    /// `value, found := lookup` as the `Maybe` of the value.
    fn maybe_of_found(
        &mut self,
        lookup: GoExpression,
        monotype: MonotypeId,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<GoExpression> {
        let value = self.temporary("value");
        let found = self.temporary("found");
        out.push(GoStatement::Define {
            names: vec![value.clone(), found.clone()],
            values: vec![lookup],
        });
        self.maybe_chosen(&found, vec![identifier_expression(&value)], monotype, out)
    }

    /// `key, value, found := near` as the `Maybe { key, value }` of the entry.
    fn maybe_entry(
        &mut self,
        near: GoExpression,
        monotype: MonotypeId,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<GoExpression> {
        let key = self.temporary("key");
        let value = self.temporary("value");
        let found = self.temporary("found");
        out.push(GoStatement::Define {
            names: vec![key.clone(), value.clone(), found.clone()],
            values: vec![near],
        });
        let entry = self.just_argument(monotype)?;
        let fields: Vec<(SmolStr, GoExpression)> = vec![
            ("key".into(), identifier_expression(&key)),
            ("value".into(), identifier_expression(&value)),
        ];
        let record = self.record_value(entry, fields)?;
        self.maybe_chosen(&found, vec![record], monotype, out)
    }

    /// The type a `Maybe` holds.
    fn just_argument(&mut self, maybe: MonotypeId) -> GoResult<MonotypeId> {
        let (data, just) = self.constructor_named(maybe, "Just")?;
        let constructors = self
            .monotypes
            .constructors(&mut self.context, &data)
            .map_err(|failure| failure.at(&self.current_definition()))?;
        Ok(constructors[just].fields[0])
    }

    /// `var entry Maybe; if found { entry = Just(values...) } else { entry = Nothing }`.
    fn maybe_chosen(
        &mut self,
        found: &str,
        values: Vec<GoExpression>,
        monotype: MonotypeId,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<GoExpression> {
        let (data, just) = self.constructor_named(monotype, "Just")?;
        let (_, nothing) = self.constructor_named(monotype, "Nothing")?;
        let present = self.construct(&data, just, values)?;
        let missing = self.construct(&data, nothing, vec![])?;
        let name = self.temporary("entry");
        let type_ = self.go_type(monotype)?;
        out.push(GoStatement::Variable { name: name.clone(), type_, value: None });
        let target = vec![identifier_expression(&name)];
        out.push(GoStatement::If {
            condition: identifier_expression(found),
            then: vec![GoStatement::Assign { targets: target.clone(), values: vec![present] }],
            otherwise: vec![GoStatement::Assign { targets: target, values: vec![missing] }],
        });
        Ok(identifier_expression(&name))
    }
}

fn method(table: GoExpression, name: &str, arguments: Vec<GoExpression>) -> GoExpression {
    call(GoExpression::Field { value: Box::new(table), name: name.into() }, arguments)
}

/// `table.Name(arguments)`, a write that changes the map in place.
fn written(table: &GoExpression, name: &str, arguments: Vec<GoExpression>) -> GoStatement {
    GoStatement::Expression(method(table.clone(), name, arguments))
}
macro_rules! ordered_map_source {
    ($constraint:literal, $order:literal) => {
        ordered_map_source!($constraint, "", $order)
    };
    ($constraint:literal, $fields:literal, $order:literal) => {
        concat!(
            "// {name} is a Data.Map that one owner holds along its whole life, as a B-tree that its writes
// change in place. A node holds up to 15 entries in ascending order of their keys, every node but
// the root at least 7, and an inner node one child more than it has entries. The leaves that
// merges free are kept for the splits to come.
//
// A map whose keys came in ascending order until its root leaf is full is a run of its entries
// instead, while every key it is given is above all those before it, or one it holds: deletes
// leave holes in the run that keep their keys. The first new key below the greatest, or a key
// next to which the run cannot answer at once, makes it the B-tree of the run's entries again.
type {name}[K ",
            $constraint,
            ", V any] struct {
\troot   *{name}Node[K, V]
\tsize   int
\texact  bool
\tspares []*{name}Node[K, V]
\t// Whether a new key came below the greatest.
\tdisordered bool
\trun        *{name}Run[K, V]
",
            $fields,
            "}

// {name}Run is the run of a map: every entry before first is a hole, and the last is none.
// Integer keys that go up one by one, the holes among them filled, are found by how far they are
// from the first.
type {name}Run[K ",
            $constraint,
            ", V any] struct {
\tentries []{name}Entry[K, V]
\tfirst   int
\tsparse  bool
}

type {name}Entry[K ",
            $constraint,
            ", V any] struct {
\tkey   K
\tvalue V
\tlive  bool
}

type {name}Node[K ",
            $constraint,
            ", V any] struct {
\tcount    int
\tkeys     [16]K
\tvalues   [16]V
\tchildren *[17]*{name}Node[K, V]
}

func (m *{name}[K, V]) Len() int {
\tif m == nil {
\t\treturn 0
\t}
\treturn m.size
}

func (m *{name}[K, V]) Lookup(key K) (V, bool) {
\tvar none V
\tif m == nil {
\t\treturn none, false
\t}
\tm.see(key)
\tif m.run != nil {
\t\tif at, found := m.locate(key); found && m.run.entries[at].live {
\t\t\treturn m.run.entries[at].value, true
\t\t}
\t\treturn none, false
\t}
\tfor node := m.root; node != nil; {
\t\tat, found := m.search(node, key)
\t\tif found {
\t\t\treturn node.values[at], true
\t\t}
\t\tif node.children == nil {
\t\t\tbreak
\t\t}
\t\tnode = node.children[at]
\t}
\treturn none, false
}

func (m *{name}[K, V]) Member(key K) bool {
\t_, found := m.Lookup(key)
\treturn found
}

func (m *{name}[K, V]) Get(key K) V {
\tvalue, _ := m.Lookup(key)
\treturn value
}

func (m *{name}[K, V]) Insert(key K, value V) {
\tm.see(key)
\tif m.run != nil {
\t\tif m.appended(key, value) {
\t\t\treturn
\t\t}
\t\tm.build()
\t}
\tif m.root == nil {
\t\troot := &{name}Node[K, V]{count: 1}
\t\troot.keys[0], root.values[0] = key, value
\t\tm.root, m.size = root, 1
\t\treturn
\t}
\tsplit, middleKey, middleValue, right := m.insert(m.root, key, value)
\tif split {
\t\troot := &{name}Node[K, V]{count: 1, children: new([17]*{name}Node[K, V])}
\t\troot.keys[0], root.values[0] = middleKey, middleValue
\t\troot.children[0], root.children[1] = m.root, right
\t\tm.root = root
\t}
}

// appended puts the entry after the run when its key is above all of the run's, or in the place
// of its key, and answers whether it could.
func (m *{name}[K, V]) appended(key K, value V) bool {
\tcount := len(m.run.entries)
\tif count == 0 || m.less(m.run.entries[count-1].key, key) {
\t\tm.push(key, value)
\t\treturn true
\t}
\tat, found := m.locate(key)
\tif !found {
\t\treturn false
\t}
\tentry := &m.run.entries[at]
\tentry.value = value
\tif !entry.live {
\t\tentry.live = true
\t\tm.size++
\t\tm.run.first = min(m.run.first, at)
\t}
\treturn true
}

// unroot makes the map the run of its root leaf's entries.
func (m *{name}[K, V]) unroot() {
\troot := m.root
\tm.root, m.size = nil, 0
\tm.run = &{name}Run[K, V]{entries: make([]{name}Entry[K, V], 0, 32)}
\tfor at := range root.count {
\t\tm.push(root.keys[at], root.values[at])
\t}
}

// build makes the map the B-tree of the run's entries, as full as it may be.
func (m *{name}[K, V]) build() {
\tm.disordered = true
\tif m.size > 0 {
\t\theight, most := 0, 15
\t\tfor most < m.size {
\t\t\theight, most = height+1, most*16+15
\t\t}
\t\tat := m.run.first
\t\tm.root = m.built(m.size, height, (most-15)/16, &at)
\t}
\tm.run = nil
}

// built answers the node of the next entries of the run, as many as the count, at the height
// above the leaves, where a node below it holds at most most entries under it.
func (m *{name}[K, V]) built(count int, height int, most int, at *int) *{name}Node[K, V] {
\tif height == 0 {
\t\tnode := &{name}Node[K, V]{count: count}
\t\tfor position := range count {
\t\t\tnode.keys[position], node.values[position] = m.taken(at)
\t\t}
\t\treturn node
\t}
\tchildren := (count + most + 1) / (most + 1)
\tnode := &{name}Node[K, V]{count: children - 1, children: new([17]*{name}Node[K, V])}
\teach, more := (count-children+1)/children, (count-children+1)%children
\tfor child := range children {
\t\tsize := each
\t\tif child < more {
\t\t\tsize++
\t\t}
\t\tnode.children[child] = m.built(size, height-1, (most-15)/16, at)
\t\tif child < children-1 {
\t\t\tnode.keys[child], node.values[child] = m.taken(at)
\t\t}
\t}
\treturn node
}

// taken answers the next entry of the run from the position, and moves past it.
func (m *{name}[K, V]) taken(at *int) (K, V) {
\tfor !m.run.entries[*at].live {
\t\t*at++
\t}
\tentry := &m.run.entries[*at]
\t*at++
\treturn entry.key, entry.value
}

// insert puts the entry under the node, and answers the middle entry and the node of the
// entries after it when the node overflowed and was split.
func (m *{name}[K, V]) insert(node *{name}Node[K, V], key K, value V) (bool, K, V, *{name}Node[K, V]) {
\tvar noKey K
\tvar noValue V
\tcount := node.count
\t// A key above every key of the node, as keys that count up are, goes after them all.
\tat, found := count, false
\tif count == 0 || !m.less(node.keys[count-1], key) {
\t\tat, found = m.search(node, key)
\t\t// A new key below the greatest is out of order.
\t\tif !found && node == m.root {
\t\t\tm.disordered = true
\t\t}
\t}
\tif found {
\t\tnode.values[at] = value
\t\treturn false, noKey, noValue, nil
\t}
\tif node.children != nil {
\t\tsplit, middleKey, middleValue, right := m.insert(node.children[at], key, value)
\t\tif !split {
\t\t\treturn false, noKey, noValue, nil
\t\t}
\t\tkey, value = middleKey, middleValue
\t\tcopy(node.children[at+2:count+2], node.children[at+1:count+1])
\t\tnode.children[at+1] = right
\t} else {
\t\tm.size++
\t}
\tcopy(node.keys[at+1:count+1], node.keys[at:count])
\tcopy(node.values[at+1:count+1], node.values[at:count])
\tnode.keys[at], node.values[at] = key, value
\tcount++
\tnode.count = count
\tif count < 16 {
\t\treturn false, noKey, noValue, nil
\t}
\t// A root leaf filled in order becomes the run instead.
\tif node == m.root && node.children == nil && !m.disordered {
\t\tm.unroot()
\t\treturn false, noKey, noValue, nil
\t}
\tright := m.spare(node.children == nil)
\tright.count = 7
\tcopy(right.keys[:], node.keys[9:])
\tcopy(right.values[:], node.values[9:])
\tif node.children != nil {
\t\tcopy(right.children[:], node.children[9:])
\t\tclear(node.children[9:])
\t}
\tmiddleKey, middleValue := node.keys[8], node.values[8]
\tclear(node.keys[8:])
\tclear(node.values[8:])
\tnode.count = 8
\treturn true, middleKey, middleValue, right
}

// spare answers an empty node, a leaf or an inner node, of those freed if there is one.
func (m *{name}[K, V]) spare(leaf bool) *{name}Node[K, V] {
\tif leaf && len(m.spares) > 0 {
\t\tlast := len(m.spares) - 1
\t\tnode := m.spares[last]
\t\tm.spares = m.spares[:last]
\t\treturn node
\t}
\tif leaf {
\t\treturn &{name}Node[K, V]{}
\t}
\treturn &{name}Node[K, V]{children: new([17]*{name}Node[K, V])}
}

func (m *{name}[K, V]) Delete(key K) {
\tif m == nil || m.size == 0 {
\t\treturn
\t}
\tm.see(key)
\tif m.run != nil {
\t\tm.hollow(key)
\t\treturn
\t}
\tif !m.delete(m.root, key) {
\t\treturn
\t}
\tm.size--
\tif m.root.count == 0 {
\t\tif m.root.children == nil {
\t\t\tm.root = nil
\t\t} else {
\t\t\tm.root = m.root.children[0]
\t\t}
\t}
}

// hollow leaves a hole where the entry of the key was in the run. The holes at its ends go, and
// so do those within once they outnumber the entries, as the run cannot skip them.
func (m *{name}[K, V]) hollow(key K) {
\tat, found := m.locate(key)
\tif !found || !m.run.entries[at].live {
\t\treturn
\t}
\tvar noValue V
\tm.run.entries[at].live, m.run.entries[at].value = false, noValue
\tm.size--
\tcount := len(m.run.entries)
\tif m.size == 0 {
\t\tclear(m.run.entries)
\t\tm.run.entries, m.run.first, m.run.sparse = m.run.entries[:0], 0, false
\t\treturn
\t}
\tif at == count-1 {
\t\tfor !m.run.entries[count-1].live {
\t\t\tcount--
\t\t}
\t\tclear(m.run.entries[count:])
\t\tm.run.entries = m.run.entries[:count]
\t}
\tif at == m.run.first {
\t\tfor !m.run.entries[m.run.first].live {
\t\t\tm.run.first++
\t\t}
\t}
\tif holes := count - m.run.first - m.size; holes > m.size*m.holesEach()+32 {
\t\tm.compact()
\t} else if m.run.first > count/2 && m.run.first >= 32 {
\t\tcopy(m.run.entries, m.run.entries[m.run.first:])
\t\tclear(m.run.entries[count-m.run.first:])
\t\tm.run.entries, m.run.first = m.run.entries[:count-m.run.first], 0
\t}
}

// compact moves the run's entries together, its holes gone.
func (m *{name}[K, V]) compact() {
\tkept := 0
\tfor _, entry := range m.run.entries[m.run.first:] {
\t\tif entry.live {
\t\t\tm.run.entries[kept] = entry
\t\t\tkept++
\t\t}
\t}
\tclear(m.run.entries[kept:])
\tm.run.entries, m.run.first = m.run.entries[:kept], 0
\tm.run.sparse = true
}

func (m *{name}[K, V]) delete(node *{name}Node[K, V], key K) bool {
\tat, found := m.search(node, key)
\tif node.children == nil {
\t\tif found {
\t\t\tnode.remove(at)
\t\t}
\t\treturn found
\t}
\tif found {
\t\tnode.keys[at], node.values[at] = m.deleteLast(node.children[at])
\t} else if !m.delete(node.children[at], key) {
\t\treturn false
\t}
\tif node.children[at].count < 7 {
\t\tm.refill(node, at)
\t}
\treturn true
}

// remove takes the entry at a leaf's position out.
func (node *{name}Node[K, V]) remove(at int) {
\tcount := node.count - 1
\tcopy(node.keys[at:count], node.keys[at+1:count+1])
\tcopy(node.values[at:count], node.values[at+1:count+1])
\tvar noKey K
\tvar noValue V
\tnode.keys[count], node.values[count] = noKey, noValue
\tnode.count = count
}

// deleteLast takes the greatest entry under the node out and answers it.
func (m *{name}[K, V]) deleteLast(node *{name}Node[K, V]) (K, V) {
\tif node.children == nil {
\t\tkey, value := node.keys[node.count-1], node.values[node.count-1]
\t\tnode.remove(node.count - 1)
\t\treturn key, value
\t}
\tlast := node.count
\tkey, value := m.deleteLast(node.children[last])
\tif node.children[last].count < 7 {
\t\tm.refill(node, last)
\t}
\treturn key, value
}

// refill gives the child at the position, which holds one entry too few, an entry of a sibling
// that can spare one, or merges it with a sibling.
func (m *{name}[K, V]) refill(node *{name}Node[K, V], at int) {
\tchild := node.children[at]
\tvar noKey K
\tvar noValue V
\tif at > 0 && node.children[at-1].count > 7 {
\t\tleft := node.children[at-1]
\t\tcopy(child.keys[1:child.count+1], child.keys[:child.count])
\t\tcopy(child.values[1:child.count+1], child.values[:child.count])
\t\tchild.keys[0], child.values[0] = node.keys[at-1], node.values[at-1]
\t\tif child.children != nil {
\t\t\tcopy(child.children[1:child.count+2], child.children[:child.count+1])
\t\t\tchild.children[0] = left.children[left.count]
\t\t\tleft.children[left.count] = nil
\t\t}
\t\tchild.count++
\t\tleft.count--
\t\tnode.keys[at-1], node.values[at-1] = left.keys[left.count], left.values[left.count]
\t\tleft.keys[left.count], left.values[left.count] = noKey, noValue
\t\treturn
\t}
\tif at < node.count && node.children[at+1].count > 7 {
\t\tright := node.children[at+1]
\t\tchild.keys[child.count], child.values[child.count] = node.keys[at], node.values[at]
\t\tif child.children != nil {
\t\t\tchild.children[child.count+1] = right.children[0]
\t\t\tcopy(right.children[:right.count], right.children[1:right.count+1])
\t\t\tright.children[right.count] = nil
\t\t}
\t\tchild.count++
\t\tnode.keys[at], node.values[at] = right.keys[0], right.values[0]
\t\tright.remove(0)
\t\treturn
\t}
\tif at == node.count {
\t\tat--
\t}
\tleft, right := node.children[at], node.children[at+1]
\tleft.keys[left.count], left.values[left.count] = node.keys[at], node.values[at]
\tcopy(left.keys[left.count+1:], right.keys[:right.count])
\tcopy(left.values[left.count+1:], right.values[:right.count])
\tif left.children != nil {
\t\tcopy(left.children[left.count+1:], right.children[:right.count+1])
\t}
\tleft.count += 1 + right.count
\tcount := node.count
\tcopy(node.children[at+1:count], node.children[at+2:count+1])
\tnode.children[count] = nil
\tnode.remove(at)
\tif right.children == nil && len(m.spares) < 8 {
\t\t*right = {name}Node[K, V]{}
\t\tm.spares = append(m.spares, right)
\t}
}

func (m *{name}[K, V]) Min() (K, V, bool) {
\tif m != nil && m.run != nil && m.size > 0 {
\t\tleast := &m.run.entries[m.run.first]
\t\treturn least.key, least.value, true
\t}
\tif m == nil || m.root == nil {
\t\tvar noKey K
\t\tvar noValue V
\t\treturn noKey, noValue, false
\t}
\tnode := m.root
\tfor node.children != nil {
\t\tnode = node.children[0]
\t}
\treturn node.keys[0], node.values[0], true
}

func (m *{name}[K, V]) Max() (K, V, bool) {
\tif m != nil && m.run != nil && m.size > 0 {
\t\tgreatest := &m.run.entries[len(m.run.entries)-1]
\t\treturn greatest.key, greatest.value, true
\t}
\tif m == nil || m.root == nil {
\t\tvar noKey K
\t\tvar noValue V
\t\treturn noKey, noValue, false
\t}
\tnode := m.root
\tfor node.children != nil {
\t\tnode = node.children[node.count]
\t}
\treturn node.keys[node.count-1], node.values[node.count-1], true
}

// AtMost answers the entry of the greatest key at most the key, or of the greatest key below it
// when the key itself does not count. The run answers it unless the entry is past a long stretch
// of holes, which the map becomes the tree for.
func (m *{name}[K, V]) AtMost(key K, counts bool) (K, V, bool) {
\tvar bestKey K
\tvar bestValue V
\tfound := false
\tif m == nil || m.size == 0 {
\t\treturn bestKey, bestValue, false
\t}
\tm.see(key)
\tif m.run != nil {
\t\tleast, greatest := &m.run.entries[m.run.first], &m.run.entries[len(m.run.entries)-1]
\t\tif m.less(greatest.key, key) || counts && greatest.key == key {
\t\t\treturn greatest.key, greatest.value, true
\t\t}
\t\tif m.less(key, least.key) || !counts && least.key == key {
\t\t\treturn bestKey, bestValue, false
\t\t}
\t\tat, hit := m.locate(key)
\t\tif hit && counts && m.run.entries[at].live {
\t\t\treturn key, m.run.entries[at].value, true
\t\t}
\t\tfor below := at - 1; below >= at-16; below-- {
\t\t\tif m.run.entries[below].live {
\t\t\t\treturn m.run.entries[below].key, m.run.entries[below].value, true
\t\t\t}
\t\t}
\t\tm.build()
\t}
\tfor node := m.root; node != nil; {
\t\tat, hit := m.search(node, key)
\t\tif hit && counts {
\t\t\treturn node.keys[at], node.values[at], true
\t\t}
\t\tif at > 0 {
\t\t\tbestKey, bestValue, found = node.keys[at-1], node.values[at-1], true
\t\t}
\t\tif node.children == nil {
\t\t\tbreak
\t\t}
\t\tnode = node.children[at]
\t}
\treturn bestKey, bestValue, found
}

// AtLeast answers the entry of the least key at least the key, or of the least key above it
// when the key itself does not count, as AtMost does.
func (m *{name}[K, V]) AtLeast(key K, counts bool) (K, V, bool) {
\tvar bestKey K
\tvar bestValue V
\tfound := false
\tif m == nil || m.size == 0 {
\t\treturn bestKey, bestValue, false
\t}
\tm.see(key)
\tif m.run != nil {
\t\tleast, greatest := &m.run.entries[m.run.first], &m.run.entries[len(m.run.entries)-1]
\t\tif m.less(key, least.key) || counts && least.key == key {
\t\t\treturn least.key, least.value, true
\t\t}
\t\tif m.less(greatest.key, key) || !counts && greatest.key == key {
\t\t\treturn bestKey, bestValue, false
\t\t}
\t\tat, hit := m.locate(key)
\t\tif hit && counts && m.run.entries[at].live {
\t\t\treturn key, m.run.entries[at].value, true
\t\t}
\t\tif hit {
\t\t\tat++
\t\t}
\t\tfor above := at; above < at+16; above++ {
\t\t\tif m.run.entries[above].live {
\t\t\t\treturn m.run.entries[above].key, m.run.entries[above].value, true
\t\t\t}
\t\t}
\t\tm.build()
\t}
\tfor node := m.root; node != nil; {
\t\tat, hit := m.search(node, key)
\t\tif hit {
\t\t\tif counts {
\t\t\t\treturn node.keys[at], node.values[at], true
\t\t\t}
\t\t\tat++
\t\t}
\t\tif at < node.count {
\t\t\tbestKey, bestValue, found = node.keys[at], node.values[at], true
\t\t}
\t\tif node.children == nil {
\t\t\tbreak
\t\t}
\t\tnode = node.children[at]
\t}
\treturn bestKey, bestValue, found
}

// Entries answers the keys in ascending order and the values in theirs.
func (m *{name}[K, V]) Entries() ([]K, []V) {
\tkeys := make([]K, 0, m.Len())
\tvalues := make([]V, 0, m.Len())
\tif m != nil && m.run != nil {
\t\tfor _, entry := range m.run.entries[m.run.first:] {
\t\t\tif entry.live {
\t\t\t\tkeys, values = append(keys, entry.key), append(values, entry.value)
\t\t\t}
\t\t}
\t} else if m != nil && m.root != nil {
\t\tkeys, values = m.root.entries(keys, values)
\t}
\treturn keys, values
}

func (node *{name}Node[K, V]) entries(keys []K, values []V) ([]K, []V) {
\tif node.children == nil {
\t\treturn append(keys, node.keys[:node.count]...), append(values, node.values[:node.count]...)
\t}
\tfor at := range node.count {
\t\tkeys, values = node.children[at].entries(keys, values)
\t\tkeys, values = append(keys, node.keys[at]), append(values, node.values[at])
\t}
\treturn node.children[node.count].entries(keys, values)
}

// Difference deletes the keys of the other map.
func (m *{name}[K, V]) Difference(other *{name}[K, V]) {
\tif m == nil {
\t\treturn
\t}
\tif m == other {
\t\tm.root, m.size, m.exact, m.disordered, m.run = nil, 0, false, false, nil
\t\treturn
\t}
\tif other == nil || other.size == 0 {
\t\treturn
\t}
\tif other.run == nil {
\t\tm.deleteKeys(other.root)
\t\treturn
\t}
\tfor _, entry := range other.run.entries[other.run.first:] {
\t\tif entry.live {
\t\t\tm.Delete(entry.key)
\t\t}
\t}
}

func (m *{name}[K, V]) deleteKeys(node *{name}Node[K, V]) {
\tfor at := range node.count {
\t\tif node.children != nil {
\t\t\tm.deleteKeys(node.children[at])
\t\t}
\t\tm.Delete(node.keys[at])
\t}
\tif node.children != nil {
\t\tm.deleteKeys(node.children[node.count])
\t}
}
",
            $order,
        )
    };
}

const INTEGER_SOURCE: &str = ordered_map_source!(
    "~int | ~int32",
    "
// see notes a key the map meets: an integer key needs nothing.
func (m *{name}[K, V]) see(key K) {}

// search answers the position of the first key of the node at least the key, and whether it is
// the key.
func (m *{name}[K, V]) search(node *{name}Node[K, V], key K) (int, bool) {
\tat := 0
\tfor at < node.count && node.keys[at] < key {
\t\tat++
\t}
\treturn at, at < node.count && node.keys[at] == key
}

func (m *{name}[K, V]) less(key K, other K) bool {
\treturn key < other
}

// locate answers the position in the run of the key, or of the least key above it, and whether
// it is the key's.
func (m *{name}[K, V]) locate(key K) (int, bool) {
\trun := m.run.entries
\tif !m.run.sparse {
\t\tif len(run) == 0 || key < run[0].key {
\t\t\treturn 0, false
\t\t}
\t\tat := int(key) - int(run[0].key)
\t\tif at >= len(run) {
\t\t\treturn len(run), false
\t\t}
\t\treturn at, true
\t}
\tlow, high := m.run.first, len(run)
\tfor low < high {
\t\tmiddle := int(uint(low+high) >> 1)
\t\tif run[middle].key < key {
\t\t\tlow = middle + 1
\t\t} else {
\t\t\thigh = middle
\t\t}
\t}
\treturn low, low < len(run) && run[low].key == key
}

// push puts the entry after the run's. Keys that go up by little have the holes between them
// filled, so that they stay one apart.
func (m *{name}[K, V]) push(key K, value V) {
\tcount := len(m.run.entries)
\tif count > 0 && !m.run.sparse {
\t\tlast := m.run.entries[count-1].key
\t\tgap := int(key) - int(last) - 1
\t\tif holes := count - m.run.first - m.size; gap > 0 && holes+gap > m.size*m.holesEach()+32 {
\t\t\tm.run.sparse = true
\t\t} else {
\t\t\tfor step := 1; step <= gap; step++ {
\t\t\t\tm.run.entries = append(m.run.entries, {name}Entry[K, V]{key: last + K(step)})
\t\t\t}
\t\t}
\t}
\tm.run.entries = append(m.run.entries, {name}Entry[K, V]{key: key, value: value, live: true})
\tm.size++
}

// holesEach answers how many holes the run keeps for each entry: those of keys that stay one
// apart cost no search.
func (m *{name}[K, V]) holesEach() int {
\tif m.run.sparse {
\t\treturn 1
\t}
\treturn 4
}
"
);

const STRING_SOURCE: &str = ordered_map_source!(
    "~string",
    "
// see notes a key the map meets: once a key holds a byte from 0xEE up, of a character from
// U+E000 up, the map compares its keys by their UTF-16 code units as JavaScript does, which Go's
// order of their bytes agrees with until then.
func (m *{name}[K, V]) see(key K) {
\tif m.exact {
\t\treturn
\t}
\tfor at := 0; at < len(key); at++ {
\t\tif key[at] >= 0xEE {
\t\t\tm.exact = true
\t\t\treturn
\t\t}
\t}
}

// search answers the position of the first key of the node at least the key, and whether it is
// the key.
func (m *{name}[K, V]) search(node *{name}Node[K, V], key K) (int, bool) {
\tlow, high := 0, node.count
\tif m.exact {
\t\tfor low < high {
\t\t\tmiddle := int(uint(low+high) >> 1)
\t\t\tif prim.CompareString(string(node.keys[middle]), string(key)) < 0 {
\t\t\t\tlow = middle + 1
\t\t\t} else {
\t\t\t\thigh = middle
\t\t\t}
\t\t}
\t\treturn low, low < node.count && node.keys[low] == key
\t}
\tfor low < high {
\t\tmiddle := int(uint(low+high) >> 1)
\t\tif node.keys[middle] < key {
\t\t\tlow = middle + 1
\t\t} else {
\t\t\thigh = middle
\t\t}
\t}
\treturn low, low < node.count && node.keys[low] == key
}

func (m *{name}[K, V]) less(key K, other K) bool {
\tif m.exact {
\t\treturn prim.CompareString(string(key), string(other)) < 0
\t}
\treturn key < other
}

// locate answers the position in the run of the key, or of the least key above it, and whether
// it is the key's.
func (m *{name}[K, V]) locate(key K) (int, bool) {
\trun := m.run.entries
\tlow, high := m.run.first, len(run)
\tfor low < high {
\t\tmiddle := int(uint(low+high) >> 1)
\t\tif m.less(run[middle].key, key) {
\t\t\tlow = middle + 1
\t\t} else {
\t\t\thigh = middle
\t\t}
\t}
\treturn low, low < len(run) && run[low].key == key
}

// push puts the entry after the run's.
func (m *{name}[K, V]) push(key K, value V) {
\tm.run.entries = append(m.run.entries, {name}Entry[K, V]{key: key, value: value, live: true})
\tm.size++
}

func (m *{name}[K, V]) holesEach() int {
\treturn 1
}
"
);

const KEYED_SOURCE: &str = ordered_map_source!(
    "comparable",
    "\tCompare func(K, K) int
",
    "
// see notes a key the map meets: a record or product key needs nothing.
func (m *{name}[K, V]) see(key K) {}

// search answers the position of the first key of the node at least the key, and whether it is
// the key.
func (m *{name}[K, V]) search(node *{name}Node[K, V], key K) (int, bool) {
\tlow, high := 0, node.count
\tfor low < high {
\t\tmiddle := int(uint(low+high) >> 1)
\t\tif m.Compare(node.keys[middle], key) < 0 {
\t\t\tlow = middle + 1
\t\t} else {
\t\t\thigh = middle
\t\t}
\t}
\treturn low, low < node.count && node.keys[low] == key
}

func (m *{name}[K, V]) less(key K, other K) bool {
\treturn m.Compare(key, other) < 0
}

// locate answers the position in the run of the key, or of the least key above it, and whether
// it is the key's.
func (m *{name}[K, V]) locate(key K) (int, bool) {
\trun := m.run.entries
\tlow, high := m.run.first, len(run)
\tfor low < high {
\t\tmiddle := int(uint(low+high) >> 1)
\t\tif m.less(run[middle].key, key) {
\t\t\tlow = middle + 1
\t\t} else {
\t\t\thigh = middle
\t\t}
\t}
\treturn low, low < len(run) && run[low].key == key
}

// push puts the entry after the run's.
func (m *{name}[K, V]) push(key K, value V) {
\tm.run.entries = append(m.run.entries, {name}Entry[K, V]{key: key, value: value, live: true})
\tm.size++
}

func (m *{name}[K, V]) holesEach() int {
\treturn 1
}
"
);
