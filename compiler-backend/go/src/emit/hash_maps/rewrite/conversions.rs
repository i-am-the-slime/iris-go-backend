//! The functions that turn a Go map into the balanced tree and back, one pair per map type.
//!
//! The tree of a Go map is built from its entries in ascending order of their keys, the middle
//! entry at the root, so that every node is balanced and its height is the bit length of its
//! size. A Go map of a
//! tree is filled by walking the tree, made for as many entries as the tree holds.

use super::{
    Conversions, Representation, Rewrite, alternative, call, constructor, hash_map,
    placeholder_function, variable,
};
use crate::foreign::{Foreign, Operator};
use crate::maps::HashMapOperation;
use crate::monomorphic::{
    Binding, Expression, ExpressionKind, Function, FunctionId, Literal, Local, Pattern, PatternKind,
};
use crate::monotype::{DataType, Monotype, MonotypeId, RecordField};
use smol_str::SmolStr;

impl Rewrite<'_> {
    /// The functions that turn a native map of the tree type into the tree and back, made at
    /// first need.
    pub(super) fn conversions(
        &mut self,
        tree: MonotypeId,
        representation: Representation,
    ) -> Conversions {
        if let Some(&conversions) = self.conversions.get(&(tree, representation)) {
            return conversions;
        }
        let hash = self.native_type(tree, representation);
        let Monotype::Data(data) = self.monotypes.get(tree).clone() else {
            unreachable!("invariant violated: a map type is no data type")
        };
        let unit = self.unit();
        // The tree of sorted entries is built the same way from either native map.
        let known = self.builders.get(&tree).copied();
        let build = known.unwrap_or_else(|| self.add_function(placeholder_function(unit)));
        let to_tree = self.add_function(placeholder_function(unit));
        let fill = self.add_function(placeholder_function(unit));
        let from_tree = self.add_function(placeholder_function(unit));
        if known.is_none() {
            let builder = self.tree_builder(build, &data, tree);
            self.program.functions[build.0 as usize] = builder;
            self.builders.insert(tree, build);
        }
        let converted = self.tree_of_table(build, tree, hash);
        self.program.functions[to_tree.0 as usize] = converted;
        let filled = self.table_filler(fill, &data, tree, hash);
        self.program.functions[fill.0 as usize] = filled;
        let converted = self.table_of_tree(fill, &data, tree, hash);
        self.program.functions[from_tree.0 as usize] = converted;
        let conversions = Conversions { to_tree, from_tree };
        self.conversions.insert((tree, representation), conversions);
        conversions
    }

    fn add_function(&mut self, function: Function) -> FunctionId {
        let id = FunctionId(self.program.functions.len() as u32);
        self.program.functions.push(function);
        id
    }

    fn defined(
        &self,
        name: &str,
        parameters: Vec<Local>,
        result: MonotypeId,
        body: Expression,
    ) -> Function {
        Function {
            name: SmolStr::new(name),
            origin: self.origin,
            parameters,
            result,
            body,
            position: None,
        }
    }

    /// `treeFromKeys keys values low high`: the balanced tree of the entries `keys[low:high]`,
    /// which ascend, and `values[low:high]`.
    fn tree_builder(&mut self, id: FunctionId, data: &DataType, tree: MonotypeId) -> Function {
        let shape = self.shapes[&tree];
        let int = self.monotypes.intern(Monotype::Int);
        let boolean = self.monotypes.intern(Monotype::Boolean);
        let keys_type = self.monotypes.intern(Monotype::Array(shape.key));
        let values_type = self.monotypes.intern(Monotype::Array(shape.value));
        let keys = self.fresh("keys", keys_type);
        let values = self.fresh("values", values_type);
        let low = self.fresh("low", int);
        let high = self.fresh("high", int);
        let middle = self.fresh("middle", int);
        let key = self.fresh("key", shape.key);
        let count = self.fresh("count", int);
        let operator = |operator: Operator, arguments: Vec<Expression>, monotype: MonotypeId| {
            let foreign = Foreign::Operator(operator).interned();
            Expression::new(ExpressionKind::Foreign { foreign, arguments }, monotype)
        };
        let one = Expression::new(ExpressionKind::Literal(Literal::Int(1)), int);
        let empty = Expression::new(
            ExpressionKind::Construct { data: data.clone(), constructor: 0, arguments: vec![] },
            tree,
        );
        let recurse = |from: Expression, to: Expression| {
            let arguments = vec![keys.expression(), values.expression(), from, to];
            call(id, arguments, tree)
        };
        let after_middle = operator(Operator::IntAdd, vec![middle.expression(), one.clone()], int);
        let node = Expression::new(
            ExpressionKind::Construct {
                data: data.clone(),
                constructor: 1,
                arguments: vec![
                    hash_map(HashMapOperation::BalancedHeight, vec![count.expression()], int),
                    count.expression(),
                    key.expression(),
                    operator(
                        Operator::ArrayIndex,
                        vec![values.expression(), middle.expression()],
                        shape.value,
                    ),
                    recurse(low.expression(), middle.expression()),
                    recurse(after_middle, high.expression()),
                ],
            },
            tree,
        );
        let sum = operator(Operator::IntAdd, vec![low.expression(), high.expression()], int);
        let bindings = vec![
            Binding {
                local: middle.clone(),
                value: operator(Operator::IntShiftRight, vec![sum, one], int),
            },
            Binding {
                local: key.clone(),
                value: operator(
                    Operator::ArrayIndex,
                    vec![keys.expression(), middle.expression()],
                    shape.key,
                ),
            },
            Binding {
                local: count.clone(),
                value: operator(
                    Operator::IntSubtract,
                    vec![high.expression(), low.expression()],
                    int,
                ),
            },
        ];
        let filled = Expression::new(ExpressionKind::Let { bindings, body: Box::new(node) }, tree);
        let equal = Foreign::Operator(Operator::Compare(crate::foreign::Comparison::Equal));
        let ended = Expression::new(
            ExpressionKind::Foreign {
                foreign: equal.interned(),
                arguments: vec![low.expression(), high.expression()],
            },
            boolean,
        );
        let body = Expression::new(
            ExpressionKind::If {
                condition: Box::new(ended),
                then: Box::new(empty),
                otherwise: Box::new(filled),
            },
            tree,
        );
        self.defined("treeFromKeys", vec![keys, values, low, high], tree, body)
    }

    /// `treeFromTable table`: the tree of a Go map's entries, sorted once by key.
    fn tree_of_table(&mut self, build: FunctionId, tree: MonotypeId, hash: MonotypeId) -> Function {
        let shape = self.shapes[&tree];
        let int = self.monotypes.intern(Monotype::Int);
        let keys_type = self.monotypes.intern(Monotype::Array(shape.key));
        let values_type = self.monotypes.intern(Monotype::Array(shape.value));
        let entries_type = self.monotypes.intern(Monotype::Record(
            vec![
                RecordField { label: SmolStr::new("keys"), monotype: keys_type },
                RecordField { label: SmolStr::new("values"), monotype: values_type },
            ]
            .into(),
        ));
        let table = self.fresh("table", hash);
        let entries = self.fresh("entries", entries_type);
        let keys = self.fresh("keys", keys_type);
        let values = self.fresh("values", values_type);
        let arguments = vec![table.expression()];
        let sorted = hash_map(HashMapOperation::SortedEntries, arguments, entries_type);
        let field = |label: &str, monotype: MonotypeId| {
            let record = Box::new(entries.expression());
            Expression::new(ExpressionKind::Access { record, label: SmolStr::new(label) }, monotype)
        };
        let length = Expression::new(
            ExpressionKind::Foreign {
                foreign: Foreign::Operator(Operator::ArrayLength).interned(),
                arguments: vec![keys.expression()],
            },
            int,
        );
        let zero = Expression::new(ExpressionKind::Literal(Literal::Int(0)), int);
        let arguments = vec![keys.expression(), values.expression(), zero, length];
        let built = call(build, arguments, tree);
        let bindings = vec![
            Binding { local: entries.clone(), value: sorted },
            Binding { local: keys.clone(), value: field("keys", keys_type) },
            Binding { local: values.clone(), value: field("values", values_type) },
        ];
        let body = Expression::new(ExpressionKind::Let { bindings, body: Box::new(built) }, tree);
        self.defined("treeFromTable", vec![table], tree, body)
    }

    /// `tableFromTreeInto tree table`: `table` with the entries of `tree` added.
    fn table_filler(
        &mut self,
        id: FunctionId,
        data: &DataType,
        tree: MonotypeId,
        hash: MonotypeId,
    ) -> Function {
        let shape = self.shapes[&tree];
        let int = self.monotypes.intern(Monotype::Int);
        let node = self.fresh("node", tree);
        let table = self.fresh("table", hash);
        let key = self.fresh("key", shape.key);
        let value = self.fresh("value", shape.value);
        let left = self.fresh("left", tree);
        let right = self.fresh("right", tree);
        let wildcard = |monotype| Pattern { kind: PatternKind::Wildcard, monotype };
        let with_left = call(id, vec![left.expression(), table.expression()], hash);
        let added = hash_map(
            HashMapOperation::Insert,
            vec![key.expression(), value.expression(), with_left],
            hash,
        );
        let with_right = call(id, vec![right.expression(), added], hash);
        let alternatives = vec![
            alternative(constructor(data, 0, vec![], tree), table.expression()),
            alternative(
                constructor(
                    data,
                    1,
                    vec![
                        wildcard(int),
                        wildcard(int),
                        variable(&key),
                        variable(&value),
                        variable(&left),
                        variable(&right),
                    ],
                    tree,
                ),
                with_right,
            ),
        ];
        let body = Expression::new(
            ExpressionKind::Case { scrutinees: vec![node.expression()], alternatives },
            hash,
        );
        self.defined("tableFromTreeInto", vec![node, table], hash, body)
    }

    /// `tableFromTree tree`: a Go map of the tree's entries, made for as many.
    fn table_of_tree(
        &mut self,
        fill: FunctionId,
        data: &DataType,
        tree: MonotypeId,
        hash: MonotypeId,
    ) -> Function {
        let int = self.monotypes.intern(Monotype::Int);
        let node = self.fresh("tree", tree);
        let size = self.fresh("size", int);
        let wildcard = |monotype| Pattern { kind: PatternKind::Wildcard, monotype };
        let zero = Expression::new(ExpressionKind::Literal(Literal::Int(0)), int);
        let shape = self.shapes[&tree];
        let counted = Expression::new(
            ExpressionKind::Case {
                scrutinees: vec![node.expression()],
                alternatives: vec![
                    alternative(constructor(data, 0, vec![], tree), zero),
                    alternative(
                        constructor(
                            data,
                            1,
                            vec![
                                wildcard(int),
                                variable(&size),
                                wildcard(shape.key),
                                wildcard(shape.value),
                                wildcard(tree),
                                wildcard(tree),
                            ],
                            tree,
                        ),
                        size.expression(),
                    ),
                ],
            },
            int,
        );
        let made = hash_map(HashMapOperation::New, vec![counted], hash);
        let body = call(fill, vec![node.expression(), made], hash);
        self.defined("tableFromTree", vec![node], hash, body)
    }
}
