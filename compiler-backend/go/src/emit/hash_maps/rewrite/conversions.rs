//! The functions that turn a Go map into the balanced tree and back, one pair per map type.
//!
//! The tree of a Go map is built from its keys in ascending order, the middle key at the root,
//! so that every node is balanced and its height is the bit length of its size. A Go map of a
//! tree is filled by walking the tree, made for as many entries as the tree holds.

use super::{
    Conversions, Rewrite, alternative, call, constructor, hash_map, placeholder_function, variable,
};
use crate::foreign::{Foreign, Operator};
use crate::maps::HashMapOperation;
use crate::monomorphic::{
    Binding, Expression, ExpressionKind, Function, FunctionId, Literal, Local, Pattern, PatternKind,
};
use crate::monotype::{DataType, Monotype, MonotypeId};
use smol_str::SmolStr;

impl Rewrite<'_> {
    /// The functions that turn a Go map of the tree type into the tree and back, made at first
    /// need.
    pub(super) fn conversions(&mut self, tree: MonotypeId) -> Conversions {
        if let Some(&conversions) = self.conversions.get(&tree) {
            return conversions;
        }
        let hash = self.hash_type(tree);
        let Monotype::Data(data) = self.monotypes.get(tree).clone() else {
            unreachable!("invariant violated: a map type is no data type")
        };
        let unit = self.unit();
        let build = self.add_function(placeholder_function(unit));
        let to_tree = self.add_function(placeholder_function(unit));
        let fill = self.add_function(placeholder_function(unit));
        let from_tree = self.add_function(placeholder_function(unit));
        let built = self.tree_builder(build, &data, tree, hash);
        self.program.functions[build.0 as usize] = built;
        let converted = self.tree_of_table(build, tree, hash);
        self.program.functions[to_tree.0 as usize] = converted;
        let filled = self.table_filler(fill, &data, tree, hash);
        self.program.functions[fill.0 as usize] = filled;
        let converted = self.table_of_tree(fill, &data, tree, hash);
        self.program.functions[from_tree.0 as usize] = converted;
        let conversions = Conversions { to_tree, from_tree };
        self.conversions.insert(tree, conversions);
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

    /// `treeFromKeys keys table low high`: the balanced tree of the entries of `table` under
    /// `keys[low:high]`, which ascend.
    fn tree_builder(
        &mut self,
        id: FunctionId,
        data: &DataType,
        tree: MonotypeId,
        hash: MonotypeId,
    ) -> Function {
        let shape = self.shapes[&tree];
        let int = self.monotypes.intern(Monotype::Int);
        let boolean = self.monotypes.intern(Monotype::Boolean);
        let keys_type = self.monotypes.intern(Monotype::Array(shape.key));
        let keys = self.fresh("keys", keys_type);
        let table = self.fresh("table", hash);
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
            let arguments = vec![keys.expression(), table.expression(), from, to];
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
                    hash_map(
                        HashMapOperation::Get,
                        vec![key.expression(), table.expression()],
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
        self.defined("treeFromKeys", vec![keys, table, low, high], tree, body)
    }

    /// `treeFromTable table`: the tree of a Go map's entries.
    fn tree_of_table(&mut self, build: FunctionId, tree: MonotypeId, hash: MonotypeId) -> Function {
        let shape = self.shapes[&tree];
        let int = self.monotypes.intern(Monotype::Int);
        let keys_type = self.monotypes.intern(Monotype::Array(shape.key));
        let table = self.fresh("table", hash);
        let keys = self.fresh("keys", keys_type);
        let sorted = hash_map(HashMapOperation::SortedKeys, vec![table.expression()], keys_type);
        let length = Expression::new(
            ExpressionKind::Foreign {
                foreign: Foreign::Operator(Operator::ArrayLength).interned(),
                arguments: vec![keys.expression()],
            },
            int,
        );
        let zero = Expression::new(ExpressionKind::Literal(Literal::Int(0)), int);
        let built = call(build, vec![keys.expression(), table.expression(), zero, length], tree);
        let bindings = vec![Binding { local: keys, value: sorted }];
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
