use rustc_hash::{FxHashMap, FxHashSet};

use super::iteration::Found;
use super::{Emitter, binary, builtin_call, call, identifier_expression};
use crate::error::GoResult;
use crate::foreign::{Comparison, Foreign, GoFunction, Operator};
use crate::monomorphic::traversal::{
    for_each_binder_mut, for_each_child_mut, free_locals, mentions_local, rename_local,
};
use crate::monomorphic::{
    Expression, ExpressionKind, Guarded, Literal, Local, LocalId, PatternKind,
};
use crate::monotype::Monotype;
use crate::purity::is_trivial;
use crate::syntax::{
    GoBinaryOperator, GoBuiltin, GoCase, GoExpression, GoPackage, GoStatement, GoType,
    GoUnaryOperator,
};

const INLINING_DEPTH: usize = 4;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Primitive {
    Int,
    Char,
    String,
    Number,
}

struct Ordering<'e> {
    parameters: [&'e Local; 2],
    keys: [Expression; 2],
    primitive: Primitive,
}

struct ThreeWay<'e> {
    left: &'e Expression,
    right: &'e Expression,
    constructors: [usize; 3],
}

impl Ordering<'_> {
    fn is_identity(&self) -> bool {
        matches!(self.keys[0].kind, ExpressionKind::Local(id) if id == self.parameters[0].id)
    }

    fn is_reversed_identity(&self) -> bool {
        let [first, second] = self.parameters.map(|parameter| parameter.id);
        matches!(self.keys[0].kind, ExpressionKind::Local(id) if id == second)
            && matches!(self.keys[1].kind, ExpressionKind::Local(id) if id == first)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Placement {
    Copied,
    InPlace,
}

impl<'p, 'q, Q> Emitter<'p, '_, 'q, Q>
where
    Q: checking::ExternalQueries,
{
    pub(super) fn primitive_sort(
        &mut self,
        arguments: &[Expression],
        placement: Placement,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<Option<GoExpression>> {
        let [compare, from_ordering, array] = arguments else { return Ok(None) };
        let Some(ordering) = self.primitive_ordering(compare, from_ordering) else {
            return Ok(None);
        };
        let identity = ordering.is_identity();
        let reversed = ordering.primitive != Primitive::Number && ordering.is_reversed_identity();
        if ordering.primitive == Primitive::Number && !identity {
            return Ok(None);
        }
        let element = match (placement, self.monotypes.get(array.monotype)) {
            (Placement::Copied, Monotype::Array(element))
            | (Placement::InPlace, Monotype::MutableArray(element)) => *element,
            _ => return Ok(None),
        };
        let element_type = self.go_type(element)?;
        if !identity && !reversed {
            return self.keyed_sort(&ordering, &element_type, array, placement, out).map(Some);
        }
        let array = self.value(array, out)?;
        let (result, sorted_expression) = match placement {
            Placement::Copied if ordering.primitive == Primitive::Number => {
                let sort = self.support_function("sortNumbers", SORT_NUMBERS_SOURCE);
                return Ok(Some(call(identifier_expression(&sort), vec![array])));
            }
            Placement::Copied => {
                let sorted = self.temporary("sorted");
                out.push(GoStatement::Define {
                    names: vec![sorted.clone()],
                    values: vec![self.slices("Clone", vec![array])],
                });
                (identifier_expression(&sorted), identifier_expression(&sorted))
            }
            Placement::InPlace => {
                let array = self.hoist(array, "array", out);
                let elements = GoExpression::Unary {
                    operator: GoUnaryOperator::Dereference,
                    operand: Box::new(array.clone()),
                };
                (array, elements)
            }
        };
        if ordering.primitive == Primitive::Number {
            let sort = self.support_function("sortNumbers", SORT_NUMBERS_SOURCE);
            let sorted = call(identifier_expression(&sort), vec![sorted_expression.clone()]);
            let copied = builtin_call(GoBuiltin::Copy, vec![sorted_expression, sorted]);
            out.push(GoStatement::Expression(copied));
            return Ok(Some(result));
        }
        let sort = match ordering.primitive {
            Primitive::String => {
                let compare = self
                    .go_function(GoFunction { package: GoPackage::Prim, name: "CompareString" });
                self.slices("SortFunc", vec![sorted_expression.clone(), compare])
            }
            _ => self.slices("Sort", vec![sorted_expression.clone()]),
        };
        out.push(GoStatement::Expression(sort));
        if reversed {
            out.push(GoStatement::Expression(self.slices("Reverse", vec![sorted_expression])));
        }
        Ok(Some(result))
    }

    /// A stable sort by a key of each element. An ascending Int, Char or enumeration key is read
    /// once per element and the (key, position) pairs merge sorted with the keys compared inline;
    /// a String key, which compares by UTF-16 code units, or a descending one, goes through the
    /// runtime's merge sort.
    fn keyed_sort(
        &mut self,
        ordering: &Ordering<'_>,
        element_type: &GoType,
        array: &Expression,
        placement: Placement,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<GoExpression> {
        let descending = free_locals(&ordering.keys[0]).contains(&ordering.parameters[1].id);
        if ordering.primitive == Primitive::String || descending {
            let comparator = self.key_comparator(ordering, element_type)?;
            let array = self.value(array, out)?;
            let name = match placement {
                Placement::Copied => "SortBy",
                Placement::InPlace => "SortByMutable",
            };
            let sort = self.go_function(GoFunction { package: GoPackage::Direct, name });
            return Ok(call(sort, vec![array, comparator]));
        }
        let key = self.key_function(ordering, element_type)?;
        let array = self.value(array, out)?;
        let sort = identifier_expression(&self.support_function("sortByKey", SORT_BY_KEY_SOURCE));
        match placement {
            Placement::Copied => Ok(call(sort, vec![array, key])),
            Placement::InPlace => {
                let array = self.hoist(array, "array", out);
                let elements = GoExpression::Unary {
                    operator: GoUnaryOperator::Dereference,
                    operand: Box::new(array.clone()),
                };
                let sorted = call(sort, vec![elements.clone(), key]);
                let copied = builtin_call(GoBuiltin::Copy, vec![elements, sorted]);
                out.push(GoStatement::Expression(copied));
                Ok(array)
            }
        }
    }

    /// `func(element T) K`: the key an ordering compares the elements by.
    fn key_function(
        &mut self,
        ordering: &Ordering<'_>,
        element_type: &GoType,
    ) -> GoResult<GoExpression> {
        let saved = self.tail_loop.take();
        let name = self.bind_local(ordering.parameters[0]);
        let mut body = vec![];
        let key = self.value(&ordering.keys[0], &mut body);
        self.tail_loop = saved;
        body.push(GoStatement::Return(Some(key?)));
        let result = self.go_type(ordering.keys[0].monotype)?;
        let parameters = vec![(name, element_type.clone())];
        Ok(GoExpression::Function { parameters, result: Some(result), body })
    }

    /// `sortBy compare xs` with a comparison the backend cannot read as primitive keys: the
    /// runtime's merge sort, whose comparator turns `compare`'s Ordering into an int at once.
    pub(super) fn ordering_sort(
        &mut self,
        arguments: &[Expression],
        placement: Placement,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<GoExpression> {
        let [compare, from_ordering, array] = arguments else {
            unreachable!("invariant violated: sortBy has three arguments")
        };
        let array_type = self.monotypes.get(array.monotype);
        let (Monotype::Array(element) | Monotype::MutableArray(element)) = *array_type else {
            unreachable!("invariant violated: sortBy sorts an array")
        };
        let element_type = self.go_type(element)?;
        let comparator = self.ordering_comparator(compare, from_ordering, element_type, out)?;
        let array = self.value(array, out)?;
        let name = match placement {
            Placement::Copied => "SortBy",
            Placement::InPlace => "SortByMutable",
        };
        let sort = self.go_function(GoFunction { package: GoPackage::Direct, name });
        Ok(call(sort, vec![array, comparator]))
    }

    /// `func(left, right T) int`: the sign of `fromOrdering (compare left right)`.
    fn ordering_comparator(
        &mut self,
        compare: &Expression,
        from_ordering: &Expression,
        element_type: GoType,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<GoExpression> {
        let ordering = self.monotypes.result_after(compare.monotype, 2);
        let mut body = vec![];
        let (left, right, ordered) = match self.callback(compare, 2) {
            Some(Found::Inline { parameters, body: compared }) => {
                let saved = self.tail_loop.take();
                let [left, right] = [parameters[0], parameters[1]].map(|parameter| {
                    match mentions_local(compared, parameter.id) {
                        true => self.bind_local(parameter),
                        false => "_".to_string(),
                    }
                });
                let ordered = self.value(compared, &mut body);
                self.tail_loop = saved;
                (left, right, ordered?)
            }
            _ => {
                let compared = self.uncurried_callback(compare, 2, false, out)?;
                let compared = self.shared(compared, "compare", out);
                let left = self.temporary("left");
                let right = self.temporary("right");
                let arguments = vec![identifier_expression(&left), identifier_expression(&right)];
                (left, right, call(compared, arguments))
            }
        };
        let signs = (0..3).map(|constructor| sign(from_ordering, constructor));
        let signs: Option<Vec<i64>> = signs.collect();
        let decided = match (self.monotypes.get(ordering).clone(), signs) {
            (Monotype::Data(data), Some(signs)) => {
                let mut cases = vec![];
                let mut constant = None;
                for (constructor, sign) in signs.into_iter().enumerate() {
                    let value = self.construct(&data, constructor, vec![])?;
                    if is_same_constant(&ordered, &value) {
                        constant = Some(sign);
                    }
                    if sign == 0 {
                        continue;
                    }
                    let body = vec![GoStatement::Return(Some(GoExpression::Integer(sign)))];
                    cases.push(GoCase { values: vec![value], body, line: None });
                }
                match constant {
                    Some(sign) => vec![GoStatement::Return(Some(GoExpression::Integer(sign)))],
                    None => vec![
                        GoStatement::Switch { value: Some(ordered), cases, default: None },
                        GoStatement::Return(Some(GoExpression::Integer(0))),
                    ],
                }
            }
            _ => {
                let converted = self.uncurried_callback(from_ordering, 1, false, out)?;
                vec![GoStatement::Return(Some(call(converted, vec![ordered])))]
            }
        };
        body.extend(decided);
        let parameters = vec![(left, element_type.clone()), (right, element_type)];
        Ok(GoExpression::Function { parameters, result: Some(GoType::Int), body })
    }

    pub(super) fn slices(&mut self, name: &str, arguments: Vec<GoExpression>) -> GoExpression {
        let function = self.qualified(GoPackage::Slices, name);
        call(function, arguments)
    }

    fn key_comparator(
        &mut self,
        ordering: &Ordering<'_>,
        element_type: &GoType,
    ) -> GoResult<GoExpression> {
        let saved = self.tail_loop.take();
        let names = ordering.parameters.map(|parameter| self.bind_local(parameter));
        let mut body = vec![];
        let outcome = self.key_comparison(ordering, &mut body);
        self.tail_loop = saved;
        outcome?;
        let parameters = names.into_iter().map(|name| (name, element_type.clone())).collect();
        Ok(GoExpression::Function { parameters, result: Some(GoType::Int), body })
    }

    fn key_comparison(
        &mut self,
        ordering: &Ordering<'_>,
        body: &mut Vec<GoStatement>,
    ) -> GoResult<()> {
        let [left, right] = &ordering.keys;
        let left = self.value(left, body)?;
        let left = self.hoist(left, "key", body);
        let right = self.value(right, body)?;
        let right = self.hoist(right, "key", body);
        if ordering.primitive == Primitive::String {
            let compare_string = GoFunction { package: GoPackage::Prim, name: "CompareString" };
            let compare = self.go_function(compare_string);
            body.push(GoStatement::Return(Some(call(compare, vec![left, right]))));
            return Ok(());
        }
        let decided = |operator, sign| GoStatement::If {
            condition: binary(operator, left.clone(), right.clone()),
            then: vec![GoStatement::Return(Some(GoExpression::Integer(sign)))],
            otherwise: vec![],
        };
        body.push(decided(GoBinaryOperator::LessThan, -1));
        body.push(decided(GoBinaryOperator::GreaterThan, 1));
        body.push(GoStatement::Return(Some(GoExpression::Integer(0))));
        Ok(())
    }

    fn primitive_ordering<'e>(
        &self,
        compare: &'e Expression,
        from_ordering: &Expression,
    ) -> Option<Ordering<'e>>
    where
        'p: 'e,
    {
        let mut aliases = FxHashMap::default();
        let mut hidden = FxHashSet::default();
        let (parameters, body) = match self.callback(compare, 2)? {
            Found::Inline { parameters, body } => ([parameters[0], parameters[1]], body),
            Found::Direct { callee, leading, .. } => {
                let function = self.program.function(callee);
                let (bound, compared) = function.parameters.split_at(leading.len());
                for (parameter, argument) in bound.iter().zip(leading) {
                    if !is_trivial(argument) {
                        return None;
                    }
                    aliases.insert(parameter.id, argument);
                    hidden.insert(parameter.id);
                }
                ([&compared[0], &compared[1]], &function.body)
            }
        };
        let three_way = self.three_way(body, &mut aliases, &mut hidden, INLINING_DEPTH)?;
        let signs = three_way.constructors.map(|constructor| sign(from_ordering, constructor));
        let (left, right) = match signs {
            [Some(-1), Some(0), Some(1)] => (three_way.left, three_way.right),
            [Some(1), Some(0), Some(-1)] => (three_way.right, three_way.left),
            _ => return None,
        };
        let primitive = match self.monotypes.get(left.monotype) {
            Monotype::Int => Primitive::Int,
            Monotype::Char => Primitive::Char,
            Monotype::String => Primitive::String,
            Monotype::Number => Primitive::Number,
            // Go's constants of an enumeration count up in the order of its constructors.
            Monotype::Data(data) if self.monotypes.enumeration_size(data).is_some() => {
                Primitive::Int
            }
            _ => return None,
        };
        let keys = [substituted(left, &aliases), substituted(right, &aliases)];
        let free = [free_locals(&keys[0]), free_locals(&keys[1])];
        if free.iter().flatten().any(|id| hidden.contains(id)) {
            return None;
        }
        let [first, second] = parameters.map(|parameter| parameter.id);
        let swapped = free[0].contains(&second);
        let (first, second) = if swapped { (second, first) } else { (first, second) };
        if free[0].contains(&second) || free[1].contains(&first) {
            return None;
        }
        same_but_for_binders(&keys[0], renamed(&keys[1], second, first)).then_some(Ordering {
            parameters,
            keys,
            primitive,
        })
    }

    fn three_way<'e>(
        &self,
        body: &'e Expression,
        aliases: &mut FxHashMap<LocalId, &'e Expression>,
        hidden: &mut FxHashSet<LocalId>,
        depth: usize,
    ) -> Option<ThreeWay<'e>>
    where
        'p: 'e,
    {
        match &body.kind {
            ExpressionKind::Let { bindings, body } => {
                for binding in bindings {
                    let value = resolved(&binding.value, aliases);
                    aliases.insert(binding.local.id, value);
                    hidden.insert(binding.local.id);
                }
                self.three_way(body, aliases, hidden, depth)
            }
            ExpressionKind::Apply { function, arguments } if depth > 0 => {
                let ExpressionKind::Function(id) = function.kind else { return None };
                let callee = self.program.function(id);
                if callee.parameters.len() != arguments.len() {
                    return None;
                }
                for (parameter, argument) in callee.parameters.iter().zip(arguments) {
                    let value = resolved(argument, aliases);
                    aliases.insert(parameter.id, value);
                    hidden.insert(parameter.id);
                }
                self.three_way(&callee.body, aliases, hidden, depth - 1)
            }
            ExpressionKind::If { condition, then, otherwise } => {
                let ExpressionKind::If { condition: inner, then: second, otherwise: greater } =
                    &otherwise.kind
                else {
                    return None;
                };
                // `if a < b then LT else if a == b then EQ else GT`, or the derived enumeration
                // order `if a == b then EQ else if a < b then LT else GT`.
                let (less_than, equal, less, same) = match compared(condition, Comparison::LessThan)
                {
                    Some(less_than) => {
                        (less_than, compared(inner, Comparison::Equal)?, then, second)
                    }
                    None => (
                        compared(inner, Comparison::LessThan)?,
                        compared(condition, Comparison::Equal)?,
                        second,
                        then,
                    ),
                };
                let operands = [less_than[0], less_than[1], equal[0], equal[1]]
                    .map(|operand| resolved(operand, aliases));
                if operands[0] != operands[2] || operands[1] != operands[3] {
                    return None;
                }
                let constructors = [constructor(less)?, constructor(same)?, constructor(greater)?];
                Some(ThreeWay { left: operands[0], right: operands[1], constructors })
            }
            _ => None,
        }
    }
}

fn is_same_constant(value: &GoExpression, constant: &GoExpression) -> bool {
    match (value, constant) {
        (GoExpression::Identifier(value), GoExpression::Identifier(constant)) => value == constant,
        (
            GoExpression::Qualified { package, name },
            GoExpression::Qualified { package: constant_package, name: constant_name },
        ) => package == constant_package && name == constant_name,
        _ => false,
    }
}

fn compared(condition: &Expression, comparison: Comparison) -> Option<[&Expression; 2]> {
    let ExpressionKind::Foreign { foreign, arguments } = &condition.kind else { return None };
    let Foreign::Operator(Operator::Compare(found)) = foreign else { return None };
    let [left, right] = arguments.as_slice() else { return None };
    (*found == comparison).then_some([left, right])
}

fn constructor(expression: &Expression) -> Option<usize> {
    match &expression.kind {
        ExpressionKind::Construct { constructor, arguments, .. } if arguments.is_empty() => {
            Some(*constructor)
        }
        _ => None,
    }
}

fn sign(from_ordering: &Expression, constructor: usize) -> Option<i64> {
    let ExpressionKind::Lambda { parameters, body } = &from_ordering.kind else { return None };
    let [parameter] = parameters.as_slice() else { return None };
    let ExpressionKind::Case { scrutinees, alternatives } = &body.kind else { return None };
    let [scrutinee] = scrutinees.as_slice() else { return None };
    if !matches!(scrutinee.kind, ExpressionKind::Local(id) if id == parameter.id) {
        return None;
    }
    let chosen = alternatives.iter().find(|alternative| match &alternative.patterns[0].kind {
        PatternKind::Constructor { constructor: matched, .. } => *matched == constructor,
        PatternKind::Wildcard => true,
        _ => false,
    })?;
    let Guarded::Unconditional(value) = &chosen.body else { return None };
    let ExpressionKind::Literal(Literal::Int(sign)) = value.kind else { return None };
    Some(sign.signum())
}

fn resolved<'e>(
    expression: &'e Expression,
    aliases: &FxHashMap<LocalId, &'e Expression>,
) -> &'e Expression {
    let mut current = expression;
    while let ExpressionKind::Local(id) = current.kind
        && let Some(alias) = aliases.get(&id)
    {
        current = alias;
    }
    current
}

fn substituted(expression: &Expression, aliases: &FxHashMap<LocalId, &Expression>) -> Expression {
    let mut substituted = resolved(expression, aliases).clone();
    substitute(&mut substituted, aliases);
    substituted
}

fn substitute(expression: &mut Expression, aliases: &FxHashMap<LocalId, &Expression>) {
    if let ExpressionKind::Local(id) = expression.kind
        && aliases.contains_key(&id)
    {
        *expression = substituted(expression, aliases);
        return;
    }
    for_each_child_mut(expression, &mut |child| substitute(child, aliases));
}

fn renamed(expression: &Expression, from: LocalId, to: LocalId) -> Expression {
    let mut renamed = expression.clone();
    rename_local(&mut renamed, from, to);
    renamed
}

/// Whether two keys are one expression but for the locals each binds inside, as the field that
/// `snd x` and `snd y` take apart from their pairs.
fn same_but_for_binders(key: &Expression, mut other: Expression) -> bool {
    let mut ours = vec![];
    for_each_binder_mut(&mut key.clone(), &mut |local| ours.push(local.clone()));
    let mut theirs = vec![];
    for_each_binder_mut(&mut other, &mut |local| theirs.push(local.id));
    if ours.len() != theirs.len() {
        return false;
    }
    for (from, to) in theirs.into_iter().zip(ours) {
        rename_local(&mut other, from, to.id);
        for_each_binder_mut(&mut other, &mut |local| {
            if local.id == from {
                *local = to.clone();
            }
        });
    }
    other == *key
}

const SORT_NUMBERS_SOURCE: &str = "func {name}(xs []float64) []float64 {
\tsorted := make([]float64, len(xs))
\tcopy(sorted, xs)
\tif len(xs) < 2 {
\t\treturn sorted
\t}
\tscratch := make([]float64, len(xs))
\tcopy(scratch, xs)
\tvar merge func(into []float64, from []float64, low int, high int)
\tmerge = func(into []float64, from []float64, low int, high int) {
\t\tmiddle := low + (high-low)>>1
\t\tif middle-low > 1 {
\t\t\tmerge(from, into, low, middle)
\t\t}
\t\tif high-middle > 1 {
\t\t\tmerge(from, into, middle, high)
\t\t}
\t\ti, j, k := low, middle, low
\t\tfor i < middle && j < high {
\t\t\tif from[i] <= from[j] {
\t\t\t\tinto[k] = from[i]
\t\t\t\ti++
\t\t\t} else {
\t\t\t\tinto[k] = from[j]
\t\t\t\tj++
\t\t\t}
\t\t\tk++
\t\t}
\t\tk += copy(into[k:], from[i:middle])
\t\tcopy(into[k:], from[j:high])
\t}
\tmerge(sorted, scratch, 0, len(xs))
\treturn sorted
}
";

const SORT_BY_KEY_SOURCE: &str = "type {name}Ordered interface {
	~int | ~int8 | ~int16 | ~int32 | ~int64 | ~uint | ~uint8 | ~uint16 | ~uint32 | ~uint64
}

type {name}Entry[K {name}Ordered] struct {
\tkey   K
\tindex int
}

func {name}[T any, K {name}Ordered](xs []T, key func(T) K) []T {
\tentries := make([]{name}Entry[K], len(xs))
\tfor index, x := range xs {
\t\tentries[index] = {name}Entry[K]{key: key(x), index: index}
\t}
\tif len(xs) > 1 {
\t\tscratch := make([]{name}Entry[K], len(xs))
\t\tcopy(scratch, entries)
\t\t{name}Merge(entries, scratch, 0, len(xs))
\t}
\tsorted := make([]T, len(xs))
\tfor index, entry := range entries {
\t\tsorted[index] = xs[entry.index]
\t}
\treturn sorted
}

func {name}Merge[K {name}Ordered](into []{name}Entry[K], from []{name}Entry[K], low int, high int) {
\tmiddle := low + (high-low)>>1
\tif middle-low > 1 {
\t\t{name}Merge(from, into, low, middle)
\t}
\tif high-middle > 1 {
\t\t{name}Merge(from, into, middle, high)
\t}
\ti, j, k := low, middle, low
\tfor i < middle && j < high {
\t\tif from[j].key < from[i].key {
\t\t\tinto[k] = from[j]
\t\t\tj++
\t\t} else {
\t\t\tinto[k] = from[i]
\t\t\ti++
\t\t}
\t\tk++
\t}
\tk += copy(into[k:], from[i:middle])
\tcopy(into[k:], from[j:high])
}
";
