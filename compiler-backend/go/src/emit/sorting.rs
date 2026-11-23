use rustc_hash::{FxHashMap, FxHashSet};

use super::iteration::Found;
use super::{Emitter, binary, call, identifier_expression};
use crate::error::GoResult;
use crate::foreign::{Comparison, Foreign, GoFunction, GoPackage, Operator};
use crate::lift::collect_binders;
use crate::monomorphic::traversal::{for_each_child_mut, visit};
use crate::monomorphic::{
    Expression, ExpressionKind, Guarded, Literal, Local, LocalId, PatternKind,
};
use crate::monotype::Monotype;
use crate::purity::is_trivial;
use crate::syntax::{GoExpression, GoStatement, GoType};

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
        let comparator = match identity || reversed {
            true => None,
            false => Some(self.key_comparator(&ordering, &element_type)?),
        };
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
                let elements =
                    GoExpression::Unary { operator: "*", operand: Box::new(array.clone()) };
                (array, elements)
            }
        };
        if ordering.primitive == Primitive::Number {
            let sort = self.support_function("sortNumbers", SORT_NUMBERS_SOURCE);
            let sorted = call(identifier_expression(&sort), vec![sorted_expression.clone()]);
            let copied = call(identifier_expression("copy"), vec![sorted_expression, sorted]);
            out.push(GoStatement::Expression(copied));
            return Ok(Some(result));
        }
        let sort = match (comparator, ordering.primitive) {
            (Some(comparator), _) => {
                self.slices("SortStableFunc", vec![sorted_expression.clone(), comparator])
            }
            (None, Primitive::String) => {
                let compare = self
                    .go_function(GoFunction { package: GoPackage::Prim, name: "CompareString" });
                self.slices("SortFunc", vec![sorted_expression.clone(), compare])
            }
            (None, _) => self.slices("Sort", vec![sorted_expression.clone()]),
        };
        out.push(GoStatement::Expression(sort));
        if reversed {
            out.push(GoStatement::Expression(self.slices("Reverse", vec![sorted_expression])));
        }
        Ok(Some(result))
    }

    fn slices(&mut self, name: &str, arguments: Vec<GoExpression>) -> GoExpression {
        self.imports.insert("slices".into());
        let function = GoExpression::Qualified { package: "slices".into(), name: name.into() };
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
            let compare =
                self.go_function(GoFunction { package: GoPackage::Prim, name: "CompareString" });
            body.push(GoStatement::Return(Some(call(compare, vec![left, right]))));
            return Ok(());
        }
        let decided = |operator, sign| GoStatement::If {
            condition: binary(operator, left.clone(), right.clone()),
            then: vec![GoStatement::Return(Some(GoExpression::Integer(sign)))],
            otherwise: vec![],
        };
        body.push(decided("<", -1));
        body.push(decided(">", 1));
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
            _ => return None,
        };
        let keys = [substituted(left, &aliases), substituted(right, &aliases)];
        let free = [free_locals(&keys[0]), free_locals(&keys[1])];
        if free.iter().flatten().any(|id| hidden.contains(id)) {
            return None;
        }
        let [first, second] = parameters.map(|parameter| parameter.id);
        let (first, second) =
            if free[0].contains(&second) { (second, first) } else { (first, second) };
        if free[0].contains(&second) || free[1].contains(&first) {
            return None;
        }
        (renamed(&keys[1], second, first) == keys[0]).then_some(Ordering {
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
                let [left, right] = compared(condition, Comparison::LessThan)?;
                let ExpressionKind::If { condition: equal, then: same, otherwise: greater } =
                    &otherwise.kind
                else {
                    return None;
                };
                let [equal_left, equal_right] = compared(equal, Comparison::Equal)?;
                let operands = [left, right, equal_left, equal_right]
                    .map(|operand| resolved(operand, aliases));
                if operands[0] != operands[2] || operands[1] != operands[3] {
                    return None;
                }
                let constructors = [constructor(then)?, constructor(same)?, constructor(greater)?];
                Some(ThreeWay { left: operands[0], right: operands[1], constructors })
            }
            _ => None,
        }
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
    rename(&mut renamed, from, to);
    renamed
}

fn rename(expression: &mut Expression, from: LocalId, to: LocalId) {
    if let ExpressionKind::Local(id) = &mut expression.kind
        && *id == from
    {
        *id = to;
    }
    for_each_child_mut(expression, &mut |child| rename(child, from, to));
}

fn free_locals(expression: &Expression) -> Vec<LocalId> {
    let mut bound = FxHashMap::default();
    collect_binders(expression, &mut bound);
    let mut free = vec![];
    visit(expression, &mut |node| {
        if let ExpressionKind::Local(id) = node.kind
            && !bound.contains_key(&id)
        {
            free.push(id);
        }
    });
    free
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
