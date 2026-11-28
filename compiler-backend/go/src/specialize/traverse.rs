use checking::core::Type;
use checking::{TypeId, tree};
use files::FileId;
use indexing::TermItemId;
use smol_str::SmolStr;

use super::{Scope, Specializer};
use crate::error::GoResult;
use crate::foreign::{self, Foreign, Operator};
use crate::monomorphic::{Expression, ExpressionKind, Literal, Local};
use crate::monotype::{Monotype, MonotypeId};
use crate::types::Substitution;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum ArrayTraversal {
    Applicative,
    Apply,
}

impl ArrayTraversal {
    fn rank_two_arguments(self) -> usize {
        match self {
            ArrayTraversal::Applicative => 3,
            ArrayTraversal::Apply => 2,
        }
    }
}

pub(super) struct TraversalReference {
    pub node: tree::ExpressionId,
    pub implementation: (FileId, TermItemId),
    pub traversal: ArrayTraversal,
    pub arguments: usize,
}

struct Traversal {
    function: TypeId,
    input: TypeId,
    element: TypeId,
    elements: TypeId,
    snoc: TypeId,
    apply: TypeId,
    map_snoc: TypeId,
    map_singleton: TypeId,
    pure: Option<TypeId>,
    /// The applicative traversed in, as the source names it: `V`, not the `Either` it erases to.
    applicative: TypeId,
    apply_scheme: TypeId,
    map_scheme: TypeId,
}

impl<'q, Q> Specializer<'q, Q>
where
    Q: checking::ExternalQueries,
{
    pub(super) fn traversal_reference(
        &mut self,
        scope: &Scope,
        head: tree::ExpressionId,
        arguments: &[tree::ExpressionId],
    ) -> GoResult<Option<TraversalReference>> {
        let tree = &scope.module.checked.tree;
        let Some(head_reference) = global_reference(&tree[head].kind) else {
            return Ok(None);
        };
        let (node, implementation, offset) = match self.uncurried_conversion(head_reference)? {
            false => (head, head_reference, 0),
            true => {
                let Some(&argument) = arguments.first() else { return Ok(None) };
                let Some(reference) = global_reference(&tree[argument].kind) else {
                    return Ok(None);
                };
                (argument, reference, 1)
            }
        };
        let module = self.context.module(implementation.0)?;
        let name = module.indexed.items[implementation.1].name.as_deref();
        let traversal = match (module.name.as_str(), name) {
            ("Data.Traversable", Some("traverseArrayImpl")) => ArrayTraversal::Applicative,
            ("Data.Array.NonEmpty.Internal", Some("traverse1Impl")) => ArrayTraversal::Apply,
            _ => return Ok(None),
        };
        if arguments.len() < offset + traversal.rank_two_arguments() {
            return Ok(None);
        }
        Ok(Some(TraversalReference { node, implementation, traversal, arguments: offset }))
    }

    fn uncurried_conversion(&mut self, (file_id, term): (FileId, TermItemId)) -> GoResult<bool> {
        let module = self.context.module(file_id)?;
        let name = module.indexed.items[term].name.clone().unwrap_or_default();
        Ok(foreign::foreign_import(&module.name, &name) == Some(&Foreign::Identity)
            && name.starts_with("runFn"))
    }

    pub(super) fn traverse_array(
        &mut self,
        scope: &mut Scope,
        reference: TraversalReference,
        arguments: &[tree::ExpressionId],
    ) -> GoResult<Expression> {
        let arguments = &arguments[reference.arguments..];
        let traversal = self.traversal(scope, &reference)?;
        let applied = self.closed_monotype(scope, traversal.apply)?;
        let accumulated = self.monotypes.result_after(applied, 2);
        if !matches!(self.monotypes.get(accumulated), Monotype::Effect(_))
            && self.is_parallel_applicative(traversal.applicative)?
        {
            return match reference.traversal {
                ArrayTraversal::Applicative => {
                    self.balanced_traversal(scope, &reference, &traversal, arguments, accumulated)
                }
                ArrayTraversal::Apply => {
                    self.rightward_traversal(scope, &reference, &traversal, arguments, accumulated)
                }
            };
        }
        let apply = self.rank_two_argument(scope, arguments[0], traversal.apply)?;
        let map = self.rank_two_argument(scope, arguments[1], traversal.map_snoc)?;

        let function = self.closed_monotype(scope, traversal.function)?;
        let input = self.closed_monotype(scope, traversal.input)?;
        let element = self.closed_monotype(scope, traversal.element)?;
        let elements = self.closed_monotype(scope, traversal.elements)?;
        let snoc = self.closed_monotype(scope, traversal.snoc)?;
        let Monotype::Array(input_element) = *self.monotypes.get(input) else {
            unreachable!("invariant violated: an array traversal traverses an array")
        };
        let step = self.monotypes.result_after(function, 1);

        let function = self.fresh_local(SmolStr::new_static("function"), function);
        let array = self.fresh_local(SmolStr::new_static("array"), input);
        let append = match self.is_linear_applicative(traversal.applicative, accumulated)? {
            true => None,
            false => Some(self.fresh_local(SmolStr::new_static("append"), snoc)),
        };
        let accumulator = self.fresh_local(SmolStr::new_static("accumulator"), accumulated);
        let current = self.fresh_local(SmolStr::new_static("element"), input_element);

        let (initial, remaining) = match traversal.pure {
            Some(pure) => {
                let pure = self.rank_two_argument(scope, arguments[2], pure)?;
                let empty = Expression::new(ExpressionKind::Array(vec![]), elements);
                (apply_to(pure, vec![empty], accumulated), array.expression())
            }
            None => {
                let map = self.rank_two_argument(scope, arguments[1], traversal.map_singleton)?;
                let first = self.fresh_local(SmolStr::new_static("first"), element);
                let singleton = ExpressionKind::Array(vec![first.expression()]);
                let singleton = Expression::new(singleton, elements);
                let singleton = self.lambda(vec![first], singleton);
                let head = self.array_head(&array);
                let head = apply_to(function.expression(), vec![head], step);
                let initial = apply_to(map, vec![singleton, head], accumulated);
                (initial, self.array_tail(&array))
            }
        };
        let snoc_function = match &append {
            Some(append) => append.expression(),
            None => self.snoc_lambda(elements, element),
        };
        let snocs = self.monotypes.result_after(map.monotype, 2);
        let snocs = apply_to(map, vec![snoc_function, accumulator.expression()], snocs);
        let result = apply_to(function.expression(), vec![current.expression()], step);
        let snocced = apply_to(apply, vec![snocs, result], accumulated);
        let step = self.lambda(vec![accumulator, current], snocced);
        let fold = match self.monotypes.get(accumulated) {
            Monotype::Effect(_) => foreign::effect_fold(),
            _ => foreign::array_fold(),
        };
        let fold_arguments = vec![step, initial, remaining];
        let fold = ExpressionKind::Foreign { foreign: fold, arguments: fold_arguments };
        let fold = Expression::new(fold, accumulated);
        let Some(append) = append else {
            let traverse = self.lambda(vec![function, array], fold);
            return self.supplied(scope, traverse, &reference, arguments);
        };

        let allocated = self.monotypes.intern(Monotype::Effect(snoc));
        let allocate = ExpressionKind::Foreign { foreign: &foreign::APPENDER, arguments: vec![] };
        let folded = self.monotypes.intern(Monotype::Effect(accumulated));
        let traversed = ExpressionKind::EffectBind {
            action: Box::new(Expression::new(allocate, allocated)),
            local: append,
            body: Box::new(Expression::new(ExpressionKind::EffectPure(Box::new(fold)), folded)),
        };
        let traversed = ExpressionKind::Foreign {
            foreign: &Foreign::RunEffect,
            arguments: vec![Expression::new(traversed, folded)],
        };
        let traversed = Expression::new(traversed, accumulated);
        let traverse = self.lambda(vec![function, array], traversed);
        self.supplied(scope, traverse, &reference, arguments)
    }

    fn balanced_traversal(
        &mut self,
        scope: &mut Scope,
        reference: &TraversalReference,
        traversal: &Traversal,
        arguments: &[tree::ExpressionId],
        accumulated: MonotypeId,
    ) -> GoResult<Expression> {
        let function = self.closed_monotype(scope, traversal.function)?;
        let input = self.closed_monotype(scope, traversal.input)?;
        let elements = self.closed_monotype(scope, traversal.elements)?;
        let Monotype::Array(input_element) = *self.monotypes.get(input) else {
            unreachable!("invariant violated: an array traversal traverses an array")
        };
        let function = self.fresh_local(SmolStr::new_static("function"), function);
        let array = self.fresh_local(SmolStr::new_static("array"), input);

        let pure = traversal.pure.expect("invariant violated: an applicative traversal has pure");
        let pure = self.rank_two_argument(scope, arguments[2], pure)?;
        let empty = Expression::new(ExpressionKind::Array(vec![]), elements);
        let none = apply_to(pure, vec![empty], accumulated);

        let mut gathered = Vec::with_capacity(3);
        for count in 1..=3 {
            let inputs = (0..count)
                .map(|_| self.fresh_local(SmolStr::new_static("element"), input_element))
                .collect();
            gathered.push(self.gathered(scope, traversal, arguments, &function, inputs)?);
        }
        let [one, two, three] = <[Expression; 3]>::try_from(gathered)
            .unwrap_or_else(|_| unreachable!("invariant violated: three leaf traversals"));

        let elements_type = traversal.elements;
        let map_scheme = traversal.map_scheme;
        let apply_scheme = traversal.apply_scheme;
        let elements_to_elements = Type::Function(elements_type, elements_type);
        let concatenated = self.context.queries.intern_type(elements_to_elements);
        let map_concat = self.instantiate_rank_two(map_scheme, &[elements_type, concatenated]);
        let map_concat = self.rank_two_argument(scope, arguments[1], map_concat)?;
        let left = self.fresh_local(SmolStr::new_static("init"), elements);
        let right = self.fresh_local(SmolStr::new_static("rest"), elements);
        let appended = ExpressionKind::Foreign {
            foreign: &foreign::ARRAY_APPEND,
            arguments: vec![left.expression(), right.expression()],
        };
        let concat = self.lambda(vec![left, right], Expression::new(appended, elements));
        let half = self.fresh_local(SmolStr::new_static("half"), accumulated);
        let mapped = self.monotypes.result_after(map_concat.monotype, 2);
        let mapped_half = apply_to(map_concat, vec![concat, half.expression()], mapped);
        let map_half = self.lambda(vec![half], mapped_half);

        let apply_concat = self.instantiate_rank_two(apply_scheme, &[elements_type, elements_type]);
        let apply_concat = self.rank_two_argument(scope, arguments[0], apply_concat)?;
        let first = self.fresh_local(SmolStr::new_static("first"), mapped);
        let second = self.fresh_local(SmolStr::new_static("second"), accumulated);
        let halves = vec![first.expression(), second.expression()];
        let joined = apply_to(apply_concat, halves, accumulated);
        let join_halves = self.lambda(vec![first, second], joined);

        let balanced = ExpressionKind::Foreign {
            foreign: &foreign::TRAVERSE_BALANCED,
            arguments: vec![array.expression(), none, one, two, three, map_half, join_halves],
        };
        let balanced = Expression::new(balanced, accumulated);
        let traverse = self.lambda(vec![function, array], balanced);
        self.supplied(scope, traverse, reference, arguments)
    }

    /// JavaScript's `traverse1Impl`: `f` on the last element first, then each one before it
    /// applied onto what follows, `apply (map cons (f x0)) (apply (map cons (f x1)) …)`.
    fn rightward_traversal(
        &mut self,
        scope: &mut Scope,
        reference: &TraversalReference,
        traversal: &Traversal,
        arguments: &[tree::ExpressionId],
        accumulated: MonotypeId,
    ) -> GoResult<Expression> {
        let function = self.closed_monotype(scope, traversal.function)?;
        let input = self.closed_monotype(scope, traversal.input)?;
        let element = self.closed_monotype(scope, traversal.element)?;
        let elements = self.closed_monotype(scope, traversal.elements)?;
        let Monotype::Array(input_element) = *self.monotypes.get(input) else {
            unreachable!("invariant violated: an array traversal traverses an array")
        };
        let step = self.monotypes.result_after(function, 1);
        let function = self.fresh_local(SmolStr::new_static("function"), function);
        let array = self.fresh_local(SmolStr::new_static("array"), input);

        let map_singleton = self.rank_two_argument(scope, arguments[1], traversal.map_singleton)?;
        let only = self.fresh_local(SmolStr::new_static("last"), element);
        let singleton = Expression::new(ExpressionKind::Array(vec![only.expression()]), elements);
        let singleton = self.lambda(vec![only], singleton);
        let last = self.array_last(&array);
        let last = apply_to(function.expression(), vec![last], step);
        let initial = apply_to(map_singleton, vec![singleton, last], accumulated);

        let elements_type = traversal.elements;
        let map_scheme = traversal.map_scheme;
        let apply_scheme = traversal.apply_scheme;
        let elements_to_elements = Type::Function(elements_type, elements_type);
        let prepends = self.context.queries.intern_type(elements_to_elements);
        let map_cons = self.instantiate_rank_two(map_scheme, &[traversal.element, prepends]);
        let map_cons = self.rank_two_argument(scope, arguments[1], map_cons)?;
        let head = self.fresh_local(SmolStr::new_static("head"), element);
        let tail = self.fresh_local(SmolStr::new_static("tail"), elements);
        let headed = Expression::new(ExpressionKind::Array(vec![head.expression()]), elements);
        let prepended = ExpressionKind::Foreign {
            foreign: &foreign::ARRAY_APPEND,
            arguments: vec![headed, tail.expression()],
        };
        let cons = self.lambda(vec![head, tail], Expression::new(prepended, elements));

        let apply_cons = self.instantiate_rank_two(apply_scheme, &[elements_type, elements_type]);
        let apply_cons = self.rank_two_argument(scope, arguments[0], apply_cons)?;
        let current = self.fresh_local(SmolStr::new_static("element"), input_element);
        let rest = self.fresh_local(SmolStr::new_static("rest"), accumulated);
        let result = apply_to(function.expression(), vec![current.expression()], step);
        let mapped = self.monotypes.result_after(map_cons.monotype, 2);
        let mapped = apply_to(map_cons, vec![cons, result], mapped);
        let applied = apply_to(apply_cons, vec![mapped, rest.expression()], accumulated);
        let onto_rest = self.lambda(vec![current, rest], applied);

        let fold = ExpressionKind::Foreign {
            foreign: foreign::array_fold_right(),
            arguments: vec![onto_rest, initial, self.array_init(&array)],
        };
        let fold = Expression::new(fold, accumulated);
        let traverse = self.lambda(vec![function, array], fold);
        self.supplied(scope, traverse, reference, arguments)
    }

    fn gathered(
        &mut self,
        scope: &mut Scope,
        traversal: &Traversal,
        arguments: &[tree::ExpressionId],
        function: &Local,
        inputs: Vec<Local>,
    ) -> GoResult<Expression> {
        let mut remaining = vec![traversal.elements];
        for _ in 1..inputs.len() {
            let last = *remaining.last().expect("invariant violated: remaining is not empty");
            remaining
                .push(self.context.queries.intern_type(Type::Function(traversal.element, last)));
        }
        remaining.reverse();

        let elements = self.closed_monotype(scope, traversal.elements)?;
        let element = self.closed_monotype(scope, traversal.element)?;
        let gathered: Vec<Local> = inputs
            .iter()
            .map(|_| self.fresh_local(SmolStr::new_static("result"), element))
            .collect();
        let array = gathered.iter().map(Local::expression).collect();
        let array = Expression::new(ExpressionKind::Array(array), elements);
        let collect = self.lambda(gathered, array);

        let step = self.monotypes.result_after(function.monotype, 1);
        let results: Vec<Expression> = inputs
            .iter()
            .map(|input| apply_to(function.expression(), vec![input.expression()], step))
            .collect();
        let mut results = results.into_iter();
        let first = results.next().expect("invariant violated: a leaf traverses an element");

        let map_scheme = traversal.map_scheme;
        let apply_scheme = traversal.apply_scheme;
        let map = self.instantiate_rank_two(map_scheme, &[traversal.element, remaining[0]]);
        let map = self.rank_two_argument(scope, arguments[1], map)?;
        let mapped = self.monotypes.result_after(map.monotype, 2);
        let mut combined = apply_to(map, vec![collect, first], mapped);
        for (result, &after) in results.zip(&remaining[1..]) {
            let apply = self.instantiate_rank_two(apply_scheme, &[traversal.element, after]);
            let apply = self.rank_two_argument(scope, arguments[0], apply)?;
            let applied = self.monotypes.result_after(apply.monotype, 2);
            combined = apply_to(apply, vec![combined, result], applied);
        }
        Ok(self.lambda(inputs, combined))
    }

    fn supplied(
        &mut self,
        scope: &mut Scope,
        traverse: Expression,
        reference: &TraversalReference,
        arguments: &[tree::ExpressionId],
    ) -> GoResult<Expression> {
        let rank_two = reference.traversal.rank_two_arguments();
        let mut supplied = Vec::with_capacity(arguments.len() - rank_two);
        for &argument in &arguments[rank_two..] {
            supplied.push(self.expression(scope, argument)?);
        }
        if supplied.is_empty() {
            return Ok(traverse);
        }
        let result = self.monotypes.result_after(traverse.monotype, supplied.len());
        Ok(apply_to(traverse, supplied, result))
    }

    fn traversal(&mut self, scope: &Scope, reference: &TraversalReference) -> GoResult<Traversal> {
        let (file_id, term) = reference.implementation;
        let module = self.context.module(file_id)?;
        let declared = module
            .checked
            .lookup_term_item_type(term)
            .unwrap_or(scope.module.checked.tree[reference.node].type_id);
        let mut instantiations = Substitution::default();
        for instantiation in scope.module.checked.tree.lookup_instantiations(reference.node) {
            let closed = self.context.types.substitute(instantiation.argument, &scope.substitution);
            instantiations.insert(instantiation.name, closed);
        }
        let (_, signature) = self.context.types.peel_quantifiers(declared);
        let signature = self.context.types.substitute(signature, &instantiations);
        let arity = reference.traversal.rank_two_arguments() + 2;
        let (parameters, result) = self.curried_parameters(signature, arity)?;
        let (rank_two, [function, input]) = parameters.split_at(arity - 2) else {
            unreachable!("invariant violated: an array traversal takes a function and an array")
        };
        let Type::Application(applicative, elements) = *self.context.types.lookup(result) else {
            unreachable!("invariant violated: an array traversal returns an applicative")
        };
        let Type::Application(_, element) = *self.context.types.lookup(elements) else {
            unreachable!("invariant violated: an array traversal returns an array")
        };
        let snocced = self.context.queries.intern_type(Type::Function(element, elements));
        let snoc = self.context.queries.intern_type(Type::Function(elements, snocced));
        let pure = match reference.traversal {
            ArrayTraversal::Applicative => {
                Some(self.instantiate_rank_two(rank_two[2], &[elements]))
            }
            ArrayTraversal::Apply => None,
        };
        Ok(Traversal {
            function: *function,
            input: *input,
            element,
            elements,
            snoc,
            apply: self.instantiate_rank_two(rank_two[0], &[element, elements]),
            map_snoc: self.instantiate_rank_two(rank_two[1], &[elements, snocced]),
            map_singleton: self.instantiate_rank_two(rank_two[1], &[element, elements]),
            pure,
            applicative,
            apply_scheme: rank_two[0],
            map_scheme: rank_two[1],
        })
    }

    fn curried_parameters(
        &mut self,
        signature: TypeId,
        arity: usize,
    ) -> GoResult<(Vec<TypeId>, TypeId)> {
        let mut parameters = Vec::with_capacity(arity);
        let mut result = signature;
        while parameters.len() < arity {
            if let Some((argument, rest)) = self.context.types.function_parts(result) {
                parameters.push(argument);
                result = rest;
                continue;
            }
            let (head, arguments) = self.context.types.spine(result);
            let Type::Constructor(file_id, item) = *self.context.types.lookup(head) else {
                unreachable!("invariant violated: an array traversal is a function")
            };
            let module = self.context.module(file_id)?;
            let uncurried = module.name == "Data.Function.Uncurried"
                && module.indexed.items[item]
                    .name
                    .as_deref()
                    .is_some_and(|name| name.starts_with("Fn"));
            let Some((&rest, uncurried_parameters)) = arguments.split_last().filter(|_| uncurried)
            else {
                unreachable!("invariant violated: an array traversal is a function")
            };
            parameters.extend_from_slice(uncurried_parameters);
            result = rest;
        }
        Ok((parameters, result))
    }

    /// Whether the applicative's `apply` resolves the snocing function of a `Right` or `Just`
    /// where it is built, so that the array is appended to in place. A newtype over `Either` with
    /// an `apply` of its own, such as `V`, which also looks at both sides, appends to an
    /// appender instead: through its function the array would be copied at every element.
    fn is_linear_applicative(
        &mut self,
        applicative: TypeId,
        accumulated: MonotypeId,
    ) -> GoResult<bool> {
        let Monotype::Data(_) = self.monotypes.get(accumulated) else { return Ok(false) };
        let (head, _) = self.context.types.spine(applicative);
        let Type::Constructor(file_id, item) = *self.context.types.lookup(head) else {
            return Ok(false);
        };
        Ok(self.context.is_type(file_id, item, "Data.Maybe", "Maybe")?
            || self.context.is_type(file_id, item, "Data.Either", "Either")?)
    }

    /// A parallel applicative runs or combines its applies in an order a
    /// program can observe, so it is traversed in JavaScript's balanced tree.
    /// Every other applicative is lawful enough that the tree's shape cannot
    /// be seen, and keeps the left fold. ParAff, an effect here, has its own
    /// parallel traversal (aff.TraverseParArrayDirect).
    fn is_parallel_applicative(&mut self, applicative: TypeId) -> GoResult<bool> {
        let (head, _) = self.context.types.spine(applicative);
        let Type::Constructor(file_id, item) = *self.context.types.lookup(head) else {
            return Ok(false);
        };
        Ok(self.context.is_type(file_id, item, "Yoga.Om", "ParOm")?)
    }

    fn snoc_lambda(&mut self, elements: MonotypeId, element: MonotypeId) -> Expression {
        let init = self.fresh_local(SmolStr::new_static("init"), elements);
        let last = self.fresh_local(SmolStr::new_static("last"), element);
        let snocced = ExpressionKind::Foreign {
            foreign: &Foreign::Snoc,
            arguments: vec![init.expression(), last.expression()],
        };
        let snocced = self.lambda(vec![last], Expression::new(snocced, elements));
        self.lambda(vec![init], snocced)
    }

    fn array_head(&mut self, array: &Local) -> Expression {
        let Monotype::Array(element) = *self.monotypes.get(array.monotype) else {
            unreachable!("invariant violated: a traversed array is an array")
        };
        let integer = self.monotypes.intern(Monotype::Int);
        let first = Expression::new(ExpressionKind::Literal(Literal::Int(0)), integer);
        let index = ExpressionKind::Foreign {
            foreign: &Foreign::Operator(Operator::ArrayIndex),
            arguments: vec![array.expression(), first],
        };
        Expression::new(index, element)
    }

    fn array_last(&mut self, array: &Local) -> Expression {
        let Monotype::Array(element) = *self.monotypes.get(array.monotype) else {
            unreachable!("invariant violated: a traversed array is an array")
        };
        let index = ExpressionKind::Foreign {
            foreign: &Foreign::Operator(Operator::ArrayIndex),
            arguments: vec![array.expression(), self.last_index(array)],
        };
        Expression::new(index, element)
    }

    fn array_init(&mut self, array: &Local) -> Expression {
        let integer = self.monotypes.intern(Monotype::Int);
        let first = Expression::new(ExpressionKind::Literal(Literal::Int(0)), integer);
        let init = ExpressionKind::Foreign {
            foreign: &foreign::ARRAY_SLICE,
            arguments: vec![first, self.last_index(array), array.expression()],
        };
        Expression::new(init, array.monotype)
    }

    fn last_index(&mut self, array: &Local) -> Expression {
        let integer = self.monotypes.intern(Monotype::Int);
        let length = ExpressionKind::Foreign {
            foreign: &Foreign::Operator(Operator::ArrayLength),
            arguments: vec![array.expression()],
        };
        let one = Expression::new(ExpressionKind::Literal(Literal::Int(1)), integer);
        let last = ExpressionKind::Foreign {
            foreign: &Foreign::Operator(Operator::IntSubtract),
            arguments: vec![Expression::new(length, integer), one],
        };
        Expression::new(last, integer)
    }

    fn array_tail(&mut self, array: &Local) -> Expression {
        let integer = self.monotypes.intern(Monotype::Int);
        let second = Expression::new(ExpressionKind::Literal(Literal::Int(1)), integer);
        let length = ExpressionKind::Foreign {
            foreign: &Foreign::Operator(Operator::ArrayLength),
            arguments: vec![array.expression()],
        };
        let length = Expression::new(length, integer);
        let tail = ExpressionKind::Foreign {
            foreign: &foreign::ARRAY_SLICE,
            arguments: vec![second, length, array.expression()],
        };
        Expression::new(tail, array.monotype)
    }

    fn instantiate_rank_two(&self, parameter: TypeId, types: &[TypeId]) -> TypeId {
        let (names, body) = self.context.types.peel_quantifiers(parameter);
        let substitution: Substitution = names.into_iter().zip(types.iter().copied()).collect();
        self.context.types.substitute(body, &substitution)
    }

    fn rank_two_argument(
        &mut self,
        scope: &mut Scope,
        argument: tree::ExpressionId,
        expected: TypeId,
    ) -> GoResult<Expression> {
        let tree = &scope.module.checked.tree;
        let mut instantiations = Substitution::default();
        let mut current = argument;
        loop {
            for instantiation in tree.lookup_instantiations(current) {
                instantiations.insert(instantiation.name, instantiation.argument);
            }
            match tree[current].kind {
                tree::ExpressionKind::EvidenceApplication { function, .. } => current = function,
                _ => break,
            }
        }
        let (_, checked) = self.context.types.peel_quantifiers(tree[argument].type_id);
        let checked = self.context.types.substitute(checked, &instantiations);
        let checked = self.context.types.substitute(checked, &scope.substitution);
        let mut skolems = vec![];
        self.context.types.rigid_names(checked, &mut skolems);
        let mut bindings = Substitution::default();
        self.context.types.match_type(checked, expected, &skolems, &mut bindings);
        let outer = scope.substitution.clone();
        scope.substitution.extend(bindings);
        let reference = self.reference(scope, argument, Substitution::default(), Some(expected));
        scope.substitution = outer;
        let reference = reference?;
        let monotype = self.closed_monotype(scope, expected)?;
        Ok(self.coerce(reference, monotype))
    }
}

fn global_reference(kind: &tree::ExpressionKind) -> Option<(FileId, TermItemId)> {
    let tree::ExpressionKind::Variable {
        resolution:
            tree::VariableResolution::Source(lowering::TermVariableResolution::Reference(file_id, term)),
    } = *kind
    else {
        return None;
    };
    Some((file_id, term))
}

fn apply_to(function: Expression, arguments: Vec<Expression>, result: MonotypeId) -> Expression {
    let kind = ExpressionKind::Apply { function: Box::new(function), arguments };
    Expression::new(kind, result)
}
