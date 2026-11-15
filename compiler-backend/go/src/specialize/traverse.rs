use checking::core::Type;
use checking::{TypeId, tree};
use files::FileId;
use indexing::TermItemId;
use smol_str::SmolStr;

use super::{Scope, Specializer};
use crate::error::GoResult;
use crate::foreign::{self, Foreign, Operator};
use crate::mono::{Expression, ExpressionKind, Literal, Local};
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
        Ok(foreign::foreign_import(&module.name, &name) == Some(Foreign::Identity)
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
        let accumulated = self.monotypes.result_after(apply.monotype, 2);
        let step = self.monotypes.result_after(function, 1);

        let function = self.fresh_local(SmolStr::new_static("function"), function);
        let array = self.fresh_local(SmolStr::new_static("array"), input);
        let append = self.fresh_local(SmolStr::new_static("append"), snoc);
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
        let snocs = self.monotypes.result_after(map.monotype, 2);
        let snocs = apply_to(map, vec![append.expression(), accumulator.expression()], snocs);
        let result = apply_to(function.expression(), vec![current.expression()], step);
        let snocced = apply_to(apply, vec![snocs, result], accumulated);
        let step = self.lambda(vec![accumulator, current], snocced);
        let fold = match self.monotypes.get(accumulated) {
            Monotype::Effect(_) => foreign::effect_fold(),
            _ => foreign::array_fold(),
        };
        let fold =
            ExpressionKind::Foreign { foreign: fold, arguments: vec![step, initial, remaining] };
        let fold = Expression::new(fold, accumulated);

        let allocated = self.monotypes.intern(Monotype::Effect(snoc));
        let allocate = ExpressionKind::Foreign { foreign: foreign::APPENDER, arguments: vec![] };
        let folded = self.monotypes.intern(Monotype::Effect(accumulated));
        let traversed = ExpressionKind::EffectBind {
            action: Box::new(Expression::new(allocate, allocated)),
            local: append,
            body: Box::new(Expression::new(ExpressionKind::EffectPure(Box::new(fold)), folded)),
        };
        let traversed = ExpressionKind::Foreign {
            foreign: Foreign::RunEffect,
            arguments: vec![Expression::new(traversed, folded)],
        };
        let traversed = Expression::new(traversed, accumulated);
        let traverse = self.lambda(vec![function, array], traversed);

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
        let Type::Application(_, elements) = *self.context.types.lookup(result) else {
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

    fn array_head(&mut self, array: &Local) -> Expression {
        let Monotype::Array(element) = *self.monotypes.get(array.monotype) else {
            unreachable!("invariant violated: a traversed array is an array")
        };
        let integer = self.monotypes.intern(Monotype::Int);
        let first = Expression::new(ExpressionKind::Literal(Literal::Int(0)), integer);
        let index = ExpressionKind::Foreign {
            foreign: Foreign::Operator(Operator::ArrayIndex),
            arguments: vec![array.expression(), first],
        };
        Expression::new(index, element)
    }

    fn array_tail(&mut self, array: &Local) -> Expression {
        let integer = self.monotypes.intern(Monotype::Int);
        let second = Expression::new(ExpressionKind::Literal(Literal::Int(1)), integer);
        let length = ExpressionKind::Foreign {
            foreign: Foreign::Operator(Operator::ArrayLength),
            arguments: vec![array.expression()],
        };
        let length = Expression::new(length, integer);
        let tail = ExpressionKind::Foreign {
            foreign: foreign::ARRAY_SLICE,
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
