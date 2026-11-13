use checking::core::Type;
use checking::{TypeId, tree};
use files::FileId;
use indexing::TermItemId;
use smol_str::SmolStr;

use super::{Scope, Specializer};
use crate::error::GoResult;
use crate::foreign::{self, Foreign};
use crate::mono::{Expression, ExpressionKind, Local};
use crate::monotype::{Monotype, MonotypeId};
use crate::types::Substitution;

struct Traversal {
    function: TypeId,
    input: TypeId,
    elements: TypeId,
    snoc: TypeId,
    rank_two: [TypeId; 3],
}

impl<'q, Q> Specializer<'q, Q>
where
    Q: checking::ExternalQueries,
{
    pub(super) fn is_traverse_array_implementation(
        &mut self,
        (file_id, term): (FileId, TermItemId),
    ) -> GoResult<bool> {
        let module = self.context.module(file_id)?;
        Ok(module.name == "Data.Traversable"
            && module.indexed.items[term].name.as_deref() == Some("traverseArrayImpl"))
    }

    pub(super) fn traverse_array(
        &mut self,
        scope: &mut Scope,
        head: tree::ExpressionId,
        implementation: (FileId, TermItemId),
        instantiations: &Substitution,
        arguments: &[tree::ExpressionId],
    ) -> GoResult<Expression> {
        let traversal = self.traversal(scope, head, implementation, instantiations)?;
        let [apply, map, pure] = traversal.rank_two;
        let apply = self.rank_two_argument(scope, arguments[0], apply)?;
        let map = self.rank_two_argument(scope, arguments[1], map)?;
        let pure = self.rank_two_argument(scope, arguments[2], pure)?;

        let function = self.closed_monotype(scope, traversal.function)?;
        let input = self.closed_monotype(scope, traversal.input)?;
        let elements = self.closed_monotype(scope, traversal.elements)?;
        let snoc = self.closed_monotype(scope, traversal.snoc)?;
        let Monotype::Array(input_element) = *self.monotypes.get(input) else {
            unreachable!("invariant violated: traverseArrayImpl traverses an array")
        };
        let accumulated = self.monotypes.result_after(pure.monotype, 1);
        let step = self.monotypes.result_after(function, 1);

        let function = self.fresh_local(SmolStr::new_static("function"), function);
        let array = self.fresh_local(SmolStr::new_static("array"), input);
        let append = self.fresh_local(SmolStr::new_static("append"), snoc);
        let accumulator = self.fresh_local(SmolStr::new_static("accumulator"), accumulated);
        let element = self.fresh_local(SmolStr::new_static("element"), input_element);

        let snocs = self.monotypes.result_after(map.monotype, 2);
        let snocs = apply_to(map, vec![local(&append), local(&accumulator)], snocs);
        let result = apply_to(local(&function), vec![local(&element)], step);
        let snocced = apply_to(apply, vec![snocs, result], accumulated);
        let step = self.lambda(vec![accumulator, element], snocced);
        let empty = Expression::new(ExpressionKind::Array(vec![]), elements);
        let initial = apply_to(pure, vec![empty], accumulated);
        let fold = ExpressionKind::Foreign {
            foreign: foreign::ARRAY_FOLD,
            arguments: vec![step, initial, local(&array)],
        };
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

        let mut remaining = Vec::with_capacity(arguments.len() - 3);
        for &argument in &arguments[3..] {
            remaining.push(self.expression(scope, argument)?);
        }
        if remaining.is_empty() {
            return Ok(traverse);
        }
        let result = self.monotypes.result_after(traverse.monotype, remaining.len());
        Ok(apply_to(traverse, remaining, result))
    }

    fn traversal(
        &mut self,
        scope: &Scope,
        head: tree::ExpressionId,
        (file_id, term): (FileId, TermItemId),
        instantiations: &Substitution,
    ) -> GoResult<Traversal> {
        let module = self.context.module(file_id)?;
        let declared = module
            .checked
            .lookup_term_item_type(term)
            .unwrap_or(scope.module.checked.tree[head].type_id);
        let mut instantiations = instantiations.clone();
        for instantiation in scope.module.checked.tree.lookup_instantiations(head) {
            let closed = self.context.types.substitute(instantiation.argument, &scope.substitution);
            instantiations.insert(instantiation.name, closed);
        }
        let (_, signature) = self.context.types.peel_quantifiers(declared);
        let signature = self.context.types.substitute(signature, &instantiations);
        let mut parameters = [signature; 5];
        let mut result = signature;
        for parameter in &mut parameters {
            let Some((argument, rest)) = self.context.types.function_parts(result) else {
                unreachable!("invariant violated: traverseArrayImpl takes five arguments")
            };
            *parameter = argument;
            result = rest;
        }
        let [apply, map, pure, function, input] = parameters;
        let Type::Application(_, elements) = *self.context.types.lookup(result) else {
            unreachable!("invariant violated: traverseArrayImpl returns an applicative")
        };
        let Type::Application(_, element) = *self.context.types.lookup(elements) else {
            unreachable!("invariant violated: traverseArrayImpl returns an array")
        };
        let snocced = self.context.queries.intern_type(Type::Function(element, elements));
        let snoc = self.context.queries.intern_type(Type::Function(elements, snocced));
        let rank_two = [
            self.instantiate_rank_two(apply, &[element, elements]),
            self.instantiate_rank_two(map, &[elements, snocced]),
            self.instantiate_rank_two(pure, &[elements]),
        ];
        Ok(Traversal { function, input, elements, snoc, rank_two })
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

fn local(local: &Local) -> Expression {
    Expression::new(ExpressionKind::Local(local.id), local.monotype)
}

fn apply_to(function: Expression, arguments: Vec<Expression>, result: MonotypeId) -> Expression {
    let kind = ExpressionKind::Apply { function: Box::new(function), arguments };
    Expression::new(kind, result)
}
