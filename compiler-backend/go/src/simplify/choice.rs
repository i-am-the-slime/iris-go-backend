//! Case of case. A case whose scrutinee chooses between constructors or
//! literals, through ifs, lets and other cases, is distributed into the
//! choice: each chosen value meets its own copy of the case, which it
//! resolves. The value is then never built, and its tag never tested.

use rustc_hash::FxHashMap;

use super::coverage::{alternatives_size, column_outcomes};
use super::{INLINE_SIZE, Simplifier, substitute};
use crate::foreign::{
    Comparison, Foreign, GoFunction, GoPackage, MUTABLE_PEEK_UNSAFE, MUTABLE_WITHIN, Operator,
};
use crate::monomorphic::traversal::visit;
use crate::monomorphic::{
    Alternative, Binding, Expression, ExpressionKind, Guarded, Literal, Local, LocalId, Pattern,
    PatternKind,
};
use crate::monotype::{DataType, Monotype, MonotypeId, Monotypes};
use crate::purity::{is_trivial, mentions_any};

/// How many more nodes distributing may copy than the case has: alternatives
/// that several chosen values select are copied once for each.
const DUPLICATION: usize = INLINE_SIZE;

/// Alternatives larger than this that several chosen values select become
/// join points rather than copies, when they bind a variable to pass.
const JOIN_SIZE: usize = 10;

impl Simplifier<'_> {
    /// The case distributed into its scrutinee's choice, unless the choice is
    /// not between values the alternatives resolve, or would copy too much;
    /// the scrutinee is taken only when distributed.
    pub(super) fn distribute(
        &mut self,
        scrutinee: &mut Expression,
        alternatives: &[Alternative],
        monotype: MonotypeId,
    ) -> Option<Expression> {
        let (scrutinee, placements) = match &scrutinee.kind {
            ExpressionKind::Foreign { foreign: Foreign::MaybeIndex, arguments } => {
                let choice = self.index_choice(arguments.clone(), scrutinee.monotype)?;
                let placements = plan(&choice, alternatives, self.monotypes)?;
                (choice, placements)
            }
            ExpressionKind::Foreign { foreign: Foreign::UpdateAt, arguments } => {
                let choice = self.update_choice(arguments.clone(), scrutinee.monotype)?;
                let placements = plan(&choice, alternatives, self.monotypes)?;
                (choice, placements)
            }
            ExpressionKind::If { .. }
            | ExpressionKind::Let { .. }
            | ExpressionKind::Case { .. } => {
                if let Some(placements) = plan(scrutinee, alternatives, self.monotypes) {
                    let unit = Expression::new(ExpressionKind::Unit, scrutinee.monotype);
                    (std::mem::replace(scrutinee, unit), placements)
                } else {
                    let exposed = self
                        .constructions_exposed(scrutinee)
                        .or_else(|| self.foreign_choices_exposed(scrutinee))?;
                    let placements = plan(&exposed, alternatives, self.monotypes)?;
                    (exposed, placements)
                }
            }
            _ => return None,
        };
        if let Some(bound) = self.bind_only_field(&scrutinee, alternatives, &placements) {
            return Some(bound);
        }
        let (joins, alternatives) = self.join_points(alternatives, &placements, monotype);
        let distributed = self.map_choices(scrutinee, monotype, &mut |simplifier, chosen| {
            let case = ExpressionKind::Case {
                scrutinees: vec![chosen],
                alternatives: alternatives.to_vec(),
            };
            let mut case = Expression::new(case, monotype);
            simplifier.rename(&mut case, &mut FxHashMap::default());
            simplifier.expression(case)
        });
        Some(self.let_bindings(joins, distributed))
    }

    /// The choice with each constructor its lets bind written where the local is used, its fields
    /// bound to locals instead, `let problem = Left (f n) in if c then problem else Right n` as
    /// `let field = f n in if c then Left field else Right n`: the constructors are then what the
    /// choice chooses between. `None` when the choice binds no constructor.
    fn constructions_exposed(&mut self, choice: &Expression) -> Option<Expression> {
        let ExpressionKind::Let { bindings, body } = &choice.kind else { return None };
        if bindings.iter().any(|binding| mentions_any(&binding.value, bindings)) {
            return None;
        }
        let mut kept = vec![];
        let mut constructions: Vec<(LocalId, Expression)> = vec![];
        for binding in bindings {
            let mut value = binding.value.clone();
            for (local, construction) in &constructions {
                value = substitute(value, *local, construction, self.monotypes);
            }
            let ExpressionKind::Construct { data, constructor, arguments } = value.kind else {
                kept.push(Binding { local: binding.local.clone(), value });
                continue;
            };
            let mut fields = Vec::with_capacity(arguments.len());
            for argument in arguments {
                if is_trivial(&argument) {
                    fields.push(argument);
                    continue;
                }
                let template =
                    Local { id: LocalId(0), name: "field".into(), monotype: argument.monotype };
                let field = self.fresh(&template);
                fields.push(field.expression());
                kept.push(Binding { local: field, value: argument });
            }
            let kind = ExpressionKind::Construct { data, constructor, arguments: fields };
            constructions.push((binding.local.id, Expression::new(kind, value.monotype)));
        }
        if constructions.is_empty() {
            return None;
        }
        let mut body = (**body).clone();
        for (local, construction) in &constructions {
            body = substitute(body, *local, construction, self.monotypes);
        }
        let kind = ExpressionKind::Let { bindings: kept, body: Box::new(body) };
        Some(Expression::new(kind, choice.monotype))
    }

    fn foreign_choices_exposed(&mut self, choice: &Expression) -> Option<Expression> {
        let mut exposed = false;
        let choice = self.map_choices(choice.clone(), choice.monotype, &mut |simplifier, chosen| {
            let foreign_choice = match &chosen.kind {
                ExpressionKind::Foreign { foreign: Foreign::MaybeIndex, arguments } => {
                    simplifier.index_choice(arguments.clone(), chosen.monotype)
                }
                ExpressionKind::Foreign { foreign: Foreign::UpdateAt, arguments } => {
                    simplifier.update_choice(arguments.clone(), chosen.monotype)
                }
                _ => None,
            };
            match foreign_choice {
                Some(foreign_choice) => {
                    exposed = true;
                    foreign_choice
                }
                None => chosen,
            }
        });
        exposed.then_some(choice)
    }

    fn bind_only_field(
        &mut self,
        choice: &Expression,
        alternatives: &[Alternative],
        placements: &[Placement],
    ) -> Option<Expression> {
        let ([alternative], [Placement::Joined]) = (alternatives, placements) else { return None };
        let ([pattern], Guarded::Unconditional(body)) =
            (&alternative.patterns[..], &alternative.body)
        else {
            return None;
        };
        let PatternKind::Constructor { arguments, .. } = &pattern.kind else { return None };
        let [Pattern { kind: PatternKind::Variable(field), .. }] = &arguments[..] else {
            return None;
        };
        let only_constructions =
            self.map_choices(choice.clone(), field.monotype, &mut |_, chosen| match chosen.kind {
                ExpressionKind::Construct { mut arguments, .. } if arguments.len() == 1 => {
                    arguments.remove(0)
                }
                _ => Expression::new(
                    ExpressionKind::Fail("not a construction".into()),
                    field.monotype,
                ),
            });
        let mut all_constructions = true;
        visit(&only_constructions, &mut |node| {
            if matches!(node.kind, ExpressionKind::Fail(_)) {
                all_constructions = false;
            }
        });
        if !all_constructions {
            return None;
        }
        let binding = Binding { local: field.clone(), value: only_constructions };
        Some(self.let_bindings(vec![binding], body.clone()))
    }

    /// Each joined alternative's body as a local function of the alternative's
    /// variables, which the alternative calls instead: once lifted, a join
    /// point that several chosen values reach is one Go function.
    fn join_points(
        &mut self,
        alternatives: &[Alternative],
        placements: &[Placement],
        monotype: MonotypeId,
    ) -> (Vec<Binding>, Vec<Alternative>) {
        let mut joins = vec![];
        let mut joined = Vec::with_capacity(alternatives.len());
        for (alternative, placement) in alternatives.iter().zip(placements) {
            let (Placement::Joined, Guarded::Unconditional(body)) = (placement, &alternative.body)
            else {
                joined.push(alternative.clone());
                continue;
            };
            let parameters = binders(&alternative.patterns);
            let mut function = monotype;
            for parameter in parameters.iter().rev() {
                function = self.monotypes.function(parameter.monotype, function);
            }
            let template = Local { id: LocalId(0), name: "join".into(), monotype: function };
            let join = self.fresh(&template);
            let lambda = ExpressionKind::Lambda {
                parameters: parameters.clone(),
                body: Box::new(body.clone()),
            };
            let mut lambda = Expression::new(lambda, function);
            self.rename(&mut lambda, &mut FxHashMap::default());
            let call = ExpressionKind::Apply {
                function: Box::new(join.expression()),
                arguments: parameters.iter().map(Local::expression).collect(),
            };
            let body = Guarded::Unconditional(Expression::new(call, monotype));
            let patterns = alternative.patterns.clone();
            joined.push(Alternative { patterns, body, position: alternative.position });
            joins.push(Binding { local: join, value: lambda });
        }
        (joins, joined)
    }

    /// `index xs i` as the choice the foreign makes: `Just xs[i]` when `i` is
    /// within the array and `Nothing` otherwise. The `Just` and `Nothing` the
    /// caller passed tell which constructors those are; like the foreign, the
    /// choice builds them at its own result type.
    fn index_choice(
        &mut self,
        arguments: Vec<Expression>,
        monotype: MonotypeId,
    ) -> Option<Expression> {
        let [just, nothing, elements, index]: [Expression; 4] =
            arguments.try_into().expect("invariant violated: index has four arguments");
        let Monotype::Data(data) = self.monotypes.get(monotype).clone() else { return None };
        let Monotype::Array(element) = *self.monotypes.get(elements.monotype) else {
            unreachable!("invariant violated: index takes an array")
        };
        // Applied to a placeholder, `just` shows the constructor it builds.
        let placeholder = Expression::new(ExpressionKind::Unit, element);
        let just = constructor(&self.apply(just, vec![placeholder], monotype))?;
        let nothing = constructor(&nothing)?;
        let maybe = MaybeChoice { data, just, nothing, monotype };
        Some(self.bounds_choice(maybe, elements, index, |elements, index| {
            operation(Operator::ArrayIndex, vec![elements, index], element)
        }))
    }

    /// `updateAt i x xs` as the choice the foreign makes: `Just` a copy of
    /// `xs` with `x` at `i` when `i` is within the array, and `Nothing`
    /// otherwise.
    fn update_choice(
        &mut self,
        arguments: Vec<Expression>,
        monotype: MonotypeId,
    ) -> Option<Expression> {
        let [just, nothing, index, value, elements]: [Expression; 5] =
            arguments.try_into().expect("invariant violated: updateAt has five arguments");
        let Monotype::Data(data) = self.monotypes.get(monotype).clone() else { return None };
        let placeholder = Expression::new(ExpressionKind::Unit, elements.monotype);
        let just = constructor(&self.apply(just, vec![placeholder], monotype))?;
        let nothing = constructor(&nothing)?;
        let maybe = MaybeChoice { data, just, nothing, monotype };
        let mut bindings = vec![];
        let value = self.shared_operand(value, "value", &mut bindings);
        let array = elements.monotype;
        let choice = self.bounds_choice(maybe, elements, index, |elements, index| {
            let kind = ExpressionKind::Foreign {
                foreign: &Foreign::ArrayUpdated,
                arguments: vec![index, value, elements],
            };
            Expression::new(kind, array)
        });
        if bindings.is_empty() {
            return Some(choice);
        }
        Some(Expression::new(ExpressionKind::Let { bindings, body: Box::new(choice) }, monotype))
    }

    /// `Just (found elements index)` when `index` is within `elements`, and
    /// `Nothing` otherwise.
    fn bounds_choice(
        &mut self,
        maybe: MaybeChoice,
        elements: Expression,
        index: Expression,
        found: impl FnOnce(Expression, Expression) -> Expression,
    ) -> Expression {
        let MaybeChoice { data, just, nothing, monotype } = maybe;
        let mut bindings = vec![];
        let elements = self.shared_operand(elements, "elements", &mut bindings);
        let index = self.shared_operand(index, "index", &mut bindings);
        let boolean = self.monotypes.intern(Monotype::Boolean);
        let int = self.monotypes.intern(Monotype::Int);
        let zero = Expression::new(ExpressionKind::Literal(Literal::Int(0)), int);
        let length = operation(Operator::ArrayLength, vec![elements.clone()], int);
        let non_negative = self.operator(
            &Foreign::Operator(Operator::Compare(Comparison::GreaterThanOrEqual)),
            vec![index.clone(), zero],
            boolean,
        );
        let below_length = self.operator(
            &Foreign::Operator(Operator::Compare(Comparison::LessThan)),
            vec![index.clone(), length],
            boolean,
        );
        let within = self.operator(
            &Foreign::Operator(Operator::BooleanAnd),
            vec![non_negative, below_length],
            boolean,
        );
        let found = found(elements, index);
        let construct = |constructor, arguments| {
            let kind = ExpressionKind::Construct { data: data.clone(), constructor, arguments };
            Expression::new(kind, monotype)
        };
        let kind = ExpressionKind::If {
            condition: Box::new(within),
            then: Box::new(construct(just, vec![found])),
            otherwise: Box::new(construct(nothing, vec![])),
        };
        let choice = Expression::new(kind, monotype);
        if bindings.is_empty() {
            return choice;
        }
        Expression::new(ExpressionKind::Let { bindings, body: Box::new(choice) }, monotype)
    }
}

/// The Maybe a bounds test chooses between.
struct MaybeChoice {
    data: DataType,
    just: usize,
    nothing: usize,
    monotype: MonotypeId,
}

impl Simplifier<'_> {
    /// `peek i array` whose `Maybe` is matched at once, purely (`map
    /// (fromMaybe 0) (peek i array)`) or by the actions that follow (`modify`),
    /// as the bounds test the foreign makes: the alternatives for `Just
    /// array[i]` when `i` is within the array, those for `Nothing` otherwise.
    /// The `Maybe` is then never built nor tested, and what the `Just`
    /// alternative does to `array[i]` sits inside the test that guards it.
    pub(super) fn peek_choice(
        &mut self,
        action: &Expression,
        local: &Local,
        body: &Expression,
        monotype: MonotypeId,
    ) -> Option<Expression> {
        let ExpressionKind::Foreign { foreign, arguments } = &action.kind else { return None };
        if !is_mutable_peek(foreign) {
            return None;
        }
        let (matched, pure) = match &body.kind {
            ExpressionKind::EffectPure(matched) => (matched.as_ref(), true),
            _ => (body, false),
        };
        let ExpressionKind::Case { scrutinees, alternatives } = &matched.kind else { return None };
        let [scrutinee] = scrutinees.as_slice() else { return None };
        let scrutinised = matches!(scrutinee.kind, ExpressionKind::Local(id) if id == local.id);
        if !scrutinised
            || crate::purity::occurrences(matched, local.id).total != 1
            || alternatives_size(alternatives) > DUPLICATION
        {
            return None;
        }
        let [just, nothing, index, array] = arguments.as_slice() else {
            unreachable!("invariant violated: peek has four arguments")
        };
        let Monotype::MutableArray(element) = *self.monotypes.get(array.monotype) else {
            unreachable!("invariant violated: peek reads a mutable array")
        };
        let template = Local { id: LocalId(0), name: "element".into(), monotype: element };
        let peeked = self.fresh(&template);
        let found = self.apply(just.clone(), vec![peeked.expression()], local.monotype);
        constructor(&found)?;
        constructor(nothing)?;
        let result = matched.monotype;
        let chosen = |simplifier: &mut Self, value: Expression| {
            let resolved = simplifier.resolve(value, alternatives, result);
            if !pure {
                return resolved;
            }
            Expression::new(ExpressionKind::EffectPure(Box::new(resolved)), monotype)
        };
        // Go rejects a constant negative index even in a branch that cannot run.
        if let ExpressionKind::Literal(Literal::Int(constant)) = index.kind
            && constant < 0
        {
            return Some(chosen(self, nothing.clone()));
        }
        let missing = chosen(self, nothing.clone());
        let found = chosen(self, found);
        let mut bindings = vec![];
        let array = self.shared_operand(array.clone(), "array", &mut bindings);
        let index = self.shared_operand(index.clone(), "index", &mut bindings);
        let boolean = self.monotypes.intern(Monotype::Boolean);
        let template = Local { id: LocalId(0), name: "within".into(), monotype: boolean };
        let within = self.fresh(&template);
        let read = Expression::new(
            ExpressionKind::Foreign {
                foreign: &MUTABLE_PEEK_UNSAFE,
                arguments: vec![index.clone(), array.clone()],
            },
            self.monotypes.intern(Monotype::Effect(element)),
        );
        let read = ExpressionKind::EffectBind {
            action: Box::new(read),
            local: peeked,
            body: Box::new(found),
        };
        let choice = ExpressionKind::If {
            condition: Box::new(within.expression()),
            then: Box::new(Expression::new(read, monotype)),
            otherwise: Box::new(missing),
        };
        let test = Expression::new(
            ExpressionKind::Foreign { foreign: &MUTABLE_WITHIN, arguments: vec![index, array] },
            self.monotypes.intern(Monotype::Effect(boolean)),
        );
        let tested = ExpressionKind::EffectBind {
            action: Box::new(test),
            local: within,
            body: Box::new(Expression::new(choice, monotype)),
        };
        Some(self.let_bindings(bindings, Expression::new(tested, monotype)))
    }

    /// The alternatives matched against one chosen value, resolved.
    fn resolve(
        &mut self,
        chosen: Expression,
        alternatives: &[Alternative],
        monotype: MonotypeId,
    ) -> Expression {
        let case =
            ExpressionKind::Case { scrutinees: vec![chosen], alternatives: alternatives.to_vec() };
        let mut case = Expression::new(case, monotype);
        self.rename(&mut case, &mut FxHashMap::default());
        self.expression(case)
    }
}

/// The bounds test of a peek whose index turned out to be a constant below
/// zero once its binding was substituted: false, so that the read it guards,
/// whose constant negative index Go rejects even where it cannot run, goes.
pub(super) fn negative_within(
    foreign: &Foreign,
    arguments: &[Expression],
    monotype: MonotypeId,
    monotypes: &mut Monotypes,
) -> Option<Expression> {
    let Foreign::Perform { function: GoFunction { package: GoPackage::Array, name }, .. } = foreign
    else {
        return None;
    };
    let ExpressionKind::Literal(Literal::Int(index)) = arguments.first()?.kind else {
        return None;
    };
    if *name != "Within" || index >= 0 {
        return None;
    }
    let outside = Expression::new(
        ExpressionKind::Literal(Literal::Boolean(false)),
        monotypes.intern(Monotype::Boolean),
    );
    Some(Expression::new(ExpressionKind::EffectPure(Box::new(outside)), monotype))
}

/// The copy that an `updateAt` whose index turned out to be a constant below zero
/// makes where its bounds test passes, which it never does: the array itself, as
/// Go rejects the constant negative index even where it cannot run.
pub(super) fn negative_update(foreign: &Foreign, arguments: &[Expression]) -> Option<Expression> {
    let (Foreign::ArrayUpdated, [index, _, elements]) = (foreign, arguments) else { return None };
    let ExpressionKind::Literal(Literal::Int(index)) = index.kind else { return None };
    (index < 0).then(|| elements.clone())
}

/// Data.Array.ST's peek.
fn is_mutable_peek(foreign: &Foreign) -> bool {
    matches!(
        foreign,
        Foreign::Perform { function: GoFunction { package: GoPackage::Array, name: "Peek" }, .. }
    )
}

enum Placement {
    /// Copied into every chosen value that reaches it.
    Copied,
    /// A join point that every chosen value reaching it calls.
    Joined,
}

/// Where each alternative goes when the case is distributed into the choice,
/// if every value the choice makes resolves the alternatives and the copies
/// stay within the budget.
fn plan(
    choice: &Expression,
    alternatives: &[Alternative],
    monotypes: &Monotypes,
) -> Option<Vec<Placement>> {
    let mut selections = vec![0usize; alternatives.len()];
    if !select(choice, choice.monotype, alternatives, &mut selections, monotypes) {
        return None;
    }
    let mut copied = 0;
    let mut placements = Vec::with_capacity(alternatives.len());
    for (alternative, &count) in alternatives.iter().zip(&selections) {
        if count <= 1 {
            placements.push(Placement::Copied);
            continue;
        }
        // Each copy of an erased value, and each join point's signature,
        // would repeat its boxing.
        if mentions_erased(alternative, monotypes) {
            return None;
        }
        let size = alternative_size(alternative);
        let joinable = matches!(alternative.body, Guarded::Unconditional(_))
            && !binders(&alternative.patterns).is_empty();
        if joinable && size > JOIN_SIZE {
            placements.push(Placement::Joined);
        } else {
            copied += (count - 1) * size;
            placements.push(Placement::Copied);
        }
    }
    (copied <= DUPLICATION).then_some(placements)
}

/// Counts, for each alternative, the chosen values that may reach it. A value
/// of another representation than the scrutinee's, such as a constructor whose
/// type arguments were erased, would carry it into the alternatives.
fn select(
    choice: &Expression,
    monotype: MonotypeId,
    alternatives: &[Alternative],
    selections: &mut [usize],
    monotypes: &Monotypes,
) -> bool {
    match &choice.kind {
        ExpressionKind::If { then, otherwise, .. } => {
            select(then, monotype, alternatives, selections, monotypes)
                && select(otherwise, monotype, alternatives, selections, monotypes)
        }
        ExpressionKind::Let { body, .. } => {
            select(body, monotype, alternatives, selections, monotypes)
        }
        ExpressionKind::Case { alternatives: inner, .. } => {
            inner.iter().all(|alternative| match &alternative.body {
                Guarded::Unconditional(body) => {
                    select(body, monotype, alternatives, selections, monotypes)
                }
                Guarded::Guards(branches) => branches.iter().all(|branch| {
                    select(&branch.body, monotype, alternatives, selections, monotypes)
                }),
            })
        }
        ExpressionKind::Fail(_) => true,
        ExpressionKind::Construct { .. } | ExpressionKind::Literal(_)
            if monotypes.same_without_causes(choice.monotype, monotype) =>
        {
            let Some(outcomes) = column_outcomes(choice, alternatives, 0) else { return false };
            // A guarded alternative may fall through to the ones after it.
            for (position, outcome) in outcomes.iter().enumerate() {
                if let super::coverage::ColumnOutcome::Matches = outcome {
                    selections[position] += 1;
                    if let Guarded::Unconditional(_) = alternatives[position].body {
                        break;
                    }
                }
            }
            true
        }
        _ => false,
    }
}

fn alternative_size(alternative: &Alternative) -> usize {
    alternatives_size(std::slice::from_ref(alternative)) + 1
}

fn mentions_erased(alternative: &Alternative, monotypes: &Monotypes) -> bool {
    let mut erased = false;
    crate::monomorphic::traversal::for_each_alternative_child(
        std::slice::from_ref(alternative),
        &mut |child| {
            crate::monomorphic::traversal::visit(child, &mut |node| {
                erased = erased || crate::lift::erases(monotypes, node.monotype)
            })
        },
    );
    erased
}

pub(super) fn operation(
    operator: Operator,
    arguments: Vec<Expression>,
    monotype: MonotypeId,
) -> Expression {
    let foreign = Foreign::Operator(operator).interned();
    Expression::new(ExpressionKind::Foreign { foreign, arguments }, monotype)
}

fn constructor(expression: &Expression) -> Option<usize> {
    match expression.kind {
        ExpressionKind::Construct { constructor, .. } => Some(constructor),
        _ => None,
    }
}

/// The variables that patterns bind, in order.
fn binders(patterns: &[Pattern]) -> Vec<Local> {
    let mut collected = vec![];
    for pattern in patterns {
        pattern.for_each_local(&mut |local| collected.push(local.clone()));
    }
    collected
}
