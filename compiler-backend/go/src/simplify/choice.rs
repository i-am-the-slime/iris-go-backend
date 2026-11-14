//! Case of case. A case whose scrutinee chooses between constructors or
//! literals, through ifs, lets and other cases, is distributed into the
//! choice: each chosen value meets its own copy of the case, which it
//! resolves. The value is then never built, and its tag never tested.

use rustc_hash::FxHashMap;

use super::{INLINE_SIZE, Simplifier, alternatives_size, column_outcomes, local_expression};
use crate::foreign::{Comparison, Foreign, Operator};
use crate::mono::{
    Alternative, Binding, Expression, ExpressionKind, Guarded, Literal, Local, LocalId, Pattern,
    PatternKind,
};
use crate::monotype::{Monotype, MonotypeId, Monotypes};

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
            ExpressionKind::If { .. }
            | ExpressionKind::Let { .. }
            | ExpressionKind::Case { .. } => {
                let placements = plan(scrutinee, alternatives, self.monotypes)?;
                let unit = Expression::new(ExpressionKind::Unit, scrutinee.monotype);
                (std::mem::replace(scrutinee, unit), placements)
            }
            _ => return None,
        };
        let (joins, alternatives) = self.join_points(alternatives, &placements, monotype);
        let distributed = self.map_choices(scrutinee, monotype, &mut |simplifier, chosen| {
            let case = ExpressionKind::Case {
                scrutinees: vec![chosen],
                alternatives: alternatives.to_vec(),
            };
            let case = Expression::new(case, monotype);
            let case = simplifier.rename(case, &mut FxHashMap::default());
            simplifier.expression(case)
        });
        Some(self.let_bindings(joins, distributed))
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
            let lambda = Expression::new(lambda, function);
            let lambda = self.rename(lambda, &mut FxHashMap::default());
            let call = ExpressionKind::Apply {
                function: Box::new(local_expression(&join)),
                arguments: parameters.iter().map(local_expression).collect(),
            };
            let body = Guarded::Unconditional(Expression::new(call, monotype));
            joined.push(Alternative { patterns: alternative.patterns.clone(), body });
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

        let mut bindings = vec![];
        let elements = self.shared_operand(elements, "elements", &mut bindings);
        let index = self.shared_operand(index, "index", &mut bindings);
        let boolean = self.monotypes.intern(Monotype::Boolean);
        let int = self.monotypes.intern(Monotype::Int);
        let zero = Expression::new(ExpressionKind::Literal(Literal::Int(0)), int);
        let length = operation(Operator::ArrayLength, vec![elements.clone()], int);
        let non_negative = self.operator(
            Foreign::Operator(Operator::Compare(Comparison::GreaterThanOrEqual)),
            vec![index.clone(), zero],
            boolean,
        );
        let below_length = self.operator(
            Foreign::Operator(Operator::Compare(Comparison::LessThan)),
            vec![index.clone(), length],
            boolean,
        );
        let within = self.operator(
            Foreign::Operator(Operator::BooleanAnd),
            vec![non_negative, below_length],
            boolean,
        );
        let found = operation(Operator::ArrayIndex, vec![elements, index], element);
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
            return Some(choice);
        }
        Some(Expression::new(ExpressionKind::Let { bindings, body: Box::new(choice) }, monotype))
    }
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
    if !select(choice, choice.monotype, alternatives, &mut selections) {
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
) -> bool {
    match &choice.kind {
        ExpressionKind::If { then, otherwise, .. } => {
            select(then, monotype, alternatives, selections)
                && select(otherwise, monotype, alternatives, selections)
        }
        ExpressionKind::Let { body, .. } => select(body, monotype, alternatives, selections),
        ExpressionKind::Case { alternatives: inner, .. } => {
            inner.iter().all(|alternative| match &alternative.body {
                Guarded::Unconditional(body) => select(body, monotype, alternatives, selections),
                Guarded::Guards(branches) => branches
                    .iter()
                    .all(|branch| select(&branch.body, monotype, alternatives, selections)),
            })
        }
        ExpressionKind::Fail(_) => true,
        ExpressionKind::Construct { .. } | ExpressionKind::Literal(_)
            if choice.monotype == monotype =>
        {
            let Some(outcomes) = column_outcomes(choice, alternatives, 0) else { return false };
            // A guarded alternative may fall through to the ones after it.
            for (position, outcome) in outcomes.iter().enumerate() {
                if let super::ColumnOutcome::Matches = outcome {
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
    super::for_each_alternative_child(std::slice::from_ref(alternative), &mut |child| {
        super::visit(child, &mut |node| {
            erased = erased || crate::lift::erases(monotypes, node.monotype)
        })
    });
    erased
}

fn operation(operator: Operator, arguments: Vec<Expression>, monotype: MonotypeId) -> Expression {
    let foreign = Foreign::Operator(operator);
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
    fn collect(pattern: &Pattern, binders: &mut Vec<Local>) {
        match &pattern.kind {
            PatternKind::Variable(local) => binders.push(local.clone()),
            PatternKind::Named { local, pattern } => {
                binders.push(local.clone());
                collect(pattern, binders);
            }
            PatternKind::Array(elements) => {
                elements.iter().for_each(|element| collect(element, binders))
            }
            PatternKind::Record(fields) => {
                fields.iter().for_each(|(_, field)| collect(field, binders))
            }
            PatternKind::Constructor { arguments, .. } => {
                arguments.iter().for_each(|argument| collect(argument, binders))
            }
            PatternKind::Closure { captures, .. } => {
                captures.iter().for_each(|capture| collect(capture, binders))
            }
            PatternKind::Wildcard | PatternKind::Literal(_) => {}
        }
    }
    let mut collected = vec![];
    patterns.iter().for_each(|pattern| collect(pattern, &mut collected));
    collected
}
