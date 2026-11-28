//! Tests whose outcome the code before them already settled.
//!
//! An alternative is tested in full even when an earlier one has ruled part of it out, so
//! `if value == leaf { return … }` is followed by `if value != leaf && value.Node0 == ColorRed`.
//! A test is known inside the branch it guards and, when the other branch leaves the block, after
//! the `if`; a known conjunct is dropped, and a conjunct known to fail decides the whole test.

use rustc_hash::FxHashSet;

use super::conditions::{is_pure, negated};
use crate::go_traversal::{self, Walk};
use crate::syntax::{
    GoBinaryOperator, GoDeclaration, GoExpression, GoStatement, GoUnaryOperator, Name,
    statements_names,
};

pub(super) fn drop_known_tests(declarations: &mut [GoDeclaration]) {
    for declaration in declarations {
        go_traversal::declaration(&mut Literals, declaration);
    }
}

/// Starts afresh in each function body, which runs when it is called rather than where it is.
struct Literals;

impl Walk for Literals {
    fn block(&mut self, body: &mut Vec<GoStatement>) {
        settle(body, vec![]);
    }
}

/// Settles the block's tests, knowing the facts on entry.
fn settle(block: &mut Vec<GoStatement>, mut facts: Vec<GoExpression>) {
    let mut position = 0;
    while position < block.len() {
        if let GoStatement::If { condition, then, otherwise } = &mut block[position] {
            match decided(condition, &facts) {
                Decision::Open => {}
                Decision::Always if !defines_names(then) => {
                    let then = std::mem::take(then);
                    block.splice(position..=position, then);
                    continue;
                }
                Decision::Never if !defines_names(otherwise) => {
                    let otherwise = std::mem::take(otherwise);
                    block.splice(position..=position, otherwise);
                    continue;
                }
                Decision::Always | Decision::Never => {}
            }
        }
        let statement = &mut block[position];
        nested(statement, &facts);
        forget_changed(statement, &mut facts);
        facts.extend(after(statement));
        position += 1;
    }
}

enum Decision {
    Open,
    Always,
    Never,
}

/// Drops the condition's known conjuncts, and says whether that settles it.
fn decided(condition: &mut GoExpression, facts: &[GoExpression]) -> Decision {
    let conjuncts = conjuncts(condition);
    if conjuncts.iter().any(|conjunct| facts.contains(&negated(conjunct))) {
        return Decision::Never;
    }
    let open: Vec<GoExpression> =
        conjuncts.iter().filter(|conjunct| !facts.contains(conjunct)).cloned().collect();
    if open.is_empty() {
        return Decision::Always;
    }
    if open.len() < conjuncts.len() {
        *condition = open
            .into_iter()
            .reduce(|left, right| GoExpression::Binary {
                operator: GoBinaryOperator::LogicalAnd,
                left: Box::new(left),
                right: Box::new(right),
            })
            .expect("an open condition has a conjunct");
    }
    Decision::Open
}

/// Settles the blocks nested in the statement, with what is known in each.
fn nested(statement: &mut GoStatement, facts: &[GoExpression]) {
    match statement {
        GoStatement::If { condition, then, otherwise } => {
            go_traversal::expression(&mut Literals, condition);
            let pure = |conjunct: &GoExpression| is_pure(conjunct);
            let mut inside = facts.to_vec();
            inside.extend(conjuncts(condition).into_iter().filter(pure));
            settle(then, inside);
            let mut outside = facts.to_vec();
            if let [single] = conjuncts(condition).as_slice()
                && is_pure(single)
            {
                outside.push(negated(single));
            }
            settle(otherwise, outside);
        }
        GoStatement::Switch { value, cases, default } => {
            if let Some(value) = value {
                go_traversal::expression(&mut Literals, value);
            }
            for case in cases {
                settle(&mut case.body, facts.to_vec());
            }
            if let Some(default) = default {
                settle(&mut default.body, facts.to_vec());
            }
        }
        GoStatement::IfAssert { value, then, .. } => {
            go_traversal::expression(&mut Literals, value);
            settle(then, facts.to_vec());
        }
        // A loop's body runs again after it has changed what it tests.
        statement => go_traversal::statement(&mut Literals, statement),
    }
}

/// Forgets the facts the statement may make false: those naming a variable it assigns or
/// defines, and, when it calls a function or writes through a pointer, those reading memory.
fn forget_changed(statement: &mut GoStatement, facts: &mut Vec<GoExpression>) {
    if facts.is_empty() {
        return;
    }
    let mut written = FxHashSet::default();
    statements_names(std::slice::from_mut(statement), &mut |name| {
        if let Name::Written(name) | Name::Binder(name) = name {
            written.insert(name.clone());
        }
    });
    let touches_memory = writes_memory(statement);
    let changed = |fact: &GoExpression| {
        mentions_any(fact, &written) || (touches_memory && reads_memory(fact))
    };
    facts.retain(|fact| !changed(fact));
}

/// What holds after the statement: the opposite of a test whose branch always leaves the block.
fn after(statement: &GoStatement) -> Vec<GoExpression> {
    let GoStatement::If { condition, then, otherwise } = statement else { return vec![] };
    if !otherwise.is_empty() || !leaves(then) || !is_pure(condition) {
        return vec![];
    }
    match conjuncts(condition).as_slice() {
        [single] => disjuncts(single).iter().map(negated).collect(),
        _ => vec![],
    }
}

fn leaves(block: &[GoStatement]) -> bool {
    block.last().is_some_and(|last| {
        last.is_panic()
            || matches!(
                last,
                GoStatement::Return(_)
                    | GoStatement::Continue
                    | GoStatement::Break
                    | GoStatement::BreakTo(_)
            )
    })
}

fn conjuncts(condition: &GoExpression) -> Vec<GoExpression> {
    split(condition, GoBinaryOperator::LogicalAnd)
}

fn disjuncts(condition: &GoExpression) -> Vec<GoExpression> {
    split(condition, GoBinaryOperator::LogicalOr)
}

fn split(condition: &GoExpression, operator: GoBinaryOperator) -> Vec<GoExpression> {
    match condition {
        GoExpression::Binary { operator: found, left, right } if *found == operator => {
            let mut parts = split(left, operator);
            parts.extend(split(right, operator));
            parts
        }
        condition => vec![condition.clone()],
    }
}

fn defines_names(block: &[GoStatement]) -> bool {
    block.iter().any(|statement| {
        matches!(statement, GoStatement::Define { .. } | GoStatement::Variable { .. })
    })
}

fn mentions_any(fact: &GoExpression, names: &FxHashSet<String>) -> bool {
    match fact {
        GoExpression::Identifier(name) => names.contains(name),
        GoExpression::Binary { left, right, .. } => {
            mentions_any(left, names) || mentions_any(right, names)
        }
        GoExpression::Unary { operand: value, .. }
        | GoExpression::Field { value, .. }
        | GoExpression::Conversion { value, .. }
        | GoExpression::Attributed { value, .. } => mentions_any(value, names),
        _ => false,
    }
}

fn reads_memory(fact: &GoExpression) -> bool {
    match fact {
        GoExpression::Field { .. } | GoExpression::Index { .. } => true,
        GoExpression::Unary { operator: GoUnaryOperator::Dereference, .. } => true,
        GoExpression::Binary { left, right, .. } => reads_memory(left) || reads_memory(right),
        GoExpression::Unary { operand: value, .. }
        | GoExpression::Conversion { value, .. }
        | GoExpression::Attributed { value, .. } => reads_memory(value),
        _ => false,
    }
}

/// Whether running the statement may change memory a fact reads: it calls a function, which may
/// write anything it can reach, or assigns through a field, an element or a pointer.
fn writes_memory(statement: &mut GoStatement) -> bool {
    struct Writes(bool);
    impl Walk for Writes {
        fn statement(&mut self, statement: &mut GoStatement) {
            if let GoStatement::Assign { targets, .. } = statement
                && targets.iter().any(|target| !matches!(target, GoExpression::Identifier(_)))
            {
                self.0 = true;
            }
            go_traversal::statement(self, statement);
        }

        fn expression(&mut self, value: &mut GoExpression) {
            match value {
                GoExpression::Call { .. } => self.0 = true,
                // A function literal runs where it is called, which is a call.
                GoExpression::Function { .. } => {}
                value => go_traversal::expression(self, value),
            }
        }
    }
    let mut writes = Writes(false);
    writes.statement(statement);
    writes.0
}
