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
    GoBinaryOperator, GoBuiltin, GoDeclaration, GoExpression, GoStatement, GoType, GoUnaryOperator,
    Name, statements_names,
};

pub(super) fn drop_known_tests(declarations: &mut [GoDeclaration]) {
    for declaration in declarations {
        let strings = unchanging_strings(declaration);
        go_traversal::declaration(&mut Literals(&strings), declaration);
    }
}

pub(super) fn unchanging_strings(declaration: &mut GoDeclaration) -> FxHashSet<String> {
    let GoDeclaration::Function { parameters, body, .. } = declaration else {
        return FxHashSet::default();
    };
    let strings = parameters.iter().filter(|(_, type_)| *type_ == GoType::String);
    let mut strings: FxHashSet<String> = strings.map(|(name, _)| name.clone()).collect();
    statements_names(body, &mut |name| {
        if let Name::Binder(name) = name {
            strings.remove(name.as_str());
        }
    });
    strings
}

/// Starts afresh in each function body, which runs when it is called rather than where it is.
struct Literals<'s>(&'s FxHashSet<String>);

impl Walk for Literals<'_> {
    fn block(&mut self, body: &mut Vec<GoStatement>) {
        settle(body, vec![], self.0);
    }
}

/// Settles the block's tests, knowing the facts on entry.
fn settle(block: &mut Vec<GoStatement>, mut facts: Vec<GoExpression>, strings: &FxHashSet<String>) {
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
        nested(statement, &facts, strings);
        forget_changed(statement, &mut facts, strings);
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
    let known = |conjunct: &GoExpression| facts.contains(conjunct) || implied(conjunct, facts);
    let open = conjuncts.iter().filter(|conjunct| !known(conjunct)).cloned();
    let open: Vec<GoExpression> = open.collect();
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
fn nested(statement: &mut GoStatement, facts: &[GoExpression], strings: &FxHashSet<String>) {
    match statement {
        GoStatement::If { condition, then, otherwise } => {
            go_traversal::expression(&mut Literals(strings), condition);
            let pure = |conjunct: &GoExpression| is_stable(conjunct);
            let mut inside = facts.to_vec();
            inside.extend(conjuncts(condition).into_iter().filter(pure));
            settle(then, inside, strings);
            let mut outside = facts.to_vec();
            if let [single] = conjuncts(condition).as_slice()
                && is_pure(single)
            {
                outside.push(negated(single));
            }
            settle(otherwise, outside, strings);
        }
        GoStatement::Switch { value, cases, default } => {
            if let Some(value) = value {
                go_traversal::expression(&mut Literals(strings), value);
            }
            for case in cases {
                settle(&mut case.body, facts.to_vec(), strings);
            }
            if let Some(default) = default {
                settle(&mut default.body, facts.to_vec(), strings);
            }
        }
        GoStatement::IfAssert { value, then, .. } => {
            go_traversal::expression(&mut Literals(strings), value);
            settle(then, facts.to_vec(), strings);
        }
        // A loop's body runs again after it has changed what it tests.
        statement => go_traversal::statement(&mut Literals(strings), statement),
    }
}

/// Forgets the facts the statement may make false: those naming a variable it assigns or
/// defines, and, when it calls a function or writes through a pointer, those reading memory.
fn forget_changed(
    statement: &mut GoStatement,
    facts: &mut Vec<GoExpression>,
    strings: &FxHashSet<String>,
) {
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
        mentions_any(fact, &written) || (touches_memory && reads_memory(fact, strings))
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

fn reads_memory(fact: &GoExpression, strings: &FxHashSet<String>) -> bool {
    match fact {
        GoExpression::Index { value, index } if matches!(&**value, GoExpression::Identifier(name) if strings.contains(name)) => {
            reads_memory(index, strings)
        }
        GoExpression::Field { .. }
        | GoExpression::Index { .. }
        | GoExpression::Unary { operator: GoUnaryOperator::Dereference, .. } => true,
        GoExpression::Binary { left, right, .. } => {
            reads_memory(left, strings) || reads_memory(right, strings)
        }
        GoExpression::Unary { operand: value, .. }
        | GoExpression::Conversion { value, .. }
        | GoExpression::Attributed { value, .. } => reads_memory(value, strings),
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

fn implied(conjunct: &GoExpression, facts: &[GoExpression]) -> bool {
    if let Some((text, shortest)) = longer_than(conjunct) {
        return facts
            .iter()
            .filter_map(longer_than)
            .any(|(known, longer)| known == text && longer >= shortest);
    }
    let Some((text, positions)) = ascii_bytes(conjunct) else { return false };
    let known = facts.iter().filter_map(ascii_bytes).filter(|(known, _)| *known == text);
    let known: Vec<i64> = known.flat_map(|(_, positions)| positions).collect();
    positions.iter().all(|position| known.contains(position))
}

fn longer_than(condition: &GoExpression) -> Option<(&GoExpression, i64)> {
    let GoExpression::Binary { operator: GoBinaryOperator::GreaterThan, left, right } = condition
    else {
        return None;
    };
    let GoExpression::Integer(shortest) = **right else { return None };
    let GoExpression::Call { function, arguments } = &**left else { return None };
    let [text] = arguments.as_slice() else { return None };
    function.is_builtin(GoBuiltin::Len).then_some((text, shortest))
}

fn ascii_bytes(condition: &GoExpression) -> Option<(&GoExpression, Vec<i64>)> {
    let GoExpression::Binary { operator: GoBinaryOperator::LessThan, left, right } = condition
    else {
        return None;
    };
    if **right != GoExpression::Integer(128) {
        return None;
    }
    let mut text = None;
    let mut positions = vec![];
    bytes_of(left, &mut text, &mut positions).then_some(())?;
    Some((text?, positions))
}

fn bytes_of<'e>(
    value: &'e GoExpression,
    text: &mut Option<&'e GoExpression>,
    positions: &mut Vec<i64>,
) -> bool {
    match value {
        GoExpression::Binary { operator: GoBinaryOperator::BitwiseOr, left, right } => {
            bytes_of(left, text, positions) && bytes_of(right, text, positions)
        }
        GoExpression::Index { value, index } => {
            let GoExpression::Integer(position) = **index else { return false };
            if text.is_some_and(|text| text != &**value) {
                return false;
            }
            *text = Some(value);
            positions.push(position);
            true
        }
        _ => false,
    }
}

fn is_stable(condition: &GoExpression) -> bool {
    match condition {
        GoExpression::Index { value, index } => is_stable(value) && is_stable(index),
        GoExpression::Call { function, arguments } if function.is_builtin(GoBuiltin::Len) => {
            arguments.iter().all(is_stable)
        }
        GoExpression::Binary { left, right, .. } => is_stable(left) && is_stable(right),
        GoExpression::Unary { operand: value, .. }
        | GoExpression::Field { value, .. }
        | GoExpression::Conversion { value, .. } => is_stable(value),
        condition => is_pure(condition),
    }
}

pub(super) fn reads_only(condition: &GoExpression, strings: &FxHashSet<String>) -> bool {
    match condition {
        GoExpression::Index { value, index } => {
            matches!(&**value, GoExpression::Identifier(name) if strings.contains(name))
                && reads_only(index, strings)
        }
        GoExpression::Call { function, arguments } if function.is_builtin(GoBuiltin::Len) => {
            arguments.iter().all(|argument| reads_only(argument, strings))
        }
        GoExpression::Binary { left, right, .. } => {
            reads_only(left, strings) && reads_only(right, strings)
        }
        GoExpression::Unary { operand: value, .. }
        | GoExpression::Field { value, .. }
        | GoExpression::Conversion { value, .. } => reads_only(value, strings),
        condition => is_pure(condition),
    }
}
