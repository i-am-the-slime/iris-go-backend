use rustc_hash::FxHashSet;

use super::Analysis;
use crate::emit::intervals::constraints::{State, kind_of_type};
use crate::emit::intervals::syntax::is_bounds_test;
use crate::go_traversal::{self, Walk};
use crate::syntax::{GoBinaryOperator, GoBuiltin, GoExpression, GoStatement, GoUnaryOperator};

impl Analysis<'_, '_, '_> {
    /// Rewrites the statement at `position` by what the state proves. True when the block
    /// changed there and the statement at `position` is to be looked at again.
    pub(super) fn rewrite_statement(
        &mut self,
        body: &mut Vec<GoStatement>,
        position: usize,
        state: &State,
    ) -> bool {
        match &mut body[position] {
            GoStatement::If { condition, .. } if !self.is_bounds_test(condition) => false,
            GoStatement::If { condition, then, otherwise } => {
                let decided = if self.is_inert(condition, state) {
                    self.decide(state, condition)
                } else {
                    None
                };
                match decided {
                    Some(true) => {
                        let passed = std::mem::take(then);
                        match splice(body, position, passed) {
                            Ok(()) => true,
                            // Kept as a branch, as its names would clash where it stands.
                            Err(passed) => {
                                if let GoStatement::If { then, otherwise, .. } = &mut body[position]
                                {
                                    *then = passed;
                                    otherwise.clear();
                                }
                                false
                            }
                        }
                    }
                    Some(false) => {
                        let failed = std::mem::take(otherwise);
                        match splice(body, position, failed) {
                            Ok(()) => true,
                            Err(failed) => {
                                if let GoStatement::If { otherwise, .. } = &mut body[position] {
                                    *otherwise = failed;
                                }
                                false
                            }
                        }
                    }
                    None => {
                        self.drop_proven_conjuncts(condition, state);
                        false
                    }
                }
            }
            _ => false,
        }
    }

    /// `true` for a test the state proves, else the test without the conjuncts it proves.
    pub(super) fn simplify_test(&mut self, test: &mut GoExpression, state: &State) {
        if self.is_inert(test, state) && self.decide(state, test) == Some(true) {
            *test = GoExpression::Boolean(true);
        } else {
            self.drop_proven_conjuncts(test, state);
        }
    }

    /// Drops each inert conjunct of `a && b && ...` that the state and the conjuncts before
    /// it prove.
    fn drop_proven_conjuncts(&mut self, condition: &mut GoExpression, state: &State) {
        if !matches!(condition, GoExpression::Binary { operator: GoBinaryOperator::LogicalAnd, .. })
        {
            return;
        }
        let original = condition.clone();
        let mut conjuncts = vec![];
        flatten_conjuncts(
            std::mem::replace(condition, GoExpression::Boolean(true)),
            &mut conjuncts,
        );
        let count = conjuncts.len();
        let mut assumed = state.clone();
        let mut kept: Vec<GoExpression> = vec![];
        for conjunct in conjuncts {
            if self.is_inert(&conjunct, &assumed) && self.decide(&assumed, &conjunct) == Some(true)
            {
                continue;
            }
            assumed = self.assume(&assumed, &conjunct, true);
            kept.push(conjunct);
        }
        if kept.len() == count {
            *condition = original;
            return;
        }
        *condition = kept
            .into_iter()
            .reduce(|left, right| GoExpression::Binary {
                operator: GoBinaryOperator::LogicalAnd,
                left: Box::new(left),
                right: Box::new(right),
            })
            .unwrap_or(GoExpression::Boolean(true));
    }

    /// A bounds test, or a name bound to one.
    fn is_bounds_test(&self, test: &GoExpression) -> bool {
        match test {
            GoExpression::Identifier(name) => self
                .lookup(name)
                .and_then(|symbol| self.conditions.get(&symbol))
                .is_some_and(|condition| is_bounds_test(&condition.test)),
            test => is_bounds_test(test),
        }
    }

    /// Whether dropping the test changes nothing but its answer: it calls nothing but `len`,
    /// cannot panic, and reads through a pointer only one whose length is known.
    fn is_inert(&self, test: &GoExpression, state: &State) -> bool {
        match test {
            GoExpression::Identifier(_) | GoExpression::Integer(_) | GoExpression::Boolean(_) => {
                true
            }
            GoExpression::Unary {
                operator: GoUnaryOperator::Not | GoUnaryOperator::Negate,
                operand,
            } => self.is_inert(operand, state),
            GoExpression::Binary { operator, left, right } => {
                matches!(
                    *operator,
                    GoBinaryOperator::LogicalAnd
                        | GoBinaryOperator::LogicalOr
                        | GoBinaryOperator::LessThan
                        | GoBinaryOperator::LessThanOrEqual
                        | GoBinaryOperator::GreaterThan
                        | GoBinaryOperator::GreaterThanOrEqual
                        | GoBinaryOperator::Equal
                        | GoBinaryOperator::NotEqual
                        | GoBinaryOperator::Add
                        | GoBinaryOperator::Subtract
                        | GoBinaryOperator::Multiply
                        | GoBinaryOperator::BitwiseAnd
                        | GoBinaryOperator::BitwiseOr
                        | GoBinaryOperator::BitwiseXor
                ) && self.is_inert(left, state)
                    && self.is_inert(right, state)
            }
            GoExpression::Conversion { type_, value } => {
                kind_of_type(type_).is_some() && self.is_inert(value, state)
            }
            GoExpression::Call { function, arguments } => {
                function.is_builtin(GoBuiltin::Len)
                    && arguments.len() == 1
                    && match &arguments[0] {
                        GoExpression::Identifier(_) | GoExpression::String(_) => true,
                        GoExpression::Unary { operator: GoUnaryOperator::Dereference, operand } => {
                            match &**operand {
                                GoExpression::Identifier(name) => {
                                    self.lookup(name).is_some_and(|symbol| {
                                        self.bindings[&symbol]
                                            .length
                                            .is_some_and(|length| state.mentions(length))
                                    })
                                }
                                _ => false,
                            }
                        }
                        _ => false,
                    }
            }
            _ => false,
        }
    }
}

fn flatten_conjuncts(condition: GoExpression, into: &mut Vec<GoExpression>) {
    match condition {
        GoExpression::Binary { operator: GoBinaryOperator::LogicalAnd, left, right } => {
            flatten_conjuncts(*left, into);
            flatten_conjuncts(*right, into);
        }
        condition => into.push(condition),
    }
}

/// Replaces the statement at `position` with `statements` when their names cannot clash:
/// no other statement of the block binds a name they bind, and none after them reads one.
fn splice(
    body: &mut Vec<GoStatement>,
    position: usize,
    statements: Vec<GoStatement>,
) -> Result<(), Vec<GoStatement>> {
    let bound: FxHashSet<String> = statements.iter().flat_map(top_level_names).collect();
    let clashes = !bound.is_empty()
        && body.iter().enumerate().any(|(other, statement)| {
            other != position
                && (top_level_names(statement).iter().any(|name| bound.contains(name))
                    || other > position && reads_free(statement, &bound))
        });
    if clashes {
        return Err(statements);
    }
    body.splice(position..=position, statements);
    Ok(())
}

fn top_level_names(statement: &GoStatement) -> Vec<String> {
    match statement {
        GoStatement::Define { names, .. } => {
            names.iter().filter(|name| *name != "_").cloned().collect()
        }
        GoStatement::Variable { name, .. } => vec![name.clone()],
        _ => vec![],
    }
}

/// Whether the statement reads one of `names` from outside itself.
fn reads_free(statement: &GoStatement, names: &FxHashSet<String>) -> bool {
    struct Free<'a> {
        names: &'a FxHashSet<String>,
        shadowed: Vec<FxHashSet<String>>,
        found: bool,
    }
    impl Free<'_> {
        fn visible(&self, name: &str) -> bool {
            self.names.contains(name) && !self.shadowed.iter().any(|scope| scope.contains(name))
        }
        fn shadow(&mut self, name: &str) {
            if let Some(scope) = self.shadowed.last_mut() {
                scope.insert(name.to_string());
            }
        }
    }
    impl Walk for Free<'_> {
        fn block(&mut self, body: &mut Vec<GoStatement>) {
            self.shadowed.push(FxHashSet::default());
            body.iter_mut().for_each(|statement| self.statement(statement));
            self.shadowed.pop();
        }

        fn statement(&mut self, statement: &mut GoStatement) {
            match statement {
                GoStatement::Define { .. } => {
                    go_traversal::statement(self, statement);
                    if let GoStatement::Define { names, .. } = statement {
                        names.clone().iter().for_each(|name| self.shadow(name));
                    }
                }
                GoStatement::Variable { name, .. } => {
                    let name = name.clone();
                    go_traversal::statement(self, statement);
                    self.shadow(&name);
                }
                GoStatement::Range { index, element, iterable, body } => {
                    self.expression(iterable);
                    self.shadowed.push(index.iter().chain([&*element]).cloned().collect());
                    self.block(body);
                    self.shadowed.pop();
                }
                GoStatement::Counting { variable, start, end, body } => {
                    self.expression(start);
                    self.shadowed.push([variable.clone()].into_iter().collect());
                    self.expression(end);
                    self.block(body);
                    self.shadowed.pop();
                }
                GoStatement::CountingDown { variable, start, body } => {
                    self.expression(start);
                    self.shadowed.push([variable.clone()].into_iter().collect());
                    self.block(body);
                    self.shadowed.pop();
                }
                GoStatement::IfAssert { name, value, then, .. } => {
                    self.expression(value);
                    self.shadowed.push([name.clone()].into_iter().collect());
                    self.block(then);
                    self.shadowed.pop();
                }
                _ => go_traversal::statement(self, statement),
            }
        }

        fn expression(&mut self, value: &mut GoExpression) {
            match value {
                GoExpression::Identifier(name) => self.found |= self.visible(name),
                GoExpression::Function { parameters, body, .. } => {
                    self.shadowed.push(parameters.iter().map(|(name, _)| name.clone()).collect());
                    self.block(body);
                    self.shadowed.pop();
                }
                _ => go_traversal::expression(self, value),
            }
        }
    }
    let mut free = Free { names, shadowed: vec![FxHashSet::default()], found: false };
    free.statement(&mut statement.clone());
    free.found
}
