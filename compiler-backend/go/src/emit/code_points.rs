use super::merging::same_code;
use crate::go_traversal::{each_block_in_declaration, each_expression_in_statement};
use crate::syntax::{
    GoBinaryOperator, GoDeclaration, GoExpression, GoPackage, GoStatement, Name, statements_names,
};

pub(super) fn read_code_points_once(declarations: &mut [GoDeclaration]) {
    for declaration in declarations {
        each_block_in_declaration(declaration, |block| {
            let mut position = 0;
            while position < block.len() {
                match answered_by_read(&block[position]) {
                    Some(read) => {
                        let length = read.len();
                        block.splice(position..=position, read);
                        position += length;
                    }
                    None => position += 1,
                }
            }
        });
    }
}

fn answered_by_read(chain: &GoStatement) -> Option<Vec<GoStatement>> {
    let mut arms: Vec<(&GoExpression, &[GoStatement])> = vec![];
    let mut rest = chain;
    let read = loop {
        let GoStatement::If { condition, then, otherwise } = rest else { return None };
        arms.push((condition, then));
        match otherwise.as_slice() {
            [next @ GoStatement::If { .. }] => rest = next,
            read => break read,
        }
    };
    let statements = without_line_marks(read);
    let read_at = CodePointRead::of(&statements)?;
    let mut text_known_present = false;
    for (condition, body) in arms {
        let disjuncts = split(condition, GoBinaryOperator::LogicalOr);
        let disjuncts: Vec<Vec<&GoExpression>> = disjuncts
            .into_iter()
            .map(|disjunct| split(disjunct, GoBinaryOperator::LogicalAnd))
            .collect();
        let answer = read_at.answer(&disjuncts, text_known_present)?;
        if !same_code(body, &answer) {
            return None;
        }
        text_known_present |= disjuncts.iter().any(|conjuncts| read_at.rules_out_empty(conjuncts));
    }
    Some(read.to_vec())
}

struct CodePointRead<'r> {
    point: &'r str,
    index: &'r GoExpression,
    text: &'r GoExpression,
    present: Vec<GoStatement>,
    absent: Vec<GoStatement>,
}

impl<'r> CodePointRead<'r> {
    fn of(read: &'r [GoStatement]) -> Option<CodePointRead<'r>> {
        let (GoStatement::Define { names, values }, tested) = read.split_first()? else {
            return None;
        };
        let [point, found] = names.as_slice() else { return None };
        let [GoExpression::Call { function, arguments }] = values.as_slice() else { return None };
        let [_, _, index, text] = arguments.as_slice() else { return None };
        let simple = |value: &GoExpression| {
            matches!(value, GoExpression::Identifier(_) | GoExpression::Integer(_))
        };
        let reads = function.is_qualified(GoPackage::Direct, "CodePointAt")
            && simple(index)
            && simple(text);
        if !reads {
            return None;
        }
        let (present, absent) =
            match tested {
                [
                    GoStatement::If { condition: GoExpression::Identifier(test), then, otherwise },
                ] if test == found => (then.clone(), otherwise.clone()),
                [
                    GoStatement::Variable { name, value: None, .. },
                    GoStatement::If { condition: GoExpression::Identifier(test), then, otherwise },
                    rest @ ..,
                ] if test == found => {
                    let mut rest = rest.to_vec();
                    let mut mentioned = false;
                    statements_names(&mut rest, &mut |mentioning| match mentioning {
                        Name::Reference(other) => mentioned |= other == point || other == found,
                        Name::Binder(other) | Name::Written(other) => {
                            mentioned |= other == point || other == found || other == name
                        }
                    });
                    if mentioned {
                        return None;
                    }
                    let present = assigned(then, name)?;
                    let absent = assigned(otherwise, name)?;
                    (substituted(&rest, name, present), substituted(&rest, name, absent))
                }
                _ => return None,
            };
        Some(CodePointRead { point, index, text, present, absent })
    }

    fn answer(
        &self,
        disjuncts: &[Vec<&GoExpression>],
        text_known_present: bool,
    ) -> Option<Vec<GoStatement>> {
        let absent = disjuncts.iter().all(|conjuncts| {
            conjuncts.iter().any(|conjunct| {
                self.tests_empty_text(conjunct)
                    || compares(conjunct, GoBinaryOperator::LessThan, self.index, 0)
            })
        });
        if absent {
            return Some(self.absent.clone());
        }
        let first = matches!(disjuncts, [conjuncts] if matches!(conjuncts.as_slice(),
            [only] if compares(only, GoBinaryOperator::Equal, self.index, 0)));
        let first_point = GoExpression::Call {
            function: Box::new(GoExpression::qualified(GoPackage::Direct, "CodePointAt0")),
            arguments: vec![GoExpression::nil(), self.text.clone()],
        };
        (first && text_known_present).then(|| substituted(&self.present, self.point, &first_point))
    }

    fn rules_out_empty(&self, conjuncts: &[&GoExpression]) -> bool {
        conjuncts.iter().any(|conjunct| self.tests_empty_text(conjunct))
            && conjuncts.iter().all(|conjunct| {
                self.tests_empty_text(conjunct)
                    || compares(conjunct, GoBinaryOperator::Equal, self.index, 0)
            })
    }

    fn tests_empty_text(&self, conjunct: &GoExpression) -> bool {
        let GoExpression::Binary { operator: GoBinaryOperator::Equal, left, right } = conjunct
        else {
            return false;
        };
        **left == *self.text && matches!(&**right, GoExpression::String(text) if text.is_empty())
    }
}

fn assigned<'s>(branch: &'s [GoStatement], name: &str) -> Option<&'s GoExpression> {
    let mut statements =
        branch.iter().filter(|statement| !matches!(statement, GoStatement::Line(_)));
    let (Some(GoStatement::Assign { targets, values }), None) =
        (statements.next(), statements.next())
    else {
        return None;
    };
    let ([GoExpression::Identifier(target)], [value]) = (targets.as_slice(), values.as_slice())
    else {
        return None;
    };
    (target == name).then_some(value)
}

fn without_line_marks(statements: &[GoStatement]) -> Vec<GoStatement> {
    let statements =
        statements.iter().filter(|statement| !matches!(statement, GoStatement::Line(_)));
    statements.cloned().collect()
}

fn substituted(statements: &[GoStatement], name: &str, value: &GoExpression) -> Vec<GoStatement> {
    let mut statements = statements.to_vec();
    for statement in &mut statements {
        each_expression_in_statement(statement, |part| {
            if matches!(part, GoExpression::Identifier(found) if found == name) {
                *part = value.clone();
            }
        });
    }
    statements
}

fn compares(
    condition: &GoExpression,
    expected: GoBinaryOperator,
    value: &GoExpression,
    constant: i64,
) -> bool {
    let GoExpression::Binary { operator, left, right } = condition else { return false };
    *operator == expected && **left == *value && **right == GoExpression::Integer(constant)
}

fn split(condition: &GoExpression, operator: GoBinaryOperator) -> Vec<&GoExpression> {
    match condition {
        GoExpression::Binary { operator: found, left, right } if *found == operator => {
            let mut parts = split(left, operator);
            parts.extend(split(right, operator));
            parts
        }
        condition => vec![condition],
    }
}
