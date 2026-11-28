use rustc_hash::FxHashSet;

use super::lengths::written_by_literals;
use super::views::evaluated_first;
use super::{binary, builtin_call, identifier_expression};
use crate::go_traversal::{self, Walk};
use crate::naming::numbered;
use crate::syntax::{
    DeclarationNames, GoBinaryOperator, GoBuiltin, GoDeclaration, GoExpression, GoPackage,
    GoStatement, GoType,
};

pub fn read_ascii_heads(
    declarations: &mut [GoDeclaration],
    names: &mut [DeclarationNames],
    taken: &dyn Fn(&str) -> bool,
) {
    for (declaration, names) in declarations.iter_mut().zip(names) {
        let written_by_literals = written_by_literals(declaration);
        let mut function = Function { names: &mut names.names, written_by_literals, taken };
        go_traversal::declaration(&mut function, declaration);
    }
}

struct Function<'a> {
    names: &'a mut FxHashSet<String>,
    written_by_literals: FxHashSet<String>,
    taken: &'a dyn Fn(&str) -> bool,
}

impl Walk for Function<'_> {
    fn statement(&mut self, statement: &mut GoStatement) {
        match statement {
            GoStatement::Loop(body)
            | GoStatement::LabeledLoop { body, .. }
            | GoStatement::Range { body, .. }
            | GoStatement::Counting { body, .. }
            | GoStatement::CountingDown { body, .. } => Looped(self).block(body),
            statement => go_traversal::statement(self, statement),
        }
    }
}

struct Looped<'f, 'a>(&'f mut Function<'a>);

impl Walk for Looped<'_, '_> {
    fn block(&mut self, body: &mut Vec<GoStatement>) {
        let mut position = 0;
        while position < body.len() {
            if let Some(replaced) = self.0.read_whole_head(&body[position]) {
                let added = replaced.len();
                body.splice(position..=position, replaced);
                position += added;
                continue;
            }
            let before = self.0.hoist_heads(&mut body[position]);
            go_traversal::statement(self, &mut body[position]);
            let added = before.len();
            body.splice(position..position, before);
            position += added + 1;
        }
    }

    fn expression(&mut self, value: &mut GoExpression) {
        if let GoExpression::Function { body, .. } = value {
            self.0.block(body);
            return;
        }
        go_traversal::expression(self, value);
    }
}

impl Function<'_> {
    fn read_whole_head(&self, statement: &GoStatement) -> Option<Vec<GoStatement>> {
        match statement {
            GoStatement::Define { names, values } => match (names.as_slice(), values.as_slice()) {
                ([name], [value]) => {
                    let head = Head::of(value, &self.written_by_literals)
                        .filter(|head| head.text != *name)?;
                    Some(head.statements(name).to_vec())
                }
                ([after, before], [value]) => {
                    let split = Split::of(value, &self.written_by_literals)
                        .filter(|split| split.text != *after && split.text != *before)?;
                    Some(split.statements(after, before))
                }
                _ => None,
            },
            GoStatement::Assign { targets, values } => {
                let [GoExpression::Identifier(name)] = targets.as_slice() else { return None };
                let [value] = values.as_slice() else { return None };
                let head = Head::of(value, &self.written_by_literals)?;
                let [_, test] = head.statements(name);
                Some(vec![test])
            }
            _ => None,
        }
    }

    fn hoist_heads(&mut self, statement: &mut GoStatement) -> Vec<GoStatement> {
        let mut heads = vec![];
        if let Some(values) = evaluated_first(statement) {
            for value in values {
                self.replace_heads(value, &mut heads);
            }
        }
        heads.into_iter().flat_map(|(name, head)| head.statements(&name)).collect()
    }

    fn replace_heads(&mut self, value: &mut GoExpression, heads: &mut Vec<(String, Head)>) {
        if let Some(head) = Head::of(value, &self.written_by_literals) {
            let name = self.fresh(format!("{}{}", head.text, head.kind.suffix()));
            *value = GoExpression::Identifier(name.clone());
            heads.push((name, head));
            return;
        }
        match value {
            GoExpression::Call { function, arguments } => {
                self.replace_heads(function, heads);
                arguments.iter_mut().for_each(|argument| self.replace_heads(argument, heads));
            }
            GoExpression::Binary { operator, left, .. } if operator.is_logical() => {
                self.replace_heads(left, heads);
            }
            GoExpression::Binary { left, right, .. } => {
                self.replace_heads(left, heads);
                self.replace_heads(right, heads);
            }
            GoExpression::Composite { fields, .. } => {
                fields.iter_mut().for_each(|(_, field)| self.replace_heads(field, heads));
            }
            GoExpression::Unary { operand: value, .. }
            | GoExpression::Conversion { value, .. }
            | GoExpression::Spread(value)
            | GoExpression::Attributed { value, .. } => self.replace_heads(value, heads),
            _ => {}
        }
    }

    fn fresh(&mut self, base: String) -> String {
        let candidate = numbered(&base, |name| self.names.contains(name) || (self.taken)(name));
        self.names.insert(candidate.clone());
        candidate
    }
}

#[derive(Clone, Copy)]
enum HeadKind {
    CodeUnit,
    Rest,
    Prefix,
    Counted,
}

impl HeadKind {
    fn of(function: &GoExpression, count: i64) -> Option<HeadKind> {
        let kind = match function.name_in(GoPackage::Prim)? {
            "CharAt" => HeadKind::CodeUnit,
            "CodeUnitDrop" => HeadKind::Rest,
            "CodeUnitTake" => HeadKind::Prefix,
            "CodeUnitLengthUpTo" => HeadKind::Counted,
            _ => return None,
        };
        let counts = match kind {
            HeadKind::CodeUnit => 0..=1,
            HeadKind::Rest | HeadKind::Prefix | HeadKind::Counted => 1..=2,
        };
        counts.contains(&count).then_some(kind)
    }

    fn suffix(self) -> &'static str {
        match self {
            HeadKind::CodeUnit => "Unit",
            HeadKind::Rest => "Rest",
            HeadKind::Prefix => "Prefix",
            HeadKind::Counted => "Counted",
        }
    }

    fn last_byte(self, count: i64) -> i64 {
        match self {
            HeadKind::CodeUnit => count,
            HeadKind::Rest | HeadKind::Prefix | HeadKind::Counted => count - 1,
        }
    }
}

struct Head {
    kind: HeadKind,
    count: i64,
    text: String,
    asked: GoExpression,
}

impl Head {
    fn of(value: &GoExpression, written_by_literals: &FxHashSet<String>) -> Option<Head> {
        let position = literal_position_call(value, written_by_literals)?;
        let LiteralPosition { function, count, text } = position;
        let kind = HeadKind::of(function, count)?;
        Some(Head { kind, count, text, asked: value.clone() })
    }

    fn statements(self, name: &str) -> [GoStatement; 2] {
        let text = || Box::new(identifier_expression(&self.text));
        let count = || Box::new(GoExpression::Integer(self.count));
        let (type_, read) = match self.kind {
            HeadKind::CodeUnit => (
                GoType::Rune,
                GoExpression::Conversion {
                    type_: GoType::Rune,
                    value: Box::new(GoExpression::Index { value: text(), index: count() }),
                },
            ),
            HeadKind::Rest => (
                GoType::String,
                GoExpression::Slice { value: text(), low: Some(count()), high: None },
            ),
            HeadKind::Prefix => (
                GoType::String,
                GoExpression::Slice { value: text(), low: None, high: Some(count()) },
            ),
            HeadKind::Counted => (GoType::Int, *count()),
        };
        let assign = |value| GoStatement::Assign {
            targets: vec![identifier_expression(name)],
            values: vec![value],
        };
        [
            GoStatement::Variable { name: name.to_string(), type_, value: None },
            GoStatement::If {
                condition: ascii_through(&self.text, self.kind.last_byte(self.count)),
                then: vec![assign(read)],
                otherwise: vec![assign(self.asked)],
            },
        ]
    }
}

struct Split {
    count: i64,
    text: String,
    asked: GoExpression,
}

impl Split {
    fn of(value: &GoExpression, written_by_literals: &FxHashSet<String>) -> Option<Split> {
        let position = literal_position_call(value, written_by_literals)?;
        let LiteralPosition { function, count, text } = position;
        (function.is_qualified(GoPackage::Direct, "SplitAt") && (1..=2).contains(&count))
            .then(|| Split { count, text, asked: value.clone() })
    }

    fn statements(self, after: &str, before: &str) -> Vec<GoStatement> {
        let text = || Box::new(identifier_expression(&self.text));
        let count = || Some(Box::new(GoExpression::Integer(self.count)));
        let targets = || vec![identifier_expression(after), identifier_expression(before)];
        let split = vec![
            GoExpression::Slice { value: text(), low: count(), high: None },
            GoExpression::Slice { value: text(), low: None, high: count() },
        ];
        let variable = |name: &str| GoStatement::Variable {
            name: name.to_string(),
            type_: GoType::String,
            value: None,
        };
        vec![
            variable(after),
            variable(before),
            GoStatement::If {
                condition: ascii_through(&self.text, self.count - 1),
                then: vec![GoStatement::Assign { targets: targets(), values: split }],
                otherwise: vec![GoStatement::Assign {
                    targets: targets(),
                    values: vec![self.asked],
                }],
            },
        ]
    }
}

struct LiteralPosition<'v> {
    function: &'v GoExpression,
    count: i64,
    text: String,
}

fn literal_position_call<'v>(
    value: &'v GoExpression,
    written_by_literals: &FxHashSet<String>,
) -> Option<LiteralPosition<'v>> {
    let GoExpression::Call { function, arguments } = value else { return None };
    if !matches!(**function, GoExpression::Qualified { .. }) {
        return None;
    }
    let [GoExpression::Integer(count), GoExpression::Identifier(text)] = arguments.as_slice()
    else {
        return None;
    };
    (!written_by_literals.contains(text)).then(|| LiteralPosition {
        function,
        count: *count,
        text: text.clone(),
    })
}

fn ascii_through(text: &str, last: i64) -> GoExpression {
    let byte = |at| GoExpression::Index {
        value: Box::new(identifier_expression(text)),
        index: Box::new(GoExpression::Integer(at)),
    };
    let bytes = match last {
        0 => byte(0),
        last => binary(GoBinaryOperator::BitwiseOr, byte(0), byte(last)),
    };
    let length = builtin_call(GoBuiltin::Len, vec![identifier_expression(text)]);
    binary(
        GoBinaryOperator::LogicalAnd,
        binary(GoBinaryOperator::GreaterThan, length, GoExpression::Integer(last)),
        binary(GoBinaryOperator::LessThan, bytes, GoExpression::Integer(0x80)),
    )
}
