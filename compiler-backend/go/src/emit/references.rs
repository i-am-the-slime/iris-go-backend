use super::aliases::is_named;
use crate::go_traversal::{self, Walk};
use crate::syntax::{GoDeclaration, GoExpression, GoStatement, GoType};

#[derive(Clone, Copy, PartialEq, Eq)]
enum Cell {
    Reference,
    Array,
}

pub(super) fn promote_references(declarations: &mut [GoDeclaration]) {
    for declaration in declarations {
        go_traversal::each_block_in_declaration(declaration, |block| {
            for position in 0..block.len() {
                promote_at(block, position);
            }
        });
    }
}

fn promote_at(block: &mut [GoStatement], position: usize) {
    let Some((name, cell)) = defined_cell(&block[position]) else { return };
    let (upto, rest) = block.split_at_mut(position + 1);
    if !stays_local(rest, &name, cell) {
        return;
    }
    for statement in rest {
        go_traversal::each_expression_in_statement(statement, |expression| {
            if is_cell_value(expression, &name, cell) {
                *expression = GoExpression::Identifier(name.clone());
            }
        });
    }
    let definition = std::mem::replace(&mut upto[position], GoStatement::Break);
    upto[position] = match cell {
        Cell::Reference => local(definition),
        Cell::Array => local_array(definition),
    };
}

fn defined_cell(statement: &GoStatement) -> Option<(String, Cell)> {
    let GoStatement::Define { names, values } = statement else { return None };
    let ([name], [value]) = (names.as_slice(), values.as_slice()) else { return None };
    if is_fresh_array(value) {
        return Some((name.clone(), Cell::Array));
    }
    let GoExpression::Address(cell) = value else { return None };
    match cell.as_ref() {
        GoExpression::Composite { type_: GoType::Slice(_), .. } => {
            Some((name.clone(), Cell::Array))
        }
        GoExpression::Composite { type_: GoType::Generic { name: generic, .. }, fields } => {
            let [(Some(field), _)] = fields.as_slice() else { return None };
            (generic == "Ref" && field == "Value").then(|| (name.clone(), Cell::Reference))
        }
        _ => None,
    }
}

fn is_fresh_array(value: &GoExpression) -> bool {
    let GoExpression::Call { function, .. } = value else { return false };
    let GoExpression::Qualified { package, name } = function.as_ref() else { return false };
    package == "array" && matches!(name.as_str(), "Thaw" | "UnsafeThaw")
}

fn local(statement: GoStatement) -> GoStatement {
    let GoStatement::Define { mut names, mut values } = statement else {
        unreachable!("invariant violated: a promoted cell is a definition")
    };
    let name = names.remove(0);
    let GoExpression::Address(cell) = values.remove(0) else {
        unreachable!("invariant violated: a promoted cell is an address")
    };
    let GoExpression::Composite { type_: GoType::Generic { mut arguments, .. }, mut fields } =
        *cell
    else {
        unreachable!("invariant violated: a promoted cell is a Ref literal")
    };
    let value = fields.remove(0).1;
    if super::is_untyped_constant(&value) {
        let type_ = arguments.remove(0);
        let value = (!super::is_nil(&value)).then_some(value);
        return GoStatement::Variable { name, type_, value };
    }
    GoStatement::Define { names: vec![name], values: vec![value] }
}

fn local_array(statement: GoStatement) -> GoStatement {
    let GoStatement::Define { names, mut values } = statement else {
        unreachable!("invariant violated: a promoted cell is a definition")
    };
    let elements = match values.remove(0) {
        GoExpression::Address(elements) => *elements,
        fresh => GoExpression::Unary { operator: "*", operand: Box::new(fresh) },
    };
    GoStatement::Define { names, values: vec![elements] }
}

fn is_cell_value(expression: &GoExpression, cell: &str, kind: Cell) -> bool {
    match (expression, kind) {
        (GoExpression::Field { value, name }, Cell::Reference) => {
            name == "Value" && is_named(value, cell)
        }
        (GoExpression::Unary { operator: "*", operand }, Cell::Array) => is_named(operand, cell),
        _ => false,
    }
}

fn stays_local(rest: &mut [GoStatement], name: &str, cell: Cell) -> bool {
    let mut uses = Uses { name, cell, escapes: false, reads: 0 };
    for statement in rest {
        uses.statement(statement);
    }
    !uses.escapes && uses.reads > 0
}

struct Uses<'a> {
    name: &'a str,
    cell: Cell,
    escapes: bool,
    reads: usize,
}

impl Walk for Uses<'_> {
    fn statement(&mut self, statement: &mut GoStatement) {
        if let GoStatement::Assign { targets, values } = statement {
            for target in targets.iter_mut() {
                if !is_cell_value(target, self.name, self.cell) {
                    self.expression(target);
                }
            }
            values.iter_mut().for_each(|value| self.expression(value));
            return;
        }
        let bound: Vec<&str> = match statement {
            GoStatement::Define { names, .. } => names.iter().map(String::as_str).collect(),
            GoStatement::Variable { name, .. } | GoStatement::IfAssert { name, .. } => vec![name],
            GoStatement::Range { element, index, .. } => {
                index.iter().map(String::as_str).chain([element.as_str()]).collect()
            }
            GoStatement::Counting { variable, .. } | GoStatement::CountingDown { variable, .. } => {
                vec![variable.as_str()]
            }
            _ => vec![],
        };
        if bound.contains(&self.name) {
            self.escapes = true;
        }
        go_traversal::statement(self, statement);
    }

    fn expression(&mut self, value: &mut GoExpression) {
        match value {
            _ if is_cell_value(value, self.name, self.cell) => self.reads += 1,
            GoExpression::Identifier(name) if name == self.name => self.escapes = true,
            GoExpression::Function { parameters, .. }
                if parameters.iter().any(|(parameter, _)| parameter == self.name) =>
            {
                self.escapes = true
            }
            _ => go_traversal::expression(self, value),
        }
    }
}
