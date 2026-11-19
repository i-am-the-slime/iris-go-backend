use super::aliases::is_named;
use crate::syntax::{GoDeclaration, GoExpression, GoStatement, GoType};
use crate::walk::{self, Walk};

pub(super) fn promote_references(declarations: &mut [GoDeclaration]) {
    for declaration in declarations {
        walk::each_block_in_declaration(declaration, |block| {
            for position in 0..block.len() {
                promote_at(block, position);
            }
        });
    }
}

fn promote_at(block: &mut [GoStatement], position: usize) {
    let Some(name) = defined_cell(&block[position]) else { return };
    let (upto, rest) = block.split_at_mut(position + 1);
    if !stays_local(rest, &name) {
        return;
    }
    for statement in rest {
        walk::each_expression_in_statement(statement, |expression| {
            if is_cell_value(expression, &name) {
                *expression = GoExpression::Identifier(name.clone());
            }
        });
    }
    upto[position] = local(std::mem::replace(&mut upto[position], GoStatement::Break));
}

fn defined_cell(statement: &GoStatement) -> Option<String> {
    let GoStatement::Define { names, values } = statement else { return None };
    let ([name], [GoExpression::Address(cell)]) = (names.as_slice(), values.as_slice()) else {
        return None;
    };
    let GoExpression::Composite { type_: GoType::Generic { name: generic, .. }, fields } =
        cell.as_ref()
    else {
        return None;
    };
    let [(Some(field), _)] = fields.as_slice() else { return None };
    (generic == "Ref" && field == "Value").then(|| name.clone())
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

fn is_cell_value(expression: &GoExpression, cell: &str) -> bool {
    matches!(expression, GoExpression::Field { value, name } if name == "Value" && is_named(value, cell))
}

fn stays_local(rest: &mut [GoStatement], name: &str) -> bool {
    let mut uses = Uses { name, escapes: false, reads: 0 };
    for statement in rest {
        uses.statement(statement);
    }
    !uses.escapes && uses.reads > 0
}

struct Uses<'a> {
    name: &'a str,
    escapes: bool,
    reads: usize,
}

impl Walk for Uses<'_> {
    fn statement(&mut self, statement: &mut GoStatement) {
        if let GoStatement::Assign { targets, values } = statement {
            for target in targets.iter_mut().filter(|target| !is_cell_value(target, self.name)) {
                self.expression(target);
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
        walk::statement(self, statement);
    }

    fn expression(&mut self, value: &mut GoExpression) {
        match value {
            _ if is_cell_value(value, self.name) => self.reads += 1,
            GoExpression::Identifier(name) if name == self.name => self.escapes = true,
            GoExpression::Function { parameters, .. }
                if parameters.iter().any(|(parameter, _)| parameter == self.name) =>
            {
                self.escapes = true
            }
            _ => walk::expression(self, value),
        }
    }
}
