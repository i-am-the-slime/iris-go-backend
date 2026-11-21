use files::FileId;

use crate::mono::{Expression, Program, SourcePosition};
use crate::simplify::for_each_child_mut;

pub fn attribute_inlined_code_to_call_sites(program: &mut Program) {
    for function in &mut program.functions {
        let Some(home) = function.origin else { continue };
        let enclosing = function.position.filter(|position| position.file == home);
        attribute_to_home(&mut function.body, home, enclosing);
    }
}

fn attribute_to_home(expression: &mut Expression, home: FileId, enclosing: Option<SourcePosition>) {
    let enclosing = match expression.position {
        Some(position) if position.file == home => Some(position),
        Some(position) => {
            expression.position = enclosing.or(Some(position));
            enclosing
        }
        None => enclosing,
    };
    for_each_child_mut(expression, &mut |child| attribute_to_home(child, home, enclosing));
}
