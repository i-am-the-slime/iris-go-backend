//! The parts of a reused cell that already hold what the construction puts there.
//!
//! A case that takes a cell apart and builds it again, `Node _ left key value right -> Node Black
//! left key value right`, reuses the cell and would store every field back. A reused cell is
//! owned, so nothing changes it between the match that takes it apart and its reuse: the
//! constructor the match found, a field the match bound, and a field the match compared with a
//! constant are all still there, and storing them again does nothing.

use crate::monomorphic::traversal::for_each_child_mut;
use crate::monomorphic::{
    Expression, ExpressionKind, Guard, Guarded, Kept, LocalId, Pattern, PatternKind,
};

pub(super) fn mark_kept_fields(body: &mut Expression) {
    Matched::default().expression(body);
}

/// What the matches around an expression found in the cells they took apart, innermost last.
#[derive(Default)]
struct Matched {
    constructors: Vec<(LocalId, usize)>,
    fields: Vec<(Slot, ExpressionKind)>,
}

/// A cell, one of its constructors, and a field of that constructor.
type Slot = (LocalId, usize, usize);

impl Matched {
    fn expression(&mut self, expression: &mut Expression) {
        if let ExpressionKind::Reuse { cell, constructor, arguments, kept, .. } =
            &mut expression.kind
            && let ExpressionKind::Local(cell) = cell.kind
        {
            *kept = self.kept(cell, *constructor, arguments);
        }
        match &mut expression.kind {
            // A function may run after the cells it sees have been reused.
            ExpressionKind::Lambda { body, .. } => {
                let mut inside = Matched::default();
                inside.expression(body);
            }
            ExpressionKind::Case { scrutinees, alternatives } => {
                scrutinees.iter_mut().for_each(|scrutinee| self.expression(scrutinee));
                for alternative in alternatives {
                    let saved = self.save();
                    for (scrutinee, pattern) in scrutinees.iter().zip(&alternative.patterns) {
                        if let ExpressionKind::Local(cell) = scrutinee.kind {
                            self.pattern(cell, pattern);
                        }
                    }
                    self.guarded(&mut alternative.body);
                    self.restore(saved);
                }
            }
            _ => for_each_child_mut(expression, &mut |child| self.expression(child)),
        }
    }

    fn guarded(&mut self, guarded: &mut Guarded) {
        let branches = match guarded {
            Guarded::Unconditional(body) => return self.expression(body),
            Guarded::Guards(branches) => branches,
        };
        for branch in branches {
            let saved = self.save();
            for guard in &mut branch.guards {
                match guard {
                    Guard::Boolean(condition) => self.expression(condition),
                    Guard::Pattern { pattern, value } => {
                        self.expression(value);
                        if let ExpressionKind::Local(cell) = value.kind {
                            self.pattern(cell, pattern);
                        }
                    }
                }
            }
            self.expression(&mut branch.body);
            self.restore(saved);
        }
    }

    /// Notes what matching the cell against the pattern finds in it.
    fn pattern(&mut self, cell: LocalId, pattern: &Pattern) {
        match &pattern.kind {
            PatternKind::Named { local, pattern } => {
                self.pattern(cell, pattern);
                self.pattern(local.id, pattern);
            }
            PatternKind::Constructor { constructor, arguments, .. } => {
                self.constructors.push((cell, *constructor));
                for (field, argument) in arguments.iter().enumerate() {
                    let slot = (cell, *constructor, field);
                    if let Some(held) = held(argument) {
                        self.fields.push((slot, held));
                    }
                    if let PatternKind::Named { local, pattern } = &argument.kind {
                        self.pattern(local.id, pattern);
                    }
                }
            }
            _ => {}
        }
    }

    fn kept(&self, cell: LocalId, constructor: usize, arguments: &[Expression]) -> Kept {
        let constructor_kept = self.constructors.contains(&(cell, constructor));
        let mut fields = 0;
        for (field, argument) in arguments.iter().enumerate().take(u64::BITS as usize) {
            let slot = (cell, constructor, field);
            let holds = self
                .fields
                .iter()
                .any(|(matched, held)| *matched == slot && *held == argument.kind);
            if constructor_kept && holds {
                fields |= 1 << field;
            }
        }
        Kept { constructor: constructor_kept, fields }
    }

    fn save(&self) -> (usize, usize) {
        (self.constructors.len(), self.fields.len())
    }

    fn restore(&mut self, (constructors, fields): (usize, usize)) {
        self.constructors.truncate(constructors);
        self.fields.truncate(fields);
    }
}

/// The value a field matched against the pattern holds, when the pattern names it or fixes it.
fn held(pattern: &Pattern) -> Option<ExpressionKind> {
    match &pattern.kind {
        PatternKind::Variable(local) | PatternKind::Named { local, .. } => {
            Some(ExpressionKind::Local(local.id))
        }
        PatternKind::Literal(literal) => Some(ExpressionKind::Literal(literal.clone())),
        PatternKind::Constructor { data, constructor, arguments } if arguments.is_empty() => {
            Some(ExpressionKind::Construct {
                data: data.clone(),
                constructor: *constructor,
                arguments: vec![],
            })
        }
        _ => None,
    }
}
