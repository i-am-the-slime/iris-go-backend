//! Range loops that read their element's fields in place.
//!
//! `for _, element := range array` copies every element into `element`, a block
//! copy per iteration for a large struct even when the body reads one or two
//! fields. When every use of `element` reads a field, the loop becomes
//! `for index := range array` and `element.field` becomes `array[index].field`.
//! Arrays are immutable, so each read sees what the copy would have held. Only
//! structs and pointers to them have fields, so scalar loops keep reading well.
//!
//! A loop keeps its copy when the element is used whole, assigned or
//! addressed, when a closure reads it (the closure could outlive a later
//! reassignment of the array variable), when a method may be called on it, or
//! when the array variable may change during the loop.

use rustc_hash::FxHashSet;

use crate::syntax::{GoDeclaration, GoExpression, GoStatement, Name};

use crate::walk::{self, Walk, each_expression_in_statement};

pub fn read_elements_in_place(declarations: &mut [GoDeclaration]) {
    for declaration in declarations {
        let mut names = FxHashSet::default();
        declaration.for_each_name_mut(&mut |name| {
            let (Name::Reference(name) | Name::Written(name) | Name::Binder(name)) = name;
            names.insert(name.clone());
        });
        walk::declaration(&mut InPlace { names }, declaration);
    }
}

struct InPlace {
    /// Every name the declaration uses, so that a new index shadows none.
    names: FxHashSet<String>,
}

impl Walk for InPlace {
    fn statement(&mut self, statement: &mut GoStatement) {
        walk::statement(self, statement);
        let GoStatement::Range { index, element, iterable, body } = statement else { return };
        if let GoExpression::Identifier(array) = iterable
            && element != "_"
            && reads_in_place(body, element, array)
        {
            let index = index.get_or_insert_with(|| self.fresh(element)).clone();
            let array = array.clone();
            let element = std::mem::replace(element, "_".to_string());
            read_from_array(body, &element, &array, &index);
        }
    }
}

impl InPlace {
    fn fresh(&mut self, element: &str) -> String {
        let mut candidate = format!("{element}Index");
        let mut suffix = 2;
        while self.names.contains(&candidate) {
            candidate = format!("{element}Index{suffix}");
            suffix += 1;
        }
        self.names.insert(candidate.clone());
        candidate
    }
}

/// Whether `element` only has its fields read in `body`, outside closures, and
/// `array` is neither rebound nor reassigned there.
fn reads_in_place(body: &mut Vec<GoStatement>, element: &str, array: &str) -> bool {
    let mut check = Check { element, array, reads: 0, refused: false, closure: false };
    check.block(body);
    !check.refused && check.reads > 0
}

struct Check<'a> {
    element: &'a str,
    array: &'a str,
    reads: usize,
    refused: bool,
    /// Whether the code visited is inside a function literal.
    closure: bool,
}

impl Check<'_> {
    fn binds(&mut self, name: &str) {
        if name == self.element || name == self.array {
            self.refused = true;
        }
    }
}

impl Walk for Check<'_> {
    fn statement(&mut self, statement: &mut GoStatement) {
        match statement {
            GoStatement::Define { names, .. } => names.iter().for_each(|name| self.binds(name)),
            GoStatement::Variable { name, .. } | GoStatement::IfAssert { name, .. } => {
                self.binds(name)
            }
            GoStatement::Assign { targets, .. } => {
                for target in targets {
                    let mut root = &*target;
                    while let GoExpression::Field { value, .. }
                    | GoExpression::Index { value, .. } = root
                    {
                        root = value;
                    }
                    if let GoExpression::Identifier(name) = root
                        && (name == self.element || name == self.array)
                    {
                        self.refused = true;
                    }
                }
            }
            GoStatement::Range { index, element, .. } => {
                index.iter().for_each(|index| self.binds(index));
                self.binds(element);
            }
            GoStatement::Counting { variable, .. } | GoStatement::CountingDown { variable, .. } => {
                self.binds(variable)
            }
            _ => {}
        }
        walk::statement(self, statement);
    }

    fn expression(&mut self, value: &mut GoExpression) {
        match value {
            GoExpression::Field { value: base, .. } if matches!(&**base, GoExpression::Identifier(name) if name == self.element) =>
            {
                self.refused |= self.closure;
                self.reads += 1;
                return;
            }
            GoExpression::Identifier(name) => self.refused |= name == self.element,
            GoExpression::Address(operand) => {
                if let GoExpression::Identifier(name) = &**operand
                    && (name == self.array || name == self.element)
                {
                    self.refused = true;
                }
            }
            GoExpression::Function { parameters, body, .. } => {
                parameters.iter().for_each(|(name, _)| self.binds(name));
                let outside = std::mem::replace(&mut self.closure, true);
                self.block(body);
                self.closure = outside;
                return;
            }
            GoExpression::Call { function, .. } => {
                // An exported name on the element may be a method of a
                // go-support type, whose receiver could be the element's address.
                if let GoExpression::Field { value: base, name } = &**function
                    && let GoExpression::Identifier(base) = &**base
                    && base == self.element
                    && name.starts_with(|c: char| c.is_uppercase())
                {
                    self.refused = true;
                }
            }
            _ => {}
        }
        walk::expression(self, value);
    }
}

fn read_from_array(body: &mut [GoStatement], element: &str, array: &str, index: &str) {
    let mut replace = |value: &mut GoExpression| {
        if matches!(value, GoExpression::Identifier(name) if name == element) {
            *value = GoExpression::Index {
                value: Box::new(GoExpression::Identifier(array.to_string())),
                index: Box::new(GoExpression::Identifier(index.to_string())),
            };
        }
    };
    for statement in body {
        each_expression_in_statement(statement, &mut replace);
    }
}
