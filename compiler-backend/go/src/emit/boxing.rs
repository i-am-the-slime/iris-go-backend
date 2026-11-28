//! Arrays at erased positions.
//!
//! The canonical boxed form of an array is `[]any`, which a reader at any view
//! of its type can take apart, but building it copies every element on the
//! way in and again on the way out. An array crosses as itself instead when
//! every array type that crosses into or out of erased positions, and might be
//! the same PureScript type, has one Go type: then no reader expects another
//! form than the one its writers store. Foreign values hold arrays that
//! JavaScript built in the canonical form, so once foreign values enter erased
//! positions every array keeps it, and once erased values leave for foreign
//! ones, so does every array type that might be one that crosses into or out
//! of a foreign value.

use rustc_hash::FxHashMap;

use super::packages::Spelling;
use super::reference_equality::BASIC_TYPES;
use super::{Emitter, call, identifier_expression};
use crate::erasure::Erasure;
use crate::error::GoResult;
use crate::monotype::{Monotype, MonotypeId};
use crate::syntax::{GoDeclaration, GoExpression, GoStatement, GoType};

#[derive(Default)]
pub(super) struct ArrayBoxes {
    crossings: Vec<Crossing>,
    by_monotype: FxHashMap<(MonotypeId, bool), usize>,
    pub(super) foreign_values_enter: bool,
    pub(super) erased_values_leave: bool,
}

struct Crossing {
    monotype: MonotypeId,
    go_type: GoType,
    /// Whether the array crosses into or out of a foreign value rather than an
    /// erased one.
    foreign: bool,
    /// The declarations of the functions that box and unbox the array, whose
    /// bodies are written once every crossing is known, and which are written.
    functions: [Option<usize>; 2],
    written: [bool; 2],
}

impl ArrayBoxes {
    pub(super) fn cross(&mut self, monotype: MonotypeId, go_type: GoType, foreign: bool) -> usize {
        let next = self.crossings.len();
        let index = *self.by_monotype.entry((monotype, foreign)).or_insert(next);
        if index == next {
            let functions = [None, None];
            let written = [false, false];
            let crossing = Crossing { monotype, go_type, foreign, functions, written };
            self.crossings.push(crossing);
        }
        index
    }
}

impl<Q> Emitter<'_, '_, '_, Q>
where
    Q: checking::ExternalQueries,
{
    /// An array put into an erased position (`boxing`) or taken out of one.
    pub(super) fn box_array(
        &mut self,
        value: GoExpression,
        array: MonotypeId,
        boxing: bool,
    ) -> GoResult<GoExpression> {
        let canonical = self.canonical(array)?;
        let go_type = self.go_type(array)?;
        let index = self.array_boxes.cross(array, go_type.clone(), false);
        if self.same_go_type(array, canonical)? {
            return Ok(match boxing {
                true => value,
                false => GoExpression::TypeAssertion { value: Box::new(value), type_: go_type },
            });
        }
        let direction = usize::from(!boxing);
        let name = match self.array_boxes.crossings[index].functions[direction] {
            Some(position) => self.type_declarations[position].name().map(str::to_string),
            None => None,
        };
        let name = match name {
            Some(name) => name,
            None => {
                let name = self.global_name(Spelling::Base("convert".into()));
                let boxed = GoType::Erased(Erasure::Boxing);
                let (parameter, result) = if boxing { (go_type, boxed) } else { (boxed, go_type) };
                let position = self.type_declarations.len();
                self.array_boxes.crossings[index].functions[direction] = Some(position);
                self.type_declarations.push(GoDeclaration::Function {
                    name: name.clone(),
                    parameters: vec![("value".into(), parameter)],
                    result: Some(result),
                    body: vec![],
                });
                name
            }
        };
        Ok(call(identifier_expression(&name), vec![value]))
    }

    /// Writes the body of every function that boxes or unboxes an array. The
    /// canonical bodies convert elements, which can make more arrays cross, so
    /// the families are found again until no crossing changes its form.
    pub(super) fn settle_array_boxes(&mut self) -> GoResult<()> {
        let unwritten = |crossing: &Crossing, direction: usize| {
            crossing.functions[direction].filter(|_| !crossing.written[direction])
        };
        let canonical = loop {
            let canonical = self.canonical_crossings();
            let changed = (0..canonical.len()).filter(|&index| canonical[index]).filter(|&index| {
                let crossing = &self.array_boxes.crossings[index];
                (0..2).any(|direction| unwritten(crossing, direction).is_some())
            });
            let changed: Vec<usize> = changed.collect();
            if changed.is_empty() {
                break canonical;
            }
            for index in changed {
                self.canonical_bodies(index)?;
            }
        };
        let value = identifier_expression("value");
        let mut direct = vec![];
        for (crossing, _) in self.array_boxes.crossings.iter().zip(canonical).filter(|(_, c)| !c) {
            let type_ = crossing.go_type.clone();
            let unboxed = GoExpression::TypeAssertion { value: Box::new(value.clone()), type_ };
            for (direction, returned) in [value.clone(), unboxed].into_iter().enumerate() {
                direct.extend(unwritten(crossing, direction).map(|position| (position, returned)));
            }
        }
        for (position, returned) in direct {
            self.set_body(position, vec![GoStatement::Return(Some(returned))]);
        }
        Ok(())
    }

    fn canonical_bodies(&mut self, index: usize) -> GoResult<()> {
        let crossings = &self.array_boxes.crossings;
        let Crossing { monotype: array, functions, written, .. } = crossings[index];
        self.array_boxes.crossings[index].written = functions.map(|function| function.is_some());
        let pending = |direction: usize| functions[direction].filter(|_| !written[direction]);
        let [boxing, unboxing] = [0, 1].map(pending);
        let canonical = self.canonical(array)?;
        let arrays = (self.monotypes.get(array), self.monotypes.get(canonical));
        let (&Monotype::Array(element), &Monotype::Array(erased)) = arrays else {
            unreachable!("invariant violated: a crossing array's canonical form is an array")
        };
        let value = identifier_expression("value");
        if let Some(position) = boxing {
            let mut body = vec![];
            let result = self.go_type(canonical)?;
            self.convert_elements(value.clone(), element, erased, &result, &mut body)?;
            self.set_body(position, body);
        }
        if let Some(position) = unboxing {
            let type_ = self.go_type(canonical)?;
            let asserted = GoExpression::TypeAssertion { value: Box::new(value), type_ };
            let values = vec![asserted];
            let mut body = vec![GoStatement::Define { names: vec!["array".into()], values }];
            let result = self.go_type(array)?;
            let elements = identifier_expression("array");
            self.convert_elements(elements, erased, element, &result, &mut body)?;
            self.set_body(position, body);
        }
        Ok(())
    }

    fn set_body(&mut self, position: usize, statements: Vec<GoStatement>) {
        if let GoDeclaration::Function { body, .. } = &mut self.type_declarations[position] {
            *body = statements;
        }
    }

    /// Whether each crossing array keeps the canonical form: its family, the
    /// crossings whose types may be views of one type, has more than one Go
    /// type or meets foreign values.
    fn canonical_crossings(&self) -> Vec<bool> {
        let boxes = &self.array_boxes;
        let types = boxes.crossings.iter().map(|crossing| crossing.go_type.clone());
        let mut types: Vec<GoType> = types.collect();
        types.iter_mut().for_each(|type_| self.resolve_aliases(type_));
        let root = |family: &[usize], mut index: usize| {
            while family[index] != index {
                index = family[index];
            }
            index
        };
        let mut family: Vec<usize> = (0..types.len()).collect();
        for right in 0..types.len() {
            for left in 0..right {
                let foreign = [left, right].map(|index| boxes.crossings[index].foreign);
                if (foreign[0] == foreign[1] || boxes.erased_values_leave)
                    && may_view_one_type(&types[left], &types[right])
                {
                    let (left, right) = (root(&family, left), root(&family, right));
                    family[right] = left;
                }
            }
        }
        let mut canonical = vec![boxes.foreign_values_enter; types.len()];
        for (index, crossing) in boxes.crossings.iter().enumerate() {
            let representative = root(&family, index);
            if crossing.foreign || types[index] != types[representative] {
                canonical[representative] = true;
            }
        }
        (0..types.len()).map(|index| canonical[root(&family, index)]).collect()
    }
}

/// Whether two Go types may be views of one PureScript type. Only Go's basic
/// types and arrays of them are told apart; erasure, named types, functions
/// and the rest may be anything.
fn may_view_one_type(left: &GoType, right: &GoType) -> bool {
    let basic = |type_: &GoType| match type_ {
        GoType::Named(name) => BASIC_TYPES.contains(&name.as_str()),
        GoType::Int | GoType::Float64 | GoType::Bool | GoType::Rune | GoType::String => true,
        _ => false,
    };
    match (left, right) {
        (GoType::Slice(left), GoType::Slice(right)) => may_view_one_type(left, right),
        (GoType::Slice(_), other) | (other, GoType::Slice(_)) => !basic(other),
        (left, right) if basic(left) && basic(right) => left == right,
        _ => true,
    }
}
