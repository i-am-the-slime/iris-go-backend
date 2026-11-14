//! The Go struct of a data type with fields.
//!
//! Go's allocator charges for every byte of a cell and the garbage collector
//! scans a cell only up to its last pointer, so the struct is kept small and
//! its pointers come first:
//!
//! - The tag is a `uint8` when the constructors fit in one.
//! - Constructors whose fields have the same types, in the same order, store
//!   them in the same slots, since a value holds one constructor at a time.
//!   `Add Expr Expr | Mul Expr Expr` needs two slots, not four.
//! - Slots are declared in an order that leaves no padding between them, with
//!   every slot that holds a pointer before every slot that holds none.
//!
//! The same plan sizes a data type that is small enough to be held by value,
//! so the size limit is applied to the struct Go actually lays out.

use rustc_hash::FxHashSet;

use super::{Emitter, identifier};
use crate::error::{GoError, GoResult};
use crate::monotype::{DataConstructor, DataType, Monotype, MonotypeId};
use crate::syntax::GoType;

/// The size and alignment Go gives a value, and whether the collector scans it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct Shape {
    size: usize,
    align: usize,
    pointers: bool,
}

impl Shape {
    const POINTER: Shape = Shape { size: 8, align: 8, pointers: true };

    fn scalar(size: usize) -> Shape {
        Shape { size, align: size.max(1), pointers: false }
    }

    fn words(words: usize) -> Shape {
        Shape { size: 8 * words, align: 8, pointers: true }
    }

    /// A struct of fields declared in the given order.
    fn of_struct(fields: impl IntoIterator<Item = Shape>) -> Shape {
        let mut size: usize = 0;
        let mut align = 1;
        let mut pointers = false;
        let mut last_is_empty = false;
        for field in fields {
            size = size.next_multiple_of(field.align) + field.size;
            align = align.max(field.align);
            pointers |= field.pointers;
            last_is_empty = field.size == 0;
        }
        // Go pads a trailing empty field, so that its address stays inside the struct.
        if last_is_empty && size > 0 {
            size += 1;
        }
        Shape { size: size.next_multiple_of(align), align, pointers }
    }

    pub(super) fn size(self) -> usize {
        self.size
    }

    /// Empty slots first, then slots holding pointers, then the rest, each
    /// group from the widest alignment down, which leaves no padding between
    /// slots of one group.
    fn declaration_rank(self) -> (u8, std::cmp::Reverse<usize>) {
        let group = if self.size == 0 {
            0
        } else if self.pointers {
            1
        } else {
            2
        };
        (group, std::cmp::Reverse(self.align))
    }
}

/// The tag of a data type with this many constructors.
pub(super) fn tag_type(constructors: usize) -> GoType {
    if constructors <= 256 { GoType::Named("uint8".into()) } else { GoType::Int }
}

fn tag_shape(constructors: usize) -> Shape {
    if constructors <= 256 { Shape::scalar(1) } else { Shape::scalar(8) }
}

/// Where each constructor keeps its fields in its data type's struct.
pub(super) struct SlotPlan {
    /// The slot of each field of each constructor.
    pub constructors: Vec<Vec<String>>,
    /// The struct's fields in declaration order.
    pub slots: Vec<Slot>,
    /// How many of the slots come before the first slot without pointers.
    pub pointer_prefix: usize,
    /// The size and alignment of the struct.
    pub shape: Shape,
}

pub(super) enum Slot {
    Tag,
    Field { name: String, monotype: MonotypeId },
}

impl<'q, Q> Emitter<'_, '_, 'q, Q>
where
    Q: checking::ExternalQueries,
{
    /// Plans the struct of a data type whose constructors have fields.
    pub(super) fn plan_slots(&mut self, constructors: &[DataConstructor]) -> GoResult<SlotPlan> {
        let mut groups = groups_of_equal_fields(constructors);
        let mut named = NamedSlots::new(constructors, &groups);
        if !named.are_distinct() {
            // A constructor named like a shared slot, such as `Field`, keeps its own slots.
            groups = (0..constructors.len()).map(|index| vec![index]).collect();
            named = NamedSlots::new(constructors, &groups);
        }
        self.arrange_slots(constructors.len(), named.constructors, named.fields)
    }

    /// Orders the slots of a struct whose `tags` constructors keep their
    /// fields in the named slots.
    pub(super) fn arrange_slots(
        &mut self,
        tags: usize,
        constructors: Vec<Vec<String>>,
        fields: Vec<(String, MonotypeId)>,
    ) -> GoResult<SlotPlan> {
        let mut slots = vec![];
        if tags > 1 {
            slots.push((Slot::Tag, tag_shape(tags)));
        }
        for (name, monotype) in fields {
            let shape = self.value_shape(monotype)?;
            slots.push((Slot::Field { name, monotype }, shape));
        }
        slots.sort_by_key(|(_, shape)| shape.declaration_rank());
        let shape = Shape::of_struct(slots.iter().map(|(_, shape)| *shape));
        let pointer_prefix =
            slots.iter().filter(|(_, shape)| shape.declaration_rank().0 < 2).count();
        let slots = slots.into_iter().map(|(slot, _)| slot).collect();
        Ok(SlotPlan { constructors, slots, pointer_prefix, shape })
    }

    /// The shape of a data type held by value, or `None` when it cannot be:
    /// it contains itself or erases its arguments.
    pub(super) fn inline_shape(&mut self, data: &DataType) -> GoResult<Option<Shape>> {
        if let Some(&shape) = self.inline_shapes.get(data) {
            return Ok(shape);
        }
        let constructors = match self.monotypes.constructors(&mut self.context, data)? {
            Ok(constructors) => constructors,
            Err(state) => {
                return Err(GoError::Unsupported { definition: "code generation".into(), state });
            }
        };
        let erases_arguments =
            data.arguments.iter().any(|&argument| self.context.types.contains_erased(argument));
        let shape = if erases_arguments || self.contains_itself(data)? {
            None
        } else if constructors.iter().all(|constructor| constructor.fields.is_empty()) {
            Some(tag_shape(constructors.len()))
        } else {
            Some(self.plan_slots(&constructors)?.shape)
        };
        self.inline_shapes.insert(data.clone(), shape);
        Ok(shape)
    }

    fn value_shape(&mut self, monotype: MonotypeId) -> GoResult<Shape> {
        Ok(match self.monotypes.get(monotype).clone() {
            Monotype::Unit => Shape::scalar(0),
            Monotype::Boolean => Shape::scalar(1),
            Monotype::Int | Monotype::Char => Shape::scalar(4),
            Monotype::Number => Shape::scalar(8),
            Monotype::String | Monotype::Erased(_) | Monotype::Opaque => Shape::words(2),
            Monotype::Error => Shape::words(4),
            Monotype::Array(_) => Shape::words(3),
            Monotype::Record(fields) => {
                let mut shapes = vec![];
                for field in fields.iter() {
                    shapes.push(self.value_shape(field.monotype)?);
                }
                Shape::of_struct(shapes)
            }
            Monotype::Data(data) => {
                if self.is_boxed(&data)? {
                    Shape::POINTER
                } else {
                    self.inline_shape(&data)?.unwrap_or(Shape::POINTER)
                }
            }
            Monotype::Function(..)
            | Monotype::Effect(_)
            | Monotype::Reference(_)
            | Monotype::MutableArray(_)
            | Monotype::Object(_)
            | Monotype::Nullable(_)
            | Monotype::Regex
            | Monotype::Mutex
            | Monotype::BigInt
            | Monotype::Lazy(_)
            | Monotype::Recursive(_) => Shape::POINTER,
        })
    }
}

/// The constructors with fields, grouped by the types of their fields, in
/// order of first appearance.
fn groups_of_equal_fields(constructors: &[DataConstructor]) -> Vec<Vec<usize>> {
    let mut groups: Vec<Vec<usize>> = vec![];
    for (index, constructor) in constructors.iter().enumerate() {
        if constructor.fields.is_empty() {
            continue;
        }
        let same =
            groups.iter_mut().find(|group| constructors[group[0]].fields == constructor.fields);
        match same {
            Some(group) => group.push(index),
            None => groups.push(vec![index]),
        }
    }
    groups
}

/// The names of the slots, each constructor's and every slot's once.
struct NamedSlots {
    constructors: Vec<Vec<String>>,
    fields: Vec<(String, MonotypeId)>,
}

impl NamedSlots {
    /// A constructor with slots of its own names them after itself, `Val0`;
    /// constructors that share slots name them after the position, `Field0`.
    fn new(constructors: &[DataConstructor], groups: &[Vec<usize>]) -> NamedSlots {
        let shared_groups = groups.iter().filter(|group| group.len() > 1).count();
        let mut named =
            NamedSlots { constructors: vec![vec![]; constructors.len()], fields: vec![] };
        let mut shared_index = 0;
        for group in groups {
            let first = &constructors[group[0]];
            let prefix = if group.len() > 1 {
                shared_index += 1;
                shared_prefix(shared_index, shared_groups)
            } else {
                identifier(&first.name)
            };
            let names: Vec<String> =
                (0..first.fields.len()).map(|position| format!("{prefix}{position}")).collect();
            for &constructor in group {
                named.constructors[constructor] = names.clone();
            }
            named.fields.extend(names.into_iter().zip(first.fields.iter().copied()));
        }
        named
    }

    fn are_distinct(&self) -> bool {
        let mut seen = FxHashSet::default();
        self.fields.iter().all(|(name, _)| seen.insert(name.as_str()))
    }
}

/// The prefix of the slots that several constructors share: `Field`, or
/// `FieldA`, `FieldB` when a type has more than one set of shared slots.
fn shared_prefix(index: usize, count: usize) -> String {
    if count == 1 {
        return "Field".into();
    }
    let mut letters = String::new();
    let mut remaining = index;
    while remaining > 0 {
        remaining -= 1;
        letters.insert(0, (b'A' + (remaining % 26) as u8) as char);
        remaining /= 26;
    }
    format!("Field{letters}")
}
