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

use super::Emitter;
use crate::error::GoResult;
use crate::monotype::{DataConstructor, DataType, Failure, Monotype, MonotypeId, Monotypes};
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
    pub(super) fn declaration_rank(self) -> (u8, std::cmp::Reverse<usize>) {
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
        let mut groups = groups_of_equal_fields(constructors, self.monotypes);
        let mut named = NamedSlots::new(constructors, &groups, Naming::Readable);
        if !named.are_distinct(constructors.len()) {
            // A constructor named like another's field or the tag, such as
            // `Tag`, numbers its fields after itself.
            named = NamedSlots::new(constructors, &groups, Naming::Positional);
        }
        if !named.are_distinct(constructors.len()) {
            // A constructor named like a shared slot, such as `Field`, keeps its own slots.
            groups = (0..constructors.len()).map(|index| vec![index]).collect();
            named = NamedSlots::new(constructors, &groups, Naming::Positional);
        }
        if !named.are_distinct(constructors.len()) {
            // Labels with one Go spelling, such as a Variant's `a` and `A`, number their slots.
            named.number_repeats(constructors.len());
        }
        self.arrange_slots(constructors.len(), named.constructors, named.fields)
    }

    /// Plans the struct of a `Sentinel` type, which has one constructor with fields and no tag.
    pub(super) fn plan_untagged_slots(
        &mut self,
        constructors: &[DataConstructor],
    ) -> GoResult<SlotPlan> {
        let plan = self.plan_slots(constructors)?;
        let fields = plan
            .slots
            .into_iter()
            .filter_map(|slot| match slot {
                Slot::Tag => None,
                Slot::Field { name, monotype } => Some((name, monotype)),
            })
            .collect();
        self.arrange_slots(1, plan.constructors, fields)
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
        let maybe = match self.maybe_payload(data)? {
            Some(payload) => Some(self.maybe_representation(payload)?),
            None => None,
        };
        let constructors = self
            .monotypes
            .constructors(&mut self.context, data)
            .map_err(Failure::in_code_generation)?;
        let erases_arguments = self.erases_arguments(data)?;
        let shape = if let Some(shape) = maybe.and_then(maybe_shape) {
            Some(shape)
        } else if erases_arguments || self.contains_itself(data)? {
            None
        } else if constructors.iter().all(|constructor| constructor.fields.is_empty()) {
            Some(tag_shape(constructors.len()))
        } else {
            Some(self.plan_slots(&constructors)?.shape)
        };
        self.inline_shapes.insert(data.clone(), shape);
        Ok(shape)
    }

    /// The data types held by value, through records and other data, in a
    /// field of a recursive data type or in an array's elements: copying the
    /// cell or the array copies them. Computed before any layout, since
    /// whether a type is boxed depends on it.
    pub(super) fn data_copied_by_containers(&mut self) -> GoResult<FxHashSet<DataType>> {
        let mut pending = vec![];
        for monotype in self.monotypes.ids() {
            match self.monotypes.get(monotype).clone() {
                Monotype::Array(element) | Monotype::MutableArray(element) => pending.push(element),
                Monotype::Data(data) if self.contains_itself(&data)? => {
                    pending.extend(self.constructor_fields(&data)?)
                }
                _ => {}
            }
        }
        let mut copied = FxHashSet::default();
        while let Some(monotype) = pending.pop() {
            match self.monotypes.get(monotype).clone() {
                Monotype::Data(data) if copied.insert(data.clone()) => {
                    pending.extend(self.constructor_fields(&data)?)
                }
                Monotype::Record(fields) => {
                    pending.extend(fields.iter().map(|field| field.monotype))
                }
                _ => {}
            }
        }
        Ok(copied)
    }

    pub(super) fn value_shape(&mut self, monotype: MonotypeId) -> GoResult<Shape> {
        Ok(match self.monotypes.get(monotype).clone() {
            Monotype::Unit => Shape::scalar(0),
            Monotype::Boolean => Shape::scalar(1),
            Monotype::Int | Monotype::Char => Shape::scalar(4),
            Monotype::Number | Monotype::Int64 | Monotype::UInt64 => Shape::scalar(8),
            // A foreign type's size is the foreign package's choice; it is
            // counted as an interface value.
            Monotype::String
            | Monotype::Erased(_)
            | Monotype::Opaque
            | Monotype::ForeignData(_) => Shape::words(2),
            Monotype::Error => Shape::words(4),
            Monotype::Array(_) => Shape::words(3),
            Monotype::Record(fields) => {
                let mut shapes = vec![];
                for field in fields.iter() {
                    shapes.push(self.value_shape(field.monotype)?);
                }
                shapes.sort_by_key(|shape| shape.declaration_rank());
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
            | Monotype::ConsList(_)
            | Monotype::Recursive(_) => Shape::POINTER,
        })
    }
}

fn maybe_shape(representation: super::maybe::Representation) -> Option<Shape> {
    use super::maybe::Representation;
    match representation {
        Representation::Int | Representation::Char => Some(Shape::scalar(8)),
        Representation::Boolean => Some(Shape::scalar(1)),
        Representation::Pointer => Some(Shape::POINTER),
        Representation::Struct => None,
    }
}

/// The constructors with fields, grouped by the types of their fields, in
/// order of first appearance.
fn groups_of_equal_fields(
    constructors: &[DataConstructor],
    monotypes: &Monotypes,
) -> Vec<Vec<usize>> {
    let mut groups: Vec<Vec<usize>> = vec![];
    for (index, constructor) in constructors.iter().enumerate() {
        if constructor.fields.is_empty() {
            continue;
        }
        let equal_fields = |fields: &[MonotypeId]| {
            fields.len() == constructor.fields.len()
                && fields
                    .iter()
                    .zip(constructor.fields.iter())
                    .all(|(&field, &other)| monotypes.same_without_causes(field, other))
        };
        let same = groups.iter_mut().find(|group| equal_fields(&constructors[group[0]].fields));
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

/// How the slots a constructor keeps to itself are named.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Naming {
    /// After the constructor when it has one field, `Just`; by ordinal when
    /// the type has one constructor, `First`, `Second`; else by position.
    Readable,
    /// After the constructor and the position, `Cons0`, `Cons1`.
    Positional,
}

/// Field names a data type's struct declares beside its constructors' slots.
const RESERVED_SLOTS: &[&str] = &["Tag", "Origin"];

const ORDINALS: &[&str] = &[
    "First", "Second", "Third", "Fourth", "Fifth", "Sixth", "Seventh", "Eighth", "Ninth", "Tenth",
    "Eleventh", "Twelfth",
];

impl NamedSlots {
    /// A constructor with slots of its own names them after itself;
    /// constructors that share slots name them after the position, `Field0`.
    fn new(constructors: &[DataConstructor], groups: &[Vec<usize>], naming: Naming) -> NamedSlots {
        let shared_groups = groups.iter().filter(|group| group.len() > 1).count();
        let mut named =
            NamedSlots { constructors: vec![vec![]; constructors.len()], fields: vec![] };
        let mut shared_index = 0;
        for group in groups {
            let first = &constructors[group[0]];
            let names: Vec<String> = if group.len() > 1 {
                shared_index += 1;
                let prefix = shared_prefix(shared_index, shared_groups);
                (0..first.fields.len()).map(|position| format!("{prefix}{position}")).collect()
            } else {
                own_slots(first, constructors.len(), naming)
            };
            for &constructor in group {
                named.constructors[constructor] = names.clone();
            }
            named.fields.extend(names.into_iter().zip(first.fields.iter().copied()));
        }
        named
    }

    /// Gives each slot that repeats an earlier slot's name, or a name the struct declares
    /// besides, the lowest number that is free. Every constructor keeps slots of its own.
    fn number_repeats(&mut self, constructors: usize) {
        let mut taken: FxHashSet<String> = RESERVED_SLOTS
            .iter()
            .filter(|&&name| name != "Tag" || constructors > 1)
            .map(|name| name.to_string())
            .collect();
        let mut field = 0;
        for slots in &mut self.constructors {
            for slot in slots.iter_mut() {
                if taken.contains(slot.as_str()) {
                    *slot = crate::naming::numbered(slot, |name| taken.contains(name));
                }
                taken.insert(slot.clone());
                self.fields[field].0 = slot.clone();
                field += 1;
            }
        }
    }

    /// Whether no two slots share a name, nor a slot a name the struct
    /// declares besides, such as the tag of a type of several constructors.
    fn are_distinct(&self, constructors: usize) -> bool {
        let mut seen = FxHashSet::default();
        let reserved =
            |name: &str| RESERVED_SLOTS.contains(&name) && (name != "Tag" || constructors > 1);
        self.fields.iter().all(|(name, _)| !reserved(name) && seen.insert(name.as_str()))
    }
}

/// The slots of a constructor that shares them with no other.
fn own_slots(constructor: &DataConstructor, constructors: usize, naming: Naming) -> Vec<String> {
    let name = crate::naming::go_field(&constructor.name);
    let count = constructor.fields.len();
    match naming {
        Naming::Readable if count == 1 => vec![name],
        Naming::Readable if constructors == 1 && count <= ORDINALS.len() => {
            ORDINALS[..count].iter().map(|ordinal| ordinal.to_string()).collect()
        }
        _ => (0..count).map(|position| format!("{name}{position}")).collect(),
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
