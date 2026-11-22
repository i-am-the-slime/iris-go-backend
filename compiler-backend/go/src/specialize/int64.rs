//! purescript-int64's Longs at the signedness each definition fixes.
//!
//! `Data.Int64.Internal` wraps one foreign `Long` in `Long' s`, whose phantom
//! says whether it is an `Int64` or a `UInt64`, and its foreigns take bare
//! Longs. Every definition is specialised at closed types, so the types of
//! one specialisation name its Longs' signedness: `quot` at `s = Signed`,
//! the `Semiring (Long' Unsigned)` instance, `Show Int64`. Its bare Longs are
//! then spelled `Long' Signed` or `Long' Unsigned`, the Go `int64` or
//! `uint64`, and its foreigns are Go's operators on that type. A definition
//! whose types mention only bare Longs (`safeReadLong`) takes the signedness
//! of the definition that uses it, and is specialised once for each.

use checking::TypeId;
use checking::core::Type;
use files::FileId;
use indexing::TypeItemId;
use rustc_hash::FxHashMap;
use smol_str::{SmolStr, format_smolstr};

use super::{Scope, Specializer};
use crate::error::GoResult;
use crate::monomorphic::{Expression, ExpressionKind};
use crate::monotype::{LongMentions, MonotypeId, long_mentions};
use crate::primitives::{Int64Operation, KnownType, Signedness};

#[derive(Default)]
pub(super) struct Int64Types {
    /// Looked up once: `Long` and `Long' Signed` and `Long' Unsigned`, when
    /// the program has `Data.Int64.Internal`.
    spelling: Option<Option<Spelling>>,
    spelled: FxHashMap<(TypeId, Signedness), TypeId>,
}

#[derive(Clone, Copy)]
struct Spelling {
    long: (FileId, TypeItemId),
    signed: TypeId,
    unsigned: TypeId,
}

/// A definition specialised at the signedness of its user, as `safeReadLong`
/// is, is named for it: `safeReadLongInt64`.
pub(super) fn inherited_name(name: SmolStr, inherited: Option<Signedness>) -> SmolStr {
    match inherited {
        Some(Signedness::Signed) => format_smolstr!("{name}Int64"),
        Some(Signedness::Unsigned) => format_smolstr!("{name}UInt64"),
        None => name,
    }
}

impl<'q, Q> Specializer<'q, Q>
where
    Q: checking::ExternalQueries,
{
    /// The signedness of a definition's Longs at these types, and whether it
    /// is the user's, which only bare Longs leave it to.
    pub(super) fn key_signedness(
        &mut self,
        scope: &Scope,
        types: &[TypeId],
        instance_types: &[TypeId],
        declared: Option<TypeId>,
    ) -> GoResult<(Option<Signedness>, bool)> {
        if self.int64_spelling()?.is_none() {
            return Ok((None, false));
        }
        let mut mentions = LongMentions::default();
        for &type_id in types.iter().chain(instance_types).chain(declared.as_ref()) {
            long_mentions(&mut self.context, type_id, &mut mentions)?;
        }
        if let Some(signedness) = mentions.signedness() {
            return Ok((Some(signedness), false));
        }
        if mentions.bare && !(mentions.signed && mentions.unsigned) {
            return Ok((scope.signedness, scope.signedness.is_some()));
        }
        Ok((None, false))
    }

    /// The type with its bare Longs spelled at the definition's signedness.
    pub(super) fn spelled_longs(
        &mut self,
        type_id: TypeId,
        signedness: Signedness,
    ) -> GoResult<TypeId> {
        let Some(spelling) = self.int64_spelling()? else { return Ok(type_id) };
        if let Some(&spelled) = self.int64.spelled.get(&(type_id, signedness)) {
            return Ok(spelled);
        }
        let signed_long = match signedness {
            Signedness::Signed => spelling.signed,
            Signedness::Unsigned => spelling.unsigned,
        };
        let spelled =
            crate::monotype::spell_longs(&mut self.context, type_id, signed_long, spelling.long);
        self.int64.spelled.insert((type_id, signedness), spelled);
        Ok(spelled)
    }

    fn int64_spelling(&mut self) -> GoResult<Option<Spelling>> {
        if let Some(spelling) = self.int64.spelling {
            return Ok(spelling);
        }
        let spelling = self.find_int64_spelling()?;
        self.int64.spelling = Some(spelling);
        Ok(spelling)
    }

    fn find_int64_spelling(&mut self) -> GoResult<Option<Spelling>> {
        let Some(file_id) = self.context.queries.module_file("Data.Int64.Internal") else {
            return Ok(None);
        };
        let module = self.context.module(file_id)?;
        let mut items = FxHashMap::default();
        for (item, indexed) in module.indexed.items.iter_types() {
            if let Some(name) = indexed.name.as_deref()
                && let Some(known) = crate::primitives::known_type(&module.name, name)
            {
                items.insert(known, item);
            }
        }
        let (Some(&long), Some(&signed_long), Some(&signed), Some(&unsigned)) = (
            items.get(&KnownType::Long),
            items.get(&KnownType::SignedLong),
            items.get(&KnownType::Signed),
            items.get(&KnownType::Unsigned),
        ) else {
            return Ok(None);
        };
        let queries = self.context.queries;
        let applied = |phantom| {
            let head = queries.intern_type(Type::Constructor(file_id, signed_long));
            let phantom = queries.intern_type(Type::Constructor(file_id, phantom));
            queries.intern_type(Type::Application(head, phantom))
        };
        Ok(Some(Spelling {
            long: (file_id, long),
            signed: applied(signed),
            unsigned: applied(unsigned),
        }))
    }

    /// `signedToUnsigned` and `unsignedToSigned`: Go's conversion between the two.
    pub(super) fn int64_conversion(&mut self, monotype: MonotypeId) -> Option<Expression> {
        let (argument, result) = self.monotypes.function_parts(monotype)?;
        let signedness = match self.monotypes.get(result) {
            crate::monotype::Monotype::Int64 => Signedness::Signed,
            crate::monotype::Monotype::UInt64 => Signedness::Unsigned,
            _ => return None,
        };
        let parameter = self.fresh_local(self.monotypes.value_name(argument), argument);
        let foreign =
            crate::foreign::Foreign::Int64 { operation: Int64Operation::Convert, signedness };
        let kind = ExpressionKind::Foreign {
            foreign: foreign.interned(),
            arguments: vec![parameter.expression()],
        };
        Some(self.lambda(vec![parameter], Expression::new(kind, result)))
    }
}
