//! A value of a data type that reaches a `Foreign` is, in JavaScript, an object whose fields are
//! the active constructor's arguments, `value0`, `value1` and so on: `JSON.stringify(Just 1)` is
//! `{"value0":1}`. go-support's foreignvalue reads such a value without reflection through a
//! function the program registers for each data type it turns into a `Foreign`:
//!
//! ```go
//! var maybeForeignFields = foreignvalue.DataFields(func(value *maybe.Maybe) []any {
//!     if value.Tag == maybe.TagJust {
//!         return []any{value.Just}
//!     }
//!     return nil
//! })
//! ```
//!
//! Each field is itself turned into a `Foreign`, as a record's or an array's would be.

use super::maybe::MaybeLayout;
use super::{Emitter, call, identifier_expression};
use crate::error::GoResult;
use crate::foreign::{GoFunction, GoPackage};
use crate::monotype::{DataType, Monotype, MonotypeId};
use crate::syntax::{GoDeclaration, GoExpression, GoStatement, GoType};

impl<'q, Q> Emitter<'_, '_, 'q, Q>
where
    Q: checking::ExternalQueries,
{
    /// Notes that a value of `canonical`, a data type at its erased arguments, may reach a
    /// `Foreign`.
    pub(super) fn note_foreign_data(&mut self, canonical: MonotypeId) {
        if let Monotype::Data(_) | Monotype::Recursive(_) = self.monotypes.get(canonical)
            && !self.foreign_data.contains(&canonical)
        {
            self.foreign_data.push(canonical);
        }
    }

    /// The registrations of the data types whose values may reach a `Foreign`, for a program
    /// that reads Foreign values. Registering one may note the data types of its fields.
    pub(super) fn foreign_data_registrations(&mut self) -> GoResult<Vec<GoDeclaration>> {
        let mut registrations = vec![];
        if !self.imports.contains(GoPackage::ForeignValue.path()) {
            return Ok(registrations);
        }
        let mut registered = std::collections::BTreeSet::new();
        let mut next = 0;
        while let Some(&monotype) = self.foreign_data.get(next) {
            next += 1;
            let (Monotype::Data(data) | Monotype::Recursive(data)) =
                self.monotypes.get(monotype).clone()
            else {
                continue;
            };
            if let Some(registration) = self.foreign_data_registration(&data)? {
                if registered.insert(registration.name().unwrap_or_default().to_string()) {
                    self.note_homes(std::slice::from_ref(&registration), Some(data.file_id));
                    registrations.push(registration);
                }
            }
        }
        Ok(registrations)
    }

    fn foreign_data_registration(&mut self, data: &DataType) -> GoResult<Option<GoDeclaration>> {
        let layout = self.data_layout(data)?;
        // A Maybe held as a pointer to its payload has no Go type of its own to recognise.
        if let Some(MaybeLayout::Pointer { .. }) = layout.maybe {
            return Ok(None);
        }
        self.locals.clear();
        self.local_names.clear();
        let value_type = self.layout_type(&layout)?;
        let value = identifier_expression("value");
        self.local_names.insert("value".into());
        let opaque = self.monotypes.intern(Monotype::Opaque);
        let mut body = vec![];
        let last = layout.constructors.len().saturating_sub(1);
        for (index, constructor) in layout.constructors.iter().enumerate() {
            let mut branch = vec![];
            let mut fields = Vec::with_capacity(constructor.fields.len());
            for position in 0..constructor.fields.len() {
                let read = self.constructor_field(&layout, index, position, value.clone());
                let field_type = constructor.fields[position].1;
                fields.push((None, self.coerce(read, field_type, opaque, &mut branch)?));
            }
            let fields = if fields.is_empty() {
                identifier_expression("nil")
            } else {
                GoExpression::Composite { type_: GoType::Slice(Box::new(GoType::Any)), fields }
            };
            branch.push(GoStatement::Return(Some(fields)));
            match self.constructor_test(&layout, index, value.clone()) {
                Some(test) if index < last => body.push(GoStatement::If {
                    condition: test,
                    then: branch,
                    otherwise: vec![],
                }),
                _ => {
                    body.extend(branch);
                    break;
                }
            }
        }
        let register = self
            .go_function(GoFunction { package: GoPackage::ForeignValue, name: "DataFields" });
        let fields = GoExpression::Function {
            parameters: vec![("value".into(), value_type)],
            result: Some(GoType::Slice(Box::new(GoType::Any))),
            body,
        };
        let name = self.global_name(crate::emit::packages::Spelling::derived(
            "",
            layout.name.clone(),
            "ForeignFields",
        ));
        let value = call(register, vec![fields]);
        Ok(Some(GoDeclaration::Variable { name, type_: None, value, line: None }))
    }
}
