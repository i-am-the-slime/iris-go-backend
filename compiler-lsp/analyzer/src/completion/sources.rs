use async_lsp::lsp_types::*;
use checking::ExternalQueries;
use checking::core::pretty::Pretty;
use checking::core::{Type, TypeId};
use files::FileId;
use indexing::{ImportKind, TermItemId, TypeItemId};
use lowering::LoweredModule;
use lowering::scope::{GraphNode, GraphNodeId};
use resolving::ResolvedModule;
use rowan::ast::{AstNode, AstPtr};
use smol_str::SmolStr;
use syntax::cst;

use crate::AnalyzerError;

use super::edit;
use super::filter::PerfectSegmentFuzzy;
use super::item::CompletionItemSpec;
use super::prelude::*;
use super::resolve::CompletionResolveData;

/// Yields the qualified names of imports.
///
/// For example:
/// ```purescript
/// import Halogen as H
/// import Halogen.HTML as HH
///
/// -- candidates -> [H, HH]
/// ```
pub struct QualifiedModules;

impl CompletionSource for QualifiedModules {
    type T = ();

    fn collect_into<F: Filter>(
        &self,
        context: &Context,
        filter: F,
        items: &mut Vec<CompletionItem>,
    ) -> Result<Self::T, AnalyzerError> {
        let source = context.resolved.qualified.iter();
        let source = source.filter(move |(name, _)| filter.matches(name));

        for (name, imports) in source {
            let Some(import) = imports.first() else { continue };
            let (parsed, _) = context.engine.parsed(import.file)?;
            let description = parsed.module_name().map(|name| name.to_string());

            let mut item = CompletionItemSpec::new(
                name.to_string(),
                context.range,
                CompletionItemKind::MODULE,
                CompletionResolveData::Import(import.file),
            );

            if let Some(description) = description {
                item.label_description(description);
            }

            items.push(item.build());
        }

        Ok(())
    }
}

/// Yields terms defined in the current module.
pub struct LocalTerms;

impl CompletionSource for LocalTerms {
    type T = ();

    fn collect_into<F: Filter>(
        &self,
        context: &Context,
        filter: F,
        items: &mut Vec<CompletionItem>,
    ) -> Result<Self::T, AnalyzerError> {
        let source = context.resolved.locals.iter_terms();
        let source = source.filter(move |(name, _, _)| filter.matches(name));

        for (name, file_id, term_id) in source {
            let mut item = CompletionItemSpec::new(
                name.to_string(),
                context.range,
                CompletionItemKind::VALUE,
                CompletionResolveData::TermItem(file_id, term_id),
            );

            item.label_description("Local".to_string());
            context.apply_type_sort(&mut item, file_id, term_id);

            items.push(item.build())
        }

        Ok(())
    }
}

/// Yields types defined in the current module.
pub struct LocalTypes;

impl CompletionSource for LocalTypes {
    type T = ();

    fn collect_into<F: Filter>(
        &self,
        context: &Context,
        filter: F,
        items: &mut Vec<CompletionItem>,
    ) -> Result<Self::T, AnalyzerError> {
        let source = context.resolved.locals.iter_types();
        let source = source.filter(move |(name, _, _)| filter.matches(name));

        for (name, file_id, type_id) in source {
            let mut item = CompletionItemSpec::new(
                name.to_string(),
                context.range,
                CompletionItemKind::STRUCT,
                CompletionResolveData::TypeItem(file_id, type_id),
            );

            item.label_description("Local".to_string());

            items.push(item.build())
        }

        let source = context.resolved.locals.iter_classes();
        let source = source.filter(move |(name, _, _)| filter.matches(name));

        for (name, file_id, type_id) in source {
            let mut item = CompletionItemSpec::new(
                name.to_string(),
                context.range,
                CompletionItemKind::STRUCT,
                CompletionResolveData::TypeItem(file_id, type_id),
            );

            item.label_description("Local".to_string());

            items.push(item.build())
        }

        Ok(())
    }
}

/// Yields terms from unqualified imports.
pub struct ImportedTerms;

impl CompletionSource for ImportedTerms {
    type T = ();

    fn collect_into<F: Filter>(
        &self,
        context: &Context,
        filter: F,
        items: &mut Vec<CompletionItem>,
    ) -> Result<Self::T, AnalyzerError> {
        let source = context.resolved.unqualified.values().flatten();

        for import in source {
            let source = import.iter_terms().filter(move |(name, _, _, kind)| {
                filter.matches(name) && !matches!(kind, ImportKind::Hidden)
            });

            for (name, file_id, term_id, _) in source {
                let (parsed, _) = context.engine.parsed(file_id)?;
                let description = parsed.module_name().map(|name| name.to_string());

                let mut item = CompletionItemSpec::new(
                    name.to_string(),
                    context.range,
                    CompletionItemKind::VALUE,
                    CompletionResolveData::TermItem(file_id, term_id),
                );

                if let Some(description) = description {
                    item.label_description(description);
                }
                context.apply_type_sort(&mut item, file_id, term_id);

                items.push(item.build())
            }
        }

        Ok(())
    }
}

/// Yields types from unqualified imports.
pub struct ImportedTypes;

impl CompletionSource for ImportedTypes {
    type T = ();

    fn collect_into<F: Filter>(
        &self,
        context: &Context,
        filter: F,
        items: &mut Vec<CompletionItem>,
    ) -> Result<Self::T, AnalyzerError> {
        let source = context.resolved.unqualified.values().flatten();

        for import in source {
            let source = import.iter_types().filter(move |(name, _, _, kind)| {
                filter.matches(name) && !matches!(kind, ImportKind::Hidden)
            });
            for (name, f, t, _) in source {
                let (parsed, _) = context.engine.parsed(f)?;
                let description = parsed.module_name().map(|name| name.to_string());

                let mut item = CompletionItemSpec::new(
                    name.to_string(),
                    context.range,
                    CompletionItemKind::STRUCT,
                    CompletionResolveData::TypeItem(f, t),
                );

                if let Some(description) = description {
                    item.label_description(description);
                }

                items.push(item.build())
            }

            let source = import.iter_classes().filter(move |(name, _, _, kind)| {
                filter.matches(name) && !matches!(kind, ImportKind::Hidden)
            });
            for (name, f, t, _) in source {
                let (parsed, _) = context.engine.parsed(f)?;
                let description = parsed.module_name().map(|name| name.to_string());

                let mut item = CompletionItemSpec::new(
                    name.to_string(),
                    context.range,
                    CompletionItemKind::STRUCT,
                    CompletionResolveData::TypeItem(f, t),
                );

                if let Some(description) = description {
                    item.label_description(description);
                }

                items.push(item.build())
            }
        }

        Ok(())
    }
}

/// Yields terms from qualified imports.
pub struct QualifiedTerms<'a>(pub &'a str);

impl CompletionSource for QualifiedTerms<'_> {
    type T = ();

    fn collect_into<F: Filter>(
        &self,
        context: &Context,
        filter: F,
        items: &mut Vec<CompletionItem>,
    ) -> Result<Self::T, AnalyzerError> {
        let Some(imports) = context.resolved.qualified.get(self.0) else {
            return Ok(());
        };

        for import in imports {
            let source = import.iter_terms().filter(|(name, _, _, kind)| {
                filter.matches(name) && !matches!(kind, ImportKind::Hidden)
            });

            for (name, file_id, term_id, _) in source {
                let (parsed, _) = context.engine.parsed(file_id)?;
                let description = parsed.module_name().map(|name| name.to_string());

                let mut item = CompletionItemSpec::new(
                    name.to_string(),
                    context.range,
                    CompletionItemKind::VALUE,
                    CompletionResolveData::TermItem(file_id, term_id),
                );

                item.edit_text(format!("{}.{name}", self.0));
                if let Some(description) = description {
                    item.label_description(description);
                }
                context.apply_type_sort(&mut item, file_id, term_id);

                items.push(item.build())
            }
        }

        Ok(())
    }
}

/// Yields types from qualified imports.
pub struct QualifiedTypes<'a>(pub &'a str);

impl CompletionSource for QualifiedTypes<'_> {
    type T = ();

    fn collect_into<F: Filter>(
        &self,
        context: &Context,
        filter: F,
        items: &mut Vec<CompletionItem>,
    ) -> Result<Self::T, AnalyzerError> {
        let Some(imports) = context.resolved.qualified.get(self.0) else {
            return Ok(());
        };

        for import in imports {
            let source = import.iter_types().filter(|(name, _, _, kind)| {
                filter.matches(name) && !matches!(kind, ImportKind::Hidden)
            });

            for (name, file_id, type_id, _) in source {
                let (parsed, _) = context.engine.parsed(file_id)?;
                let description = parsed.module_name().map(|name| name.to_string());

                let mut item = CompletionItemSpec::new(
                    name.to_string(),
                    context.range,
                    CompletionItemKind::STRUCT,
                    CompletionResolveData::TypeItem(file_id, type_id),
                );

                item.edit_text(format!("{}.{name}", self.0));
                if let Some(description) = description {
                    item.label_description(description);
                }

                items.push(item.build())
            }

            let source = import.iter_classes().filter(|(name, _, _, kind)| {
                filter.matches(name) && !matches!(kind, ImportKind::Hidden)
            });

            for (name, file_id, type_id, _) in source {
                let (parsed, _) = context.engine.parsed(file_id)?;
                let description = parsed.module_name().map(|name| name.to_string());

                let mut item = CompletionItemSpec::new(
                    name.to_string(),
                    context.range,
                    CompletionItemKind::STRUCT,
                    CompletionResolveData::TypeItem(file_id, type_id),
                );

                item.edit_text(format!("{}.{name}", self.0));
                if let Some(description) = description {
                    item.label_description(description);
                }

                items.push(item.build())
            }
        }

        Ok(())
    }
}

/// Yields suggestions for terms.
pub struct SuggestedTerms;

/// Yields suggestions for types.
pub struct SuggestedTypes;

trait SuggestionsHelper {
    type ItemId;

    fn exports(resolved: &ResolvedModule)
    -> impl Iterator<Item = (&SmolStr, FileId, Self::ItemId)>;

    fn candidate(
        &self,
        context: &Context,
        name: &SmolStr,
        import_id: FileId,
        file_id: FileId,
        item_id: Self::ItemId,
    ) -> Result<Option<CompletionItem>, AnalyzerError>;
}

impl SuggestionsHelper for SuggestedTerms {
    type ItemId = TermItemId;

    fn exports(resolved: &ResolvedModule) -> impl Iterator<Item = (&SmolStr, FileId, TermItemId)> {
        resolved.exports.iter_terms()
    }

    fn candidate(
        &self,
        context: &Context,
        name: &SmolStr,
        import_id: FileId,
        file_id: FileId,
        item_id: Self::ItemId,
    ) -> Result<Option<CompletionItem>, AnalyzerError> {
        assert_eq!(import_id, file_id);

        if context.has_term_import(None, name) {
            return Ok(None);
        }

        let (parsed, _) = context.engine.parsed(file_id)?;
        let Some(module_name) = parsed.module_name() else {
            return Ok(None);
        };

        let mut item = CompletionItemSpec::new(
            name.to_string(),
            context.range,
            CompletionItemKind::VALUE,
            CompletionResolveData::TermItem(file_id, item_id),
        );

        let (import_text, import_range) =
            edit::term_import_item(context, &module_name, name, file_id, item_id);

        let range_new_text =
            import_range.or_else(|| context.insert_import_range()).zip(import_text);

        item.label_detail(format!(" (import {module_name})"));
        item.label_description(format!("{module_name}"));
        item.sort_text(format!("{module_name}.{name}"));
        context.apply_type_sort(&mut item, file_id, item_id);

        if let Some((range, new_text)) = range_new_text {
            item.additional_text_edits(vec![TextEdit { range, new_text }]);
        }

        Ok(Some(item.build()))
    }
}

impl SuggestionsHelper for SuggestedTypes {
    type ItemId = TypeItemId;

    fn exports(
        resolved: &ResolvedModule,
    ) -> impl Iterator<Item = (&SmolStr, FileId, Self::ItemId)> {
        resolved.exports.iter_types().chain(resolved.exports.iter_classes())
    }

    fn candidate(
        &self,
        context: &Context,
        name: &SmolStr,
        import_id: FileId,
        file_id: FileId,
        item_id: Self::ItemId,
    ) -> Result<Option<CompletionItem>, AnalyzerError> {
        assert_eq!(import_id, file_id);

        if context.has_type_import(None, name) {
            return Ok(None);
        }

        let (parsed, _) = context.engine.parsed(file_id)?;
        let Some(module_name) = parsed.module_name() else {
            return Ok(None);
        };

        let mut item = CompletionItemSpec::new(
            name.to_string(),
            context.range,
            CompletionItemKind::STRUCT,
            CompletionResolveData::TypeItem(file_id, item_id),
        );

        let (import_text, import_range) =
            edit::type_import_item(context, &module_name, name, file_id, item_id);

        let range_new_text =
            import_range.or_else(|| context.insert_import_range()).zip(import_text);

        item.label_detail(format!(" (import {module_name})"));
        item.label_description(format!("{module_name}"));
        item.sort_text(format!("{module_name}.{name}"));

        if let Some((range, new_text)) = range_new_text {
            item.additional_text_edits(vec![TextEdit { range, new_text }]);
        }

        Ok(Some(item.build()))
    }
}

fn suggestions_candidates<T: SuggestionsHelper>(
    this: &T,
    context: &Context,
    filter: impl Filter,
    items: &mut Vec<CompletionItem>,
) -> Result<(), AnalyzerError> {
    let has_prim = context
        .resolved
        .unqualified
        .values()
        .flatten()
        .any(|import| import.file == context.prim_id);

    let file_ids = context.files.iter_id().filter(move |&id| {
        let not_self = id != context.current_file;
        let not_prim = id != context.prim_id;
        not_self && (not_prim || has_prim)
    });

    for import_id in file_ids {
        let resolved = context.engine.resolved(import_id)?;

        let source = T::exports(&resolved)
            .filter(|(name, file_id, _)| filter.matches(name) && *file_id == import_id);

        for (name, file_id, item_id) in source {
            if let Some(item) = this.candidate(context, name, import_id, file_id, item_id)? {
                items.push(item);
            }
        }
    }

    Ok(())
}

impl CompletionSource for SuggestedTerms {
    type T = ();

    fn collect_into<F: Filter>(
        &self,
        context: &Context,
        filter: F,
        items: &mut Vec<CompletionItem>,
    ) -> Result<Self::T, AnalyzerError> {
        suggestions_candidates(self, context, filter, items)
    }
}

impl CompletionSource for SuggestedTypes {
    type T = ();

    fn collect_into<F: Filter>(
        &self,
        context: &Context,
        filter: F,
        items: &mut Vec<CompletionItem>,
    ) -> Result<Self::T, AnalyzerError> {
        suggestions_candidates(self, context, filter, items)
    }
}

/// Yields terms for implicit Prim.
pub struct PrimTerms;

impl CompletionSource for PrimTerms {
    type T = ();

    fn collect_into<F: Filter>(
        &self,
        context: &Context,
        filter: F,
        items: &mut Vec<CompletionItem>,
    ) -> Result<Self::T, AnalyzerError> {
        let source = context
            .prim_resolved
            .exports
            .iter_terms()
            .filter(move |(name, _, _)| filter.matches(name));

        for (name, file_id, term_id) in source {
            let mut item = CompletionItemSpec::new(
                name.to_string(),
                context.range,
                CompletionItemKind::VALUE,
                CompletionResolveData::TermItem(file_id, term_id),
            );

            item.label_description("Prim".to_string());
            context.apply_type_sort(&mut item, file_id, term_id);

            items.push(item.build())
        }

        Ok(())
    }
}

/// Yields types for implicit Prim.
pub struct PrimTypes;

impl CompletionSource for PrimTypes {
    type T = ();

    fn collect_into<F: Filter>(
        &self,
        context: &Context,
        filter: F,
        items: &mut Vec<CompletionItem>,
    ) -> Result<Self::T, AnalyzerError> {
        let source = context
            .prim_resolved
            .exports
            .iter_types()
            .filter(move |(name, _, _)| filter.matches(name));

        for (name, file_id, type_item) in source {
            let mut item = CompletionItemSpec::new(
                name.to_string(),
                context.range,
                CompletionItemKind::STRUCT,
                CompletionResolveData::TypeItem(file_id, type_item),
            );

            item.label_description("Prim".to_string());

            items.push(item.build())
        }

        let source = context
            .prim_resolved
            .exports
            .iter_classes()
            .filter(move |(name, _, _)| filter.matches(name));

        for (name, file_id, type_item) in source {
            let mut item = CompletionItemSpec::new(
                name.to_string(),
                context.range,
                CompletionItemKind::STRUCT,
                CompletionResolveData::TypeItem(file_id, type_item),
            );

            item.label_description("Prim".to_string());

            items.push(item.build())
        }

        Ok(())
    }
}

/// Yields suggestions for qualified terms.
pub struct QualifiedTermsSuggestions<'a>(pub &'a str);

/// Yields suggestions for qualified types.
pub struct QualifiedTypesSuggestions<'a>(pub &'a str);

impl SuggestionsHelper for QualifiedTermsSuggestions<'_> {
    type ItemId = TermItemId;

    fn exports(
        resolved: &ResolvedModule,
    ) -> impl Iterator<Item = (&SmolStr, FileId, Self::ItemId)> {
        resolved.exports.iter_terms()
    }

    fn candidate(
        &self,
        context: &Context,
        name: &SmolStr,
        import_id: FileId,
        file_id: FileId,
        item_id: Self::ItemId,
    ) -> Result<Option<CompletionItem>, AnalyzerError> {
        let (parsed, _) = context.engine.parsed(import_id)?;
        let Some(module_name) = parsed.module_name() else {
            return Ok(None);
        };

        let mut item = CompletionItemSpec::new(
            name.to_string(),
            context.range,
            CompletionItemKind::VALUE,
            CompletionResolveData::TermItem(file_id, item_id),
        );

        item.label_detail(format!(" (import {module_name} as {})", self.0));
        item.label_description(format!("{module_name}"));

        item.edit_text(format!("{}.{name}", self.0));
        item.sort_text(format!("{module_name}.{name}"));
        context.apply_type_sort(&mut item, file_id, item_id);

        if let Some(range) = context.insert_import_range() {
            let new_text = format!("import {module_name} as {}\n", self.0);
            item.additional_text_edits(vec![TextEdit { range, new_text }]);
        }

        Ok(Some(item.build()))
    }
}

impl SuggestionsHelper for QualifiedTypesSuggestions<'_> {
    type ItemId = TypeItemId;

    fn exports(
        resolved: &ResolvedModule,
    ) -> impl Iterator<Item = (&SmolStr, FileId, Self::ItemId)> {
        resolved.exports.iter_types().chain(resolved.exports.iter_classes())
    }

    fn candidate(
        &self,
        context: &Context,
        name: &SmolStr,
        import_id: FileId,
        file_id: FileId,
        item_id: Self::ItemId,
    ) -> Result<Option<CompletionItem>, AnalyzerError> {
        let (parsed, _) = context.engine.parsed(import_id)?;
        let Some(module_name) = parsed.module_name() else {
            return Ok(None);
        };

        let mut item = CompletionItemSpec::new(
            name.to_string(),
            context.range,
            CompletionItemKind::STRUCT,
            CompletionResolveData::TypeItem(file_id, item_id),
        );

        item.label_detail(format!(" (import {module_name} as {})", self.0));
        item.label_description(format!("{module_name}"));

        item.edit_text(format!("{}.{name}", self.0));
        item.sort_text(format!("{module_name}.{name}"));

        if let Some(range) = context.insert_import_range() {
            let new_text = format!("import {module_name} as {}\n", self.0);
            item.additional_text_edits(vec![TextEdit { range, new_text }]);
        }

        Ok(Some(item.build()))
    }
}

fn suggestions_candidates_qualified<T: SuggestionsHelper>(
    this: &T,
    prefix: &str,
    context: &Context,
    filter: impl Filter,
    items: &mut Vec<CompletionItem>,
) -> Result<(), AnalyzerError> {
    let has_prim =
        context.resolved.qualified.values().flatten().any(|import| import.file == context.prim_id);

    let file_ids = context.files.iter_id().filter(move |&id| {
        let not_self = id != context.current_file;
        let not_prim = id != context.prim_id;
        not_self && (not_prim || has_prim)
    });

    for import_id in file_ids {
        let (parsed, _) = context.engine.parsed(import_id)?;
        let resolved = context.engine.resolved(import_id)?;

        if parsed.module_name().is_some_and(|module_name| {
            let filter = PerfectSegmentFuzzy(&module_name);
            !filter.matches(prefix)
        }) {
            continue;
        }

        let source = T::exports(&resolved).filter(|(name, _, _)| filter.matches(name));

        for (name, file_id, item_id) in source {
            if let Some(item) = this.candidate(context, name, import_id, file_id, item_id)? {
                items.push(item);
            }
        }
    }

    Ok(())
}

impl CompletionSource for QualifiedTermsSuggestions<'_> {
    type T = ();

    fn collect_into<F: Filter>(
        &self,
        context: &Context,
        filter: F,
        items: &mut Vec<CompletionItem>,
    ) -> Result<Self::T, AnalyzerError> {
        suggestions_candidates_qualified(self, self.0, context, filter, items)
    }
}

impl CompletionSource for QualifiedTypesSuggestions<'_> {
    type T = ();

    fn collect_into<F: Filter>(
        &self,
        context: &Context,
        filter: F,
        items: &mut Vec<CompletionItem>,
    ) -> Result<Self::T, AnalyzerError> {
        suggestions_candidates_qualified(self, self.0, context, filter, items)
    }
}

/// Yields record fields for record access completion.
pub struct RecordFields<'a> {
    pub expr_ptr: &'a AstPtr<cst::Expression>,
    pub completed_labels: &'a [SmolStr],
}

impl CompletionSource for RecordFields<'_> {
    type T = ();

    fn collect_into<F: Filter>(
        &self,
        context: &Context,
        filter: F,
        items: &mut Vec<CompletionItem>,
    ) -> Result<Self::T, AnalyzerError> {
        let expr_id =
            context.stabilized.lookup_ptr(self.expr_ptr).ok_or(AnalyzerError::NonFatal)?;
        let checked = context.engine.checked(context.current_file)?;
        let type_id = checked.nodes.lookup_expression(expr_id).ok_or(AnalyzerError::NonFatal)?;

        let mut current_type = type_id;
        for label in self.completed_labels {
            let fields = extract_record_fields(context.engine, current_type)
                .ok_or(AnalyzerError::NonFatal)?;
            current_type = fields
                .iter()
                .find(|(l, _)| l == label)
                .map(|(_, t)| *t)
                .ok_or(AnalyzerError::NonFatal)?;
        }

        let fields =
            extract_record_fields(context.engine, current_type).ok_or(AnalyzerError::NonFatal)?;

        for (label, field_type) in &fields {
            if !filter.matches(label) {
                continue;
            }

            let type_str = Pretty::new(context.engine, &checked).render(*field_type);

            let mut item = CompletionItemSpec::new(
                label.to_string(),
                context.range,
                CompletionItemKind::FIELD,
                CompletionResolveData::RecordField,
            );

            item.label_detail(format!(" :: {type_str}"));
            item.label_description("Record".to_string());

            items.push(item.build());
        }

        Ok(())
    }
}

fn extract_record_fields(
    engine: &impl ExternalQueries,
    type_id: TypeId,
) -> Option<Vec<(SmolStr, TypeId)>> {
    let ty = engine.lookup_type(type_id);
    match ty {
        Type::Application(ctor, arg) => {
            if !is_prim_record(engine, ctor) {
                return None;
            }
            let row_ty = engine.lookup_type(arg);
            match row_ty {
                Type::Row(row_id) => {
                    let row = engine.lookup_row_type(row_id);
                    Some(row.fields.iter().map(|f| (f.label.clone(), f.id)).collect())
                }
                _ => None,
            }
        }
        _ => None,
    }
}

fn is_prim_record(engine: &impl ExternalQueries, type_id: TypeId) -> bool {
    let ty = engine.lookup_type(type_id);
    if let Type::Constructor(file_id, _) = ty {
        file_id == engine.prim_id()
            && engine
                .resolved(file_id)
                .ok()
                .and_then(|resolved| resolved.exports.lookup_type("Record"))
                .is_some_and(|(_, item_id)| {
                    matches!(engine.lookup_type(type_id), Type::Constructor(_, tid) if tid == item_id)
                })
    } else {
        false
    }
}

fn find_expression_scope(
    context: &Context,
    lowered: &LoweredModule,
) -> Result<GraphNodeId, AnalyzerError> {
    let offset = context.token.text_range().start();

    // Walk the CST to find the deepest Expression node covering this offset.
    let root = context.parsed.syntax_node();
    let mut node = root;

    loop {
        let child = node
            .children()
            .find(|c| c.text_range().contains_inclusive(offset));
        match child {
            Some(c) => node = c,
            None => break,
        }
    }

    // Walk up from the deepest node to find an Expression with a scope entry.
    for ancestor in node.ancestors() {
        let Some(expr) = cst::Expression::cast(ancestor) else { continue };
        let ptr = AstPtr::new(&expr);
        let Some(expr_id) = context.stabilized.lookup_ptr(&ptr) else { continue };
        if let Some(scope) = lowered.nodes.lookup_expression(expr_id) {
            return Ok(scope);
        }
    }

    Err(AnalyzerError::NonFatal)
}

/// Yields expression-local bindings (let-bound variables, function parameters, case binders).
pub struct ExpressionLocals;

impl CompletionSource for ExpressionLocals {
    type T = ();

    fn collect_into<F: Filter>(
        &self,
        context: &Context,
        filter: F,
        items: &mut Vec<CompletionItem>,
    ) -> Result<Self::T, AnalyzerError> {
        let lowered = context.engine.lowered(context.current_file)?;

        let scope_id = find_expression_scope(context, &lowered)?;

        let checked = context.engine.checked(context.current_file).ok();

        for (_, node) in lowered.graph.traverse(scope_id) {
            match node {
                GraphNode::Binder { binders, puns, .. } => {
                    for (name, binder_id) in binders {
                        if !filter.matches(name) {
                            continue;
                        }
                        let mut item = CompletionItemSpec::new(
                            name.to_string(),
                            context.range,
                            CompletionItemKind::VALUE,
                            CompletionResolveData::RecordField,
                        );
                        if let Some(type_id) =
                            checked.as_ref().and_then(|c| c.nodes.lookup_binder(*binder_id))
                        {
                            let type_str = Pretty::new(context.engine, checked.as_ref().unwrap())
                                .render(type_id);
                            item.label_detail(format!(" :: {type_str}"));
                            context.apply_type_sort_raw(&mut item, type_id);
                        }
                        item.label_description("Local".to_string());
                        items.push(item.build());
                    }
                    for (name, pun_id) in puns {
                        if !filter.matches(name) {
                            continue;
                        }
                        let mut item = CompletionItemSpec::new(
                            name.to_string(),
                            context.range,
                            CompletionItemKind::VALUE,
                            CompletionResolveData::RecordField,
                        );
                        if let Some(type_id) =
                            checked.as_ref().and_then(|c| c.nodes.puns.get(pun_id).copied())
                        {
                            let type_str = Pretty::new(context.engine, checked.as_ref().unwrap())
                                .render(type_id);
                            item.label_detail(format!(" :: {type_str}"));
                            context.apply_type_sort_raw(&mut item, type_id);
                        }
                        item.label_description("Local".to_string());
                        items.push(item.build());
                    }
                }
                GraphNode::Let { bindings, .. } => {
                    for (name, let_id) in bindings {
                        if !filter.matches(name) {
                            continue;
                        }
                        let mut item = CompletionItemSpec::new(
                            name.to_string(),
                            context.range,
                            CompletionItemKind::VALUE,
                            CompletionResolveData::RecordField,
                        );
                        if let Some(type_id) =
                            checked.as_ref().and_then(|c| c.nodes.lookup_let(*let_id))
                        {
                            let type_str = Pretty::new(context.engine, checked.as_ref().unwrap())
                                .render(type_id);
                            item.label_detail(format!(" :: {type_str}"));
                            context.apply_type_sort_raw(&mut item, type_id);
                        }
                        item.label_description("Local".to_string());
                        items.push(item.build());
                    }
                }
                _ => {}
            }
        }

        Ok(())
    }
}

/// Yields module names in the workspace.
pub struct WorkspaceModules;

impl CompletionSource for WorkspaceModules {
    type T = ();

    fn collect_into<F: Filter>(
        &self,
        context: &Context,
        filter: F,
        items: &mut Vec<CompletionItem>,
    ) -> Result<Self::T, AnalyzerError> {
        for id in context.files.iter_id() {
            let (parsed, _) = context.engine.parsed(id)?;

            let Some(module_name) = parsed.module_name() else {
                continue;
            };

            if !filter.matches(&module_name) {
                continue;
            }

            let mut item = CompletionItemSpec::new(
                module_name.to_string(),
                context.range,
                CompletionItemKind::MODULE,
                CompletionResolveData::Import(id),
            );

            item.label_description(format!("{module_name}"));

            items.push(item.build())
        }

        Ok(())
    }
}
