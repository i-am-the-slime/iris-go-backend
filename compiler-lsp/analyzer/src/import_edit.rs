use std::iter;

use async_lsp::lsp_types::Range;
use files::FileId;
use indexing::{ImportKind, IndexedModule, TermItemId, TermItemKind, TypeItemId, TypeItemKind};
use itertools::Itertools;
use parsing::ParsedModule;
use resolving::{ResolvedImport, ResolvedModule};
use rowan::ast::AstNode;
use smol_str::{SmolStrBuilder, ToSmolStr};
use stabilizing::StabilizedModule;

use crate::locate;

pub struct ImportContext<'a> {
    pub content: &'a str,
    pub stabilized: &'a StabilizedModule,
    pub parsed: &'a ParsedModule,
    pub resolved: &'a ResolvedModule,
}

fn import_item<F, G>(
    ctx: &ImportContext,
    engine: &building::QueryEngine,
    module_name: &str,
    file_id: FileId,
    lookup_fn: F,
    name_fn: G,
) -> (Option<String>, Option<Range>)
where
    F: Fn(&ResolvedImport) -> Option<ImportKind>,
    G: Fn(&IndexedModule) -> Option<String>,
{
    let existing_import = ctx.resolved.unqualified.get(module_name);
    let import_with_item = existing_import
        .into_iter()
        .flatten()
        .find_map(|import| lookup_fn(import).map(|kind| (import, kind)));

    let Ok(import_indexed) = engine.indexed(file_id) else {
        return (None, None);
    };

    if let Some((import, kind)) = import_with_item {
        // Implicit or hidden imports are skipped.
        if !matches!(import.kind, ImportKind::Explicit) {
            return (None, None);
        }

        // Names that are already imported are skipped.
        if matches!(kind, ImportKind::Explicit) {
            return (None, None);
        }

        let Some(ptr) = ctx.stabilized.ast_ptr(import.id) else {
            return (None, None);
        };

        let root = ctx.parsed.syntax_node();
        let Some(node) = ptr.try_to_node(&root) else {
            return (None, None);
        };

        let import_list =
            node.import_list().expect("invariant violated: ImportKind::Explicit w/ no ImportList");

        let Some(import_item_name) = name_fn(&import_indexed) else {
            return (None, None);
        };

        let import_item_name = {
            let mut buffer = SmolStrBuilder::new();
            buffer.push(' ');
            buffer.push_str(&import_item_name);
            buffer.finish()
        };

        // When adding e.g. Maybe(..), filter out a bare Maybe that it supersedes
        let superseded_prefix =
            import_item_name.trim().strip_suffix("(..)").map(|prefix| prefix.trim().to_string());

        let import_list = import_list
            .children()
            .map(|cst| {
                let cst = cst.syntax();
                cst.text().to_smolstr()
            })
            .filter(|existing| {
                if let Some(prefix) = &superseded_prefix { existing.trim() != prefix } else { true }
            })
            .chain(iter::once(import_item_name))
            .join(",");

        let import_text = format!("import {module_name} ({import_list})");

        let import_range = {
            let ptr = ptr.syntax_node_ptr();
            locate::syntax_range(ctx.content, &root, &ptr)
        };

        (Some(import_text), import_range)
    } else if let Some(import_item_name) = name_fn(&import_indexed) {
        let import_text = format!("import {module_name} ({import_item_name})\n");
        (Some(import_text), None)
    } else {
        (None, None)
    }
}

pub fn term_import_item(
    ctx: &ImportContext,
    engine: &building::QueryEngine,
    module_name: &str,
    term_name: &str,
    file_id: FileId,
    term_id: TermItemId,
) -> (Option<String>, Option<Range>) {
    import_item(
        ctx,
        engine,
        module_name,
        file_id,
        |import| {
            import
                .lookup_term(term_name)
                .and_then(|(f, t, k)| if (f, t) == (file_id, term_id) { Some(k) } else { None })
        },
        |import_indexed| term_import_name(import_indexed, term_name, term_id),
    )
}

pub fn type_import_item(
    ctx: &ImportContext,
    engine: &building::QueryEngine,
    module_name: &str,
    type_name: &str,
    file_id: FileId,
    type_id: TypeItemId,
) -> (Option<String>, Option<Range>) {
    import_item(
        ctx,
        engine,
        module_name,
        file_id,
        |import| {
            import
                .lookup_type(type_name)
                .or_else(|| import.lookup_class(type_name))
                .and_then(|(f, t, k)| if (f, t) == (file_id, type_id) { Some(k) } else { None })
        },
        |import_indexed| type_import_name(import_indexed, type_name, type_id),
    )
}

pub fn term_import_name(
    import_indexed: &IndexedModule,
    term_name: &str,
    term_id: TermItemId,
) -> Option<String> {
    let term_item = &import_indexed.items[term_id];
    if matches!(term_item.kind, TermItemKind::Constructor { .. }) {
        let type_id = import_indexed
            .pairs
            .constructor_type(term_id)
            .expect("invariant violated: floating data constructor");
        let type_item = &import_indexed.items[type_id];
        let Some(type_name) = &type_item.name else {
            tracing::trace!("Missing name for {:?}", type_id);
            return None;
        };
        Some(format!("{type_name}(..)"))
    } else if matches!(term_item.kind, TermItemKind::Operator { .. }) {
        Some(format!("({term_name})"))
    } else {
        Some(term_name.to_string())
    }
}

pub fn type_import_name(
    import_indexed: &IndexedModule,
    type_name: &str,
    type_id: TypeItemId,
) -> Option<String> {
    let type_item = &import_indexed.items[type_id];
    if matches!(type_item.kind, TypeItemKind::Class { .. }) {
        Some(format!("class {type_name}"))
    } else if matches!(type_item.kind, TypeItemKind::Operator { .. }) {
        Some(format!("type ({type_name})"))
    } else {
        Some(type_name.to_string())
    }
}
