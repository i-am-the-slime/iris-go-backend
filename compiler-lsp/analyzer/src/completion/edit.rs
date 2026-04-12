use async_lsp::lsp_types::Range;
use files::FileId;
use indexing::{TermItemId, TypeItemId};

use crate::completion::Context;
use crate::import_edit::{self, ImportContext};

pub(super) fn term_import_item(
    context: &Context,
    module_name: &str,
    term_name: &str,
    file_id: FileId,
    term_id: TermItemId,
) -> (Option<String>, Option<Range>) {
    let ctx = ImportContext {
        content: context.content,
        stabilized: context.stabilized,
        parsed: context.parsed,
        resolved: context.resolved,
    };
    import_edit::term_import_item(&ctx, context.engine, module_name, term_name, file_id, term_id)
}

pub(super) fn type_import_item(
    context: &Context,
    module_name: &str,
    type_name: &str,
    file_id: FileId,
    type_id: TypeItemId,
) -> (Option<String>, Option<Range>) {
    let ctx = ImportContext {
        content: context.content,
        stabilized: context.stabilized,
        parsed: context.parsed,
        resolved: context.resolved,
    };
    import_edit::type_import_item(&ctx, context.engine, module_name, type_name, file_id, type_id)
}
