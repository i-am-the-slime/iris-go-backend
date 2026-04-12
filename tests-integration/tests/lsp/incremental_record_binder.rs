//! Test that record binder completion survives incremental typing.
//! Simulates VS Code behavior: initial `{ }` → gets all fields including `path`,
//! then typing `p` → should still show `path` from the cache.

use analyzer::completion::{RecordFieldsCache, SuggestionsCache};
use async_lsp::lsp_types::*;

#[test]
fn record_binder_fields_persist_across_incremental_typing() {
    let path = std::path::Path::new("fixtures/lsp").join("040_completion_space_trigger_done");
    let (mut engine, mut files) = tests_integration::load_compiler(&path);

    let id = engine.module_file("Main").expect("Main module not found");
    let original_content = engine.content(id).to_string();

    // Find the line with `{  } <- ask` in test 1 (deleteTodoHandler).
    let target_line = original_content
        .lines()
        .position(|l| l.contains("{  } <- ask") && !l.starts_with("--"))
        .expect("couldn't find {  } <- ask");

    let uri_str = files.path(id).to_string();
    let uri = Url::parse(&uri_str).unwrap();
    let uri = analyzer::prim::handle_generated(uri, &original_content).unwrap();

    let mut suggestions_cache = SuggestionsCache::default();
    let mut record_fields_cache = RecordFieldsCache::default();

    // Step 1: Completion at `{  } <- ask` — should find all fields including `path`.
    let position = Position { line: target_line as u32, character: 3 };
    let response = analyzer::completion::implementation(
        &engine,
        &files,
        &mut suggestions_cache,
        &mut record_fields_cache,
        uri.clone(),
        position,
        None,
    );
    let items = extract_items(response);
    let labels: Vec<&str> = items.iter().map(|i| i.label.as_str()).collect();
    assert!(
        labels.contains(&"path"),
        "Step 1: initial `{{  }}` should contain `path`, got: {labels:?}"
    );
    let initial_count = labels.len();
    eprintln!("Step 1: {initial_count} fields: {labels:?}");

    // Step 2: Simulate typing "p" — update file content to `{p} <- ask`.
    let modified = original_content.replacen("{  } <- ask", "{p} <- ask", 1);
    let file_id = files.insert(uri_str.clone(), modified.clone());
    engine.set_content(file_id, files.content(file_id));

    // Position is now at `p` inside `{p}`.
    let position = Position { line: target_line as u32, character: 3 };
    let response = analyzer::completion::implementation(
        &engine,
        &files,
        &mut suggestions_cache,
        &mut record_fields_cache,
        uri.clone(),
        position,
        None,
    );
    let items = extract_items(response);
    let labels: Vec<&str> = items.iter().map(|i| i.label.as_str()).collect();
    eprintln!("Step 2: {} fields: {labels:?}", labels.len());
    assert!(
        labels.contains(&"path"),
        "Step 2: after typing `p`, should still contain `path` (from cache), got: {labels:?}"
    );
    assert!(
        labels.len() >= initial_count,
        "Step 2: should have at least as many fields as step 1 ({initial_count}), got: {}",
        labels.len()
    );
}

#[test]
fn record_binder_fields_persist_through_multiple_keystrokes() {
    let path = std::path::Path::new("fixtures/lsp").join("040_completion_space_trigger_done");
    let (mut engine, mut files) = tests_integration::load_compiler(&path);

    let id = engine.module_file("Main").expect("Main module not found");
    let original_content = engine.content(id).to_string();

    let target_line = original_content
        .lines()
        .position(|l| l.contains("{  } <- ask") && !l.starts_with("--"))
        .expect("couldn't find {  } <- ask");

    let uri_str = files.path(id).to_string();
    let uri = Url::parse(&uri_str).unwrap();
    let uri = analyzer::prim::handle_generated(uri, &original_content).unwrap();

    let mut suggestions_cache = SuggestionsCache::default();
    let mut record_fields_cache = RecordFieldsCache::default();

    let steps: &[(&str, &str)] = &[
        ("{  } <- ask", "empty braces"),
        ("{p} <- ask", "typed p"),
        ("{pa} <- ask", "typed pa"),
        ("{pat} <- ask", "typed pat"),
        ("{path} <- ask", "typed path"),
        ("{pa} <- ask", "backspaced to pa"),
        ("{p} <- ask", "backspaced to p"),
        ("{} <- ask", "backspaced to empty"),
        ("{c} <- ask", "typed c"),
        ("{co} <- ask", "typed co"),
        ("{con} <- ask", "typed con"),
    ];

    for (content_fragment, description) in steps {
        let modified = original_content.replacen("{  } <- ask", content_fragment, 1);
        let file_id = files.insert(uri_str.clone(), modified.clone());
        engine.set_content(file_id, files.content(file_id));

        let position = Position { line: target_line as u32, character: 3 };
        let response = analyzer::completion::implementation(
            &engine,
            &files,
            &mut suggestions_cache,
            &mut record_fields_cache,
            uri.clone(),
            position,
            None,
        );
        let items = extract_items(response);
        let labels: Vec<&str> = items.iter().map(|i| i.label.as_str()).collect();
        eprintln!("{description}: {} fields: {labels:?}", labels.len());

        assert!(labels.contains(&"path"), "{description}: should contain `path`, got: {labels:?}");
        assert!(
            labels.contains(&"config"),
            "{description}: should contain `config`, got: {labels:?}"
        );
        assert!(
            labels.contains(&"authApi"),
            "{description}: should contain `authApi`, got: {labels:?}"
        );
        assert!(labels.contains(&"db"), "{description}: should contain `db`, got: {labels:?}");
    }
}

#[test]
fn record_binder_with_named_binder_and_corruption() {
    let path = std::path::Path::new("fixtures/lsp").join("040_completion_space_trigger_done");
    let (mut engine, mut files) = tests_integration::load_compiler(&path);

    let id = engine.module_file("Main").expect("Main module not found");
    let original_content = engine.content(id).to_string();

    // Find the line with `ctx@{  } <- ask` (test 5 in fixture).
    let target_line = original_content
        .lines()
        .position(|l| l.contains("ctx@{  } <- ask"))
        .expect("couldn't find ctx@{  } <- ask");

    let uri_str = files.path(id).to_string();
    let uri = Url::parse(&uri_str).unwrap();
    let uri = analyzer::prim::handle_generated(uri, &original_content).unwrap();

    let mut suggestions_cache = SuggestionsCache::default();
    let mut record_fields_cache = RecordFieldsCache::default();

    let steps: &[(&str, &str)] = &[
        ("ctx@{  } <- ask", "empty named binder"),
        ("ctx@{p} <- ask", "typed p in named binder"),
        ("ctx@{pa} <- ask", "typed pa in named binder"),
        ("ctx@{path} <- ask", "typed path in named binder"),
        ("ctx@{p} <- ask", "backspaced to p in named binder"),
    ];

    for (content_fragment, description) in steps {
        let modified = original_content.replacen("ctx@{  } <- ask", content_fragment, 1);
        let file_id = files.insert(uri_str.clone(), modified.clone());
        engine.set_content(file_id, files.content(file_id));

        let position = Position { line: target_line as u32, character: 7 };
        let response = analyzer::completion::implementation(
            &engine,
            &files,
            &mut suggestions_cache,
            &mut record_fields_cache,
            uri.clone(),
            position,
            None,
        );
        let items = extract_items(response);
        let labels: Vec<&str> = items.iter().map(|i| i.label.as_str()).collect();
        eprintln!("{description}: {} fields: {labels:?}", labels.len());

        assert!(labels.contains(&"path"), "{description}: should contain `path`, got: {labels:?}");
        assert!(
            labels.len() >= 4,
            "{description}: should have at least 4 fields, got: {}",
            labels.len()
        );
    }
}

#[test]
fn dot_trigger_shows_all_fields() {
    let path = std::path::Path::new("fixtures/lsp").join("040_completion_space_trigger_done");
    let (engine, files) = tests_integration::load_compiler(&path);

    let id = engine.module_file("Main").expect("Main module not found");
    let content = engine.content(id).to_string();

    let target_line = content.lines().position(|l| l.trim() == "ctx.").expect("couldn't find ctx.");

    let uri_str = files.path(id).to_string();
    let uri = Url::parse(&uri_str).unwrap();
    let uri = analyzer::prim::handle_generated(uri, &content).unwrap();

    let mut suggestions_cache = SuggestionsCache::default();
    let mut record_fields_cache = RecordFieldsCache::default();

    let position = Position { line: target_line as u32, character: 6 };
    let response = analyzer::completion::implementation(
        &engine,
        &files,
        &mut suggestions_cache,
        &mut record_fields_cache,
        uri,
        position,
        Some("."),
    );
    let items = extract_items(response);
    let labels: Vec<&str> = items.iter().map(|i| i.label.as_str()).collect();
    eprintln!("dot trigger: {} fields: {labels:?}", labels.len());

    assert!(labels.contains(&"config"), "dot trigger should contain `config`, got: {labels:?}");
    assert!(labels.contains(&"authApi"), "dot trigger should contain `authApi`, got: {labels:?}");
    assert!(labels.contains(&"db"), "dot trigger should contain `db`, got: {labels:?}");
}

#[test]
fn record_accessor_section_asks_underscore_dot() {
    let path = std::path::Path::new("fixtures/lsp").join("040_completion_space_trigger_done");
    let (engine, files) = tests_integration::load_compiler(&path);

    let id = engine.module_file("Main").expect("Main module not found");
    let content = engine.content(id).to_string();

    let target_line =
        content.lines().position(|l| l.contains("asks _.")).expect("couldn't find asks _.");

    let uri_str = files.path(id).to_string();
    let uri = Url::parse(&uri_str).unwrap();
    let uri = analyzer::prim::handle_generated(uri, &content).unwrap();

    let mut suggestions_cache = SuggestionsCache::default();
    let mut record_fields_cache = RecordFieldsCache::default();

    // The dot is after `_.` — find the column.
    let line_content = content.lines().nth(target_line).unwrap();
    let dot_col = line_content.find("_.").unwrap() + 2; // after the dot

    let position = Position { line: target_line as u32, character: dot_col as u32 };
    let response = analyzer::completion::implementation(
        &engine,
        &files,
        &mut suggestions_cache,
        &mut record_fields_cache,
        uri,
        position,
        Some("."),
    );
    let items = extract_items(response);
    let labels: Vec<&str> = items.iter().map(|i| i.label.as_str()).collect();
    eprintln!("asks _. : {} fields: {labels:?}", labels.len());

    assert!(labels.contains(&"config"), "asks _. should contain `config`, got: {labels:?}");
    assert!(labels.contains(&"authApi"), "asks _. should contain `authApi`, got: {labels:?}");
    assert!(labels.contains(&"db"), "asks _. should contain `db`, got: {labels:?}");
}

fn extract_items(
    response: Result<Option<CompletionResponse>, analyzer::AnalyzerError>,
) -> Vec<CompletionItem> {
    match response.expect("completion should not error") {
        Some(CompletionResponse::List(list)) => list.items,
        Some(CompletionResponse::Array(items)) => items,
        None => vec![],
    }
}
