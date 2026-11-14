use super::support::TestWorkspace;

#[test]
fn go_reports_checking_errors_instead_of_generating_code() {
    let workspace = TestWorkspace::empty();
    workspace.write(
        "spago.yaml",
        r#"workspace: {}
package:
  name: application
  dependencies: []
"#,
    );
    workspace.write(
        "src/Main.purs",
        r#"module Main where

type Segment = { spans :: Array { startT :: Number, source :: Int } }

segment :: Segment
segment = { spans: [ { startT: 1.0, source: 2 } ] }

spansOf :: forall r. { spans :: Array { startT :: Number } | r } -> Array { startT :: Number }
spansOf open = open.spans

main :: Array { startT :: Number }
main = spansOf segment
"#,
    );
    workspace.write("go/go.mod", "module example.com/application\n\ngo 1.27.0\n");

    let output = workspace.command(&["go", "--entry", "Main.main", "go"]);

    insta::with_settings!({omit_expression => true}, {
        insta::assert_snapshot!("go_checking_error_diagnostics", workspace.report(&output));
    });
    assert!(!workspace.path().join("go/main.go").exists());
}
