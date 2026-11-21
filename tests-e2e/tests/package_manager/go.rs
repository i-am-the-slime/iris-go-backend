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

#[test]
fn run_go_builds_once_and_passes_arguments_and_exit_status_through() {
    let workspace = TestWorkspace::empty();
    workspace.write(
        "spago.yaml",
        r#"workspace: {}
package:
  name: greeter
  dependencies: []
"#,
    );
    workspace.write(
        "src/Effect.purs",
        "module Effect where\n\nforeign import data Effect :: Type -> Type\n",
    );
    workspace.write(
        "src/Main.purs",
        r#"module Main where

import Effect (Effect)

foreign import greet :: Effect Int

main :: Effect Int
main = greet
"#,
    );
    workspace.write(
        "src/Main.go",
        r#"package ffi

import (
	"fmt"
	"os"
	"strings"
)

func Greet() int32 {
	fmt.Println("hello " + strings.Join(os.Args[1:], ","))
	return 3
}
"#,
    );

    let output = workspace.command(&["run", "--go", "--quiet", "--", "first", "second"]);
    insta::assert_snapshot!(workspace.report(&output), @"
    status: 3
    --- stdout
    hello first,second
    --- stderr
    ");
    let executable = workspace.path().join(".spago/go/greeter/bin/greeter");
    let built = std::fs::metadata(&executable).unwrap().modified().unwrap();

    let output = workspace.command(&["run", "--go", "--quiet", "--", "again"]);
    insta::assert_snapshot!(workspace.report(&output), @"
    status: 3
    --- stdout
    hello again
    --- stderr
    ");
    let unchanged = std::fs::metadata(&executable).unwrap().modified().unwrap();
    assert_eq!(built, unchanged, "an unchanged program is not built again");
}
