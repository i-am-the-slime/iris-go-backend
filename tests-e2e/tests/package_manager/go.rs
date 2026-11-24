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
fn go_reports_a_parse_error_that_hides_the_entry_point() {
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

import Data.Unit (Unit

main :: Int
main = 1
"#,
    );
    workspace.write("go/go.mod", "module example.com/application\n\ngo 1.27.0\n");

    let output = workspace.command(&["go", "--entry", "Main.main", "go"]);

    insta::with_settings!({omit_expression => true}, {
        insta::assert_snapshot!("go_parse_error_diagnostics", workspace.report(&output));
    });
}

#[test]
fn go_reports_custom_warnings_of_a_program_it_compiles() {
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

import Prim.TypeError (class Warn, Text)

deprecated :: Warn (Text "deprecated is deprecated") => Int -> Int
deprecated n = n

main :: Int
main = deprecated 1
"#,
    );
    workspace.write("go/go.mod", "module example.com/application\n\ngo 1.27.0\n");

    let output = workspace.command(&["go", "--entry", "Main.main", "go"]);

    insta::with_settings!({omit_expression => true}, {
        insta::assert_snapshot!("go_custom_warning_diagnostics", workspace.report(&output));
    });
    assert!(workspace.path().join("go/main.go").exists());
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
    let executable = workspace
        .path()
        .join(format!(".spago/go/greeter/bin/greeter{}", std::env::consts::EXE_SUFFIX));
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

#[cfg(unix)]
#[test]
fn run_go_copies_the_files_foreign_go_embeds_into_the_program() {
    let workspace = greeting_workspace(
        r#"package ffi

import (
	"embed"
	_ "embed"
	"fmt"
	"io/fs"
)

//go:embed greeting.txt
var greeting string

//go:embed fonts "styles/*.css"
//go:embed linked/logo.svg all:config
var assets embed.FS

func Greet() int32 {
	fmt.Print(greeting)
	fs.WalkDir(assets, ".", func(path string, entry fs.DirEntry, err error) error {
		if !entry.IsDir() {
			contents, _ := assets.ReadFile(path)
			fmt.Printf("%s: %s", path, contents)
		}
		return nil
	})
	return 0
}
"#,
    );
    workspace.write("src/greeting.txt", "Hello from an embedded file!\n");
    workspace.write("src/fonts/Inter.ttf", "inter\n");
    workspace.write("src/fonts/bold/Inter-Bold.ttf", "inter bold\n");
    workspace.write("src/fonts/.DS_Store", "hidden\n");
    workspace.write("src/fonts/_draft.ttf", "draft\n");
    workspace.write("src/styles/main.css", "main\n");
    workspace.write("src/config/.env", "kept by all:\n");
    workspace.write("src/styles/notes.txt", "not a stylesheet\n");
    workspace.write("shared/logo.svg", "<svg/>\n");
    std::os::unix::fs::symlink(
        workspace.path().join("shared"),
        workspace.path().join("src/linked"),
    )
    .unwrap();

    let output = workspace.command(&["run", "--go", "--quiet"]);
    insta::assert_snapshot!(workspace.report(&output), @"
    status: 0
    --- stdout
    Hello from an embedded file!
    config/.env: kept by all:
    fonts/Inter.ttf: inter
    fonts/bold/Inter-Bold.ttf: inter bold
    linked/logo.svg: <svg/>
    styles/main.css: main
    --- stderr
    ");
}

#[test]
fn run_go_refuses_an_embed_pattern_that_leaves_the_directory_of_the_go_file() {
    let workspace = greeting_workspace(
        "package ffi\n\nimport _ \"embed\"\n\n//go:embed ../shared/greeting.txt\nvar greeting string\n\nfunc Greet() int32 { return 0 }\n",
    );
    workspace.write("shared/greeting.txt", "Hello!\n");

    let output = workspace.command(&["run", "--go", "--quiet"]);
    insta::assert_snapshot!(workspace.report(&output), @"
    status: 1
    --- stdout
    --- stderr
    src/Greeting.go: //go:embed ../shared/greeting.txt: the pattern leaves the directory of the Go file; embed only files beside it or below it
    ");
}

#[test]
fn run_go_names_the_go_file_and_the_embed_pattern_that_matches_nothing() {
    let workspace = greeting_workspace(
        "package ffi\n\nimport _ \"embed\"\n\n//go:embed greeting.txt\nvar greeting string\n\nfunc Greet() int32 { return 0 }\n",
    );

    let output = workspace.command(&["run", "--go", "--quiet"]);
    insta::assert_snapshot!(workspace.report(&output), @"
    status: 1
    --- stdout
    --- stderr
    src/Greeting.go: //go:embed greeting.txt: no matching files found
    ");
}

#[test]
fn run_go_and_go_copy_the_files_a_dependency_embeds() {
    let workspace = TestWorkspace::empty();
    workspace.write("spago.yaml", "workspace: {}\n");
    workspace.write(
        "packages/application/spago.yaml",
        "package:\n  name: application\n  dependencies:\n    - greeting\n",
    );
    workspace.write(
        "packages/application/src/Main.purs",
        "module Main where\n\nimport Effect (Effect)\nimport Greeting (greet)\n\nmain :: Effect Int\nmain = greet\n",
    );
    workspace
        .write("packages/greeting/spago.yaml", "package:\n  name: greeting\n  dependencies: []\n");
    workspace.write(
        "packages/greeting/src/Effect.purs",
        "module Effect where\n\nforeign import data Effect :: Type -> Type\n",
    );
    workspace.write(
        "packages/greeting/src/Greeting.purs",
        "module Greeting where\n\nimport Effect (Effect)\n\nforeign import greet :: Effect Int\n",
    );
    workspace.write(
        "packages/greeting/src/Greeting.go",
        "package ffi\n\nimport (\n\t_ \"embed\"\n\t\"fmt\"\n)\n\n//go:embed greeting.txt\nvar greeting string\n\nfunc Greet() int32 {\n\tfmt.Print(greeting)\n\treturn 0\n}\n",
    );
    workspace.write("packages/greeting/src/greeting.txt", "Hello from a dependency!\n");
    workspace
        .write("packages/application/go/go.mod", "module example.com/application\n\ngo 1.27.0\n");

    let output = workspace.command(&["run", "--go", "--quiet", "--package", "application"]);
    insta::assert_snapshot!(workspace.report(&output), @"
    status: 0
    --- stdout
    Hello from a dependency!
    --- stderr
    ");

    let output =
        workspace.command_in("packages/application", &["go", "--entry", "Main.main", "go"]);
    assert!(output.status.success(), "{}", workspace.report(&output));
    assert_eq!(
        workspace.read("packages/application/go/Greeting_ffi/greeting.txt"),
        "Hello from a dependency!\n"
    );
}

#[test]
fn run_go_stack_traces_name_the_purescript_lines() {
    let workspace = TestWorkspace::empty();
    workspace.write("spago.yaml", "workspace: {}\npackage:\n  name: crasher\n  dependencies: []\n");
    workspace.write(
        "src/Effect.purs",
        "module Effect where\n\nforeign import data Effect :: Type -> Type\n",
    );
    workspace.write(
        "src/Main.purs",
        r#"module Main where

import Effect (Effect)

foreign import at :: Array Int -> Int -> Int
foreign import exitWith :: Int -> Effect Int

third :: Array Int -> Int
third numbers =
  at numbers 2

main :: Effect Int
main = exitWith (third [ 1, 2 ])
"#,
    );
    workspace.write(
        "src/Main.go",
        "package ffi\n\nfunc At(numbers []int32, index int32) int32 {\n\treturn numbers[index]\n}\n\nfunc ExitWith(status int32) int32 {\n\treturn status\n}\n",
    );

    let output = workspace.command(&["run", "--go", "--quiet"]);
    let stderr = workspace.normalize_output(&output.stderr);
    assert!(stderr.contains("index out of range [2] with length 2"), "{stderr}");
    let frame = |line: &str| {
        let line = line.trim();
        line == "[WORKSPACE]/src/Main.purs:13" || line.starts_with("[WORKSPACE]/src/Main.purs:13 ")
    };
    assert!(
        stderr.lines().any(frame),
        "the frame of `main`, into which `third` is inlined, names the line calling it:\n{stderr}"
    );

    workspace.write("go/go.mod", "module example.com/crasher\n\ngo 1.27.0\n");
    let output = workspace.command(&["go", "--entry", "Main.main", "go"]);
    assert!(output.status.success(), "{}", workspace.report(&output));
    let generated = workspace.read("go/main.go");
    assert!(generated.contains("\n//line ../src/Main.purs:13:8\n"), "{generated}");
    let formatted = std::process::Command::new("gofmt")
        .arg(workspace.path().join("go/main.go"))
        .output()
        .unwrap();
    assert!(formatted.status.success(), "{}", String::from_utf8_lossy(&formatted.stderr));
    assert!(
        String::from_utf8_lossy(&formatted.stdout).contains("\n//line ../src/Main.purs:13:8\n"),
        "gofmt keeps the directives at the start of their lines"
    );

    let output = workspace.command(&["go", "--entry", "Main.main", "--no-line-directives", "go"]);
    assert!(output.status.success(), "{}", workspace.report(&output));
    assert!(!workspace.read("go/main.go").contains("//line"));
}

/// A package whose `main` prints what `Greeting.go` makes of the files it embeds.
fn greeting_workspace(greeting_go: &str) -> TestWorkspace {
    let workspace = TestWorkspace::empty();
    workspace.write("spago.yaml", "workspace: {}\npackage:\n  name: greeter\n  dependencies: []\n");
    workspace.write(
        "src/Effect.purs",
        "module Effect where\n\nforeign import data Effect :: Type -> Type\n",
    );
    workspace.write(
        "src/Greeting.purs",
        "module Greeting where\n\nimport Effect (Effect)\n\nforeign import greet :: Effect Int\n",
    );
    workspace.write(
        "src/Main.purs",
        "module Main where\n\nimport Effect (Effect)\nimport Greeting (greet)\n\nmain :: Effect Int\nmain = greet\n",
    );
    workspace.write("src/Greeting.go", greeting_go);
    workspace
}
