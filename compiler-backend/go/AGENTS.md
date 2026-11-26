# Go backend

Read the repository's root `AGENTS.md` first. This file adds the rules that are specific to the Go
backend. They exist because the cheapest way to make a failing program compile is almost always a
shortcut, and a shortcut taken once becomes the pattern for every later fix.

## What generated Go must look like

The backend specialises the whole program from the checker's exact types. Generated Go should read
as if a careful person had written it by hand for those types.

- Real Go types everywhere. `any` and type assertions are reserved for polymorphic recursion whose
  types genuinely grow without bound. Every other source of erasure is a backend bug.
  - Rank-N quantified values (`Scene`, CPS parsers' answer types, and similar) are specialised per
    instantiation, not erased.
  - Recursive newtypes and data types become recursive named Go types.
- Effects are direct. `a -> Effect b` is `func(A) B`, a do-block is a sequence of statements, and a
  thunk exists only where an effect is genuinely first-class.
- PureScript `Int` is Go's `int` and wraps at its width, not at JavaScript's 32 bits (see
  documentation/go-output.md). It crosses Go APIs without conversions.
- No `reflect` and no `unsafe` in generated code, except the `Array Int` SIMD kernels, which view a
  `[]int` as `[]int64` in files that build only for arm64 and wasm.
- Calls read like the PureScript they come from: `n(f, x)`, never `n.Apply(f, x)`, `Invoke`,
  `Call2` or similar plumbing names.
- Programs keep PureScript's semantics: the same output as the JS backend for everything
  PureScript defines, such as `show`, String's UTF-16 code units and Int's 32-bit wrapping.
  JavaScript and engine accidents are not copied: float results may differ in the last digits
  (Go's math, fused multiply-add), and an Int result JS leaves outside 32 bits wraps. Each such
  difference is listed in documentation/go-output.md.

## Gates

Work is done when every gate passes. A passing gate that was weakened to pass does not count.

- `compiler-backend/go/scripts/run-examples.sh` runs every example, compares its output with JS, and
  then checks generated-Go quality with `scripts/quality.sh`.
- `compiler-backend/go/scripts/markgraf/run.sh` checks that the compactor's output equals JS.
- `just integration` runs the snapshot tests.

`quality-baseline.txt` holds the number of escape hatches (`any` and its causes, type assertions,
`reflect`, `unsafe`, `panic`) in each scope. It is a ratchet:

- A rise fails the gate. Fix the cause; do not raise the number.
- When one drops, lower the baseline with `quality.sh --update` in the same change.
- Raising one is a hand edit in a change whose description explains why no typed solution exists.

Size and readability numbers (lines, functions, nesting) are printed for information only.

## Shortcuts that are not allowed

- Erasing a type to `any` to get past a Go type error.
- Generic runtime helpers over `any` where a specialised, typed function can be emitted.
- Special-casing a function, module or type by name to make one program build. The one exception
  is `primitives::known`, a small table of primitives of very stable libraries (`Data.Exists`)
  whose meaning the backend implements in general, approved by the maintainer.
- Stubbing a foreign or emitting `panic("not implemented")` for code the target program reaches.
- Weakening a test: removing an edge case, loosening a comparison, excluding an example, or
  accepting a regenerated snapshot without reading the diff.
- Silent fallbacks. Every degraded code path reports a diagnostic with its reason, so that the
  erasure census accounts for every `any` that remains.

When the correct fix is out of scope or needs a design decision, stop and report it. Do not ship
the shortcut and mention it afterwards.

## Reporting

Say what changed, the gate results, and anything left undone.

## Runbook

The fork is `i-am-the-slime/iris-go-backend`, jj remote `fork`. Never push to `origin`
(purefunctor/purescript-iris).

### Workspace and build

```bash
jj -R ~/Developer/iris-ws-merge6 workspace add ~/Developer/iris-ws-<name> -r main@fork
cd ~/Developer/iris-ws-<name>
export CARGO_BUILD_JOBS=4 GOMAXPROCS=4    # always, on Mark's laptop
cargo build -p iris-cli --release          # target/release/googoo
```

`IRIS_GO` points at the iris-go checkout to build against (Mark's shell sets `~/Developer/iris-go`,
kept on main).

### Quick local checks

Run only what the change touches. Never run the full suites locally; CI runs them.

```bash
just integration --test go <fixture-dir>           # one Go fixture, e.g. 1794566171_recursive_newtypes
just integration --test go_style <fixture-dir>     # one style-suite fixture
just t go <fixture-dir>                            # same, and update its snapshot (read the diff)
IRIS=$PWD/target/release/googoo JOBS=4 \
  compiler-backend/go/scripts/run-examples.sh Tco01 Array01   # selected iris-go examples vs JS
```

Selected examples skip the quality ratchet; the full run in CI checks it.

### Full gates in CI

Pushing a branch named `gates/<name>` to `fork` runs the Gates workflow
(`.github/workflows/gates.yml`), in about 15 minutes:

- every `tests-integration` test with the Go fixtures' builds required, in 4 hash partitions;
- `tests-e2e` on Linux;
- iris-go's examples against JS (`run-examples.sh`, quality ratchet included);
- the registry sweep against `tests-compatibility/go-sweep-baseline.tsv`, 4 shards x 3 build parts.

They build against the iris-go tag in `RUNTIME_VERSION`. A manual run can take another ref:
`gh workflow run gates.yml -R i-am-the-slime/iris-go-backend --ref gates/<name> -f runtime-ref=main`.

```bash
jj bookmark create gates/<name> -r @-
jj git push --remote fork -b gates/<name> --allow-new
gh run list -R i-am-the-slime/iris-go-backend -w Gates -b gates/<name> -L 1
gh run watch <run-id> -R i-am-the-slime/iris-go-backend --exit-status
gh run view <run-id> -R i-am-the-slime/iris-go-backend --log-failed
```

The Summary job's page has one row per gate. Delete the branch when done:
`jj bookmark delete gates/<name> && jj git push --remote fork --deleted`.

`main` runs Cargo Build & Test on push (all platforms, Go fixtures and style suite, examples
against iris-go main). The registry sweep also runs nightly at 02:17 UTC against iris-go main.

### Cutting a release

Only when Mark asks.

1. Tag and push iris-go (`vX.Y.Z`) if the runtime changed.
2. Set `RUNTIME_VERSION` (`compiler-executable/iris-go/src/program.rs`) and `GO_RUNTIME_VERSION`
   (`tests-integration/src/fixtures.rs`) to that tag; `just prepare-release 0.1.18-go.N`.
3. Commit `Release 0.1.18-go.N against iris-go vX.Y.Z`, get Gates green, move `main` there and
   push it to `fork` (fast-forward).
4. Tag `v0.1.18-go.N` on that commit and push the tag to `fork`; Cargo Build & Release publishes
   the `googoo-<target>` archives.
5. Tap (`i-am-the-slime/homebrew-tap`): set `version` in `Formula/googoo.rb`, run
   `bin/update-googoo-checksums`, commit `googoo 0.1.18-go.N`, push.
6. Package set (`rowtype-yoga/purescript-go-package-sets`): `gogogo scripts/verify.purs` with the
   new googoo, add the row to the README's tag table, tag `go-0.1.18-<yyyymmdd>[.n]`, push.
