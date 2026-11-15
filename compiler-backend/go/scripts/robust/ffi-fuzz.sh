#!/usr/bin/env bash
#
# Differential FFI fuzzing of the Go backend against JS. Generates PureScript programs that call
# the strings, arrays, integers, numbers, Map/Set, Object, show and JSON functions whose foreigns
# go-support implements, on adversarial and seeded random inputs, one output line per call.
# Compiles them with purs-backend-es (run under Bun: the original JS foreigns, the oracle) and with
# `iris go`, runs both, and prints every divergence grouped by function, with a minimal input.
#
#   compiler-backend/go/scripts/robust/ffi-fuzz.sh                 # every area, seed 1
#   compiler-backend/go/scripts/robust/ffi-fuzz.sh Strings Arrays  # module name filters
#   FUZZ_SEED=7 FUZZ_RANDOM=60 ...                                 # other seed, more random cases
#   SKIP_BUILD=1 ...                                               # rerun WORK's programs
#
# Divergences are reported in classes: real ones; those whose input or JS output holds a lone
# surrogate (go-support keeps strings as UTF-8, which cannot hold one; go-support prim/string.go
# explains the seam); those where the JS result is not an Int at all (JS `-x`, `x % 0`, `>>>`);
# those with a `__proto__` key, which a JS object literal treats as its prototype; and those where
# Bun and Deno disagree with each other.
#
# Environment: IRIS, GO_SUPPORT, PURS_BACKEND_ES, WORK (kept), JOBS, FUZZ_SEED, FUZZ_RANDOM,
# FUZZ_CHUNK (cases per program), FUZZ_GO_TAGS (e.g. `libm`: go-support's transcendental functions
# from the C library, as JavaScriptCore on macOS computes them), GOEXPERIMENT (default simd).

set -uo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../../../.." && pwd)"
IRIS="${IRIS:-$ROOT/target/release/iris}"
GO_SUPPORT="${GO_SUPPORT:-/Users/mark/Developer/purs-backend-go/go-support}"
export GOEXPERIMENT="${GOEXPERIMENT:-simd}"
PURS_BACKEND_ES="${PURS_BACKEND_ES:-${MARKGRAF_GATES:-/Users/mark/Developer/markgraf-gates}/npm/node_modules/.bin/purs-backend-es}"
WORK="${WORK:-${TMPDIR:-/tmp}/iris-ffi-fuzz}"
JOBS="${JOBS:-6}"
SEED="${FUZZ_SEED:-1}"
RANDOM_CASES="${FUZZ_RANDOM:-24}"
PROJECT="$WORK/project"
mkdir -p "$PROJECT/src/Fuzz" "$WORK/go" "$WORK/results"

[ -x "$IRIS" ] || { echo "no iris binary at $IRIS (cargo build --release -p iris-cli)"; exit 1; }

build_javascript() {
  cp "$HERE/ffi-fuzz/spago.yaml" "$PROJECT/spago.yaml"
  rm -f "$PROJECT"/src/Fuzz/*.purs
  cp "$HERE"/ffi-fuzz/src/Fuzz/*.purs "$PROJECT/src/Fuzz/"
  bun "$HERE/ffi-fuzz/gen.ts" "$PROJECT/src" "$WORK/cases.json" "$SEED" "$RANDOM_CASES" >"$WORK/modules.txt" || exit 1
  (cd "$PROJECT" && spago build --quiet) >"$WORK/spago.log" 2>&1 || { tail -40 "$WORK/spago.log"; exit 1; }
  local sources=()
  while IFS= read -r source; do sources+=("$PROJECT/$source"); done < <(cd "$PROJECT" && spago sources 2>/dev/null)
  (cd "$PROJECT" && purs compile "${sources[@]}" --codegen corefn --output "$WORK/corefn") >"$WORK/purs.log" 2>&1 \
    || { tail -40 "$WORK/purs.log"; exit 1; }
  rm -rf "$WORK/es"
  (cd "$PROJECT" && "$PURS_BACKEND_ES" build --corefn-dir "$WORK/corefn" --output-dir "$WORK/es") >"$WORK/es.log" 2>&1 \
    || { tail -40 "$WORK/es.log"; exit 1; }
  cat > "$WORK/run.mjs" <<'JS'
const name = typeof Deno !== "undefined" ? Deno.args[0] : process.argv[2];
const module = await import(new URL(`./es/${name}/index.js`, import.meta.url));
module.main();
JS
}

build_go() {
  local name="$1" out="$WORK/go/$1"
  rm -rf "$out"
  mkdir -p "$out"
  cat > "$out/go.mod" <<GOMOD
module ffifuzz.example/program

go 1.27.0

require github.com/i-am-the-slime/purs-backend-go/go-support v0.0.0

replace github.com/i-am-the-slime/purs-backend-go/go-support => $GO_SUPPORT
GOMOD
  if ! (cd "$PROJECT" && timeout 600 "$IRIS" go --entry "$name.main" "$out") >"$out/compile.log" 2>&1; then
    echo iris >"$out/stage"; return
  fi
  if ! (cd "$out" && go build ${FUZZ_GO_TAGS:+-tags "$FUZZ_GO_TAGS"} -o program .) >"$out/build.log" 2>&1; then
    echo go-build >"$out/stage"; return
  fi
  echo built >"$out/stage"
}
export -f build_go
export PROJECT IRIS GO_SUPPORT WORK FUZZ_GO_TAGS

run_both() {
  local name="$1" result="$WORK/results/$1"
  (cd "$WORK" && timeout 600 bun run.mjs "$name") >"$result.js.out" 2>"$result.js.err"
  echo "$?" >"$result.js.status"
  # Deno (V8) is a second oracle: where the two engines disagree, the case says so.
  if command -v deno >/dev/null; then
    (cd "$WORK" && timeout 600 deno run -A run.mjs "$name") >"$result.deno.out" 2>"$result.deno.err"
  fi
  if [ "$(cat "$WORK/go/$name/stage" 2>/dev/null)" = built ]; then
    timeout 600 "$WORK/go/$name/program" >"$result.go.out" 2>"$result.go.err"
    echo "$?" >"$result.go.status"
  else
    : >"$result.go.out"; : >"$result.go.err"; echo "not built" >"$result.go.status"
  fi
}
export -f run_both

if [ "${SKIP_BUILD:-0}" != 1 ]; then
  build_javascript
fi

names=()
while IFS= read -r name; do
  if [ "$#" -eq 0 ]; then names+=("$name"); else
    for filter in "$@"; do case "$name" in *"$filter"*) names+=("$name"); break ;; esac; done
  fi
done <"$WORK/modules.txt"
[ "${#names[@]}" -gt 0 ] || { echo "no fuzz program matches $*"; exit 1; }

if [ "${SKIP_BUILD:-0}" != 1 ]; then
  printf '%s\n' "${names[@]}" | xargs -P "$JOBS" -I{} bash -c 'build_go "$1"' _ {}
fi
printf '%s\n' "${names[@]}" | xargs -P "$JOBS" -I{} bash -c 'run_both "$1"' _ {}

bun "$HERE/ffi-fuzz/compare.ts" "$WORK" "${names[@]}"
