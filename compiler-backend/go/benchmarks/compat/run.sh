#!/usr/bin/env bash
#
# Compiles every compatibility program with purs-backend-es (run under Bun) and with `iris go`,
# runs both, and reports per program one of
#
#   OK | FLOAT CLOSE | JS FAILS | IRIS ERROR <category> | GO BUILD ERROR | RUNTIME PANIC | OUTPUT MISMATCH
#
# followed by a summary by category. FLOAT CLOSE passes: the outputs differ only in the last digits
# of their numbers, by at most FLOAT_TOLERANCE relative (default 1e-12), as Go's fused
# multiply-adds and its math package's rounding allow. A program is a module under src/ or repro/src/ that defines
# `main`. `JS FAILS` means the corpus program itself is wrong.
#
#   compiler-backend/go/benchmarks/compat/run.sh                 # every program
#   compiler-backend/go/benchmarks/compat/run.sh Hyrule Optics   # module name filters
#   SKIP_JS=1 ...                                                # reuse WORK's JavaScript build
#
# Environment: IRIS, GO_SUPPORT, PURS_BACKEND_ES, WORK (build directory, kept), JOBS, TIMEOUT,
# GOEXPERIMENT (default simd).

set -uo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../../../.." && pwd)"
IRIS="${IRIS:-$ROOT/target/release/iris}"
GO_SUPPORT="${GO_SUPPORT:-/Users/mark/Developer/iris-go}"
export GOEXPERIMENT="${GOEXPERIMENT:-simd}"
PURS_BACKEND_ES="${PURS_BACKEND_ES:-/Users/mark/Developer/markgraf/npm/node_modules/.bin/purs-backend-es}"
WORK="${WORK:-${TMPDIR:-/tmp}/iris-compat}"
JOBS="${JOBS:-6}"
TIMEOUT="${TIMEOUT:-120}"
FLOAT_TOLERANCE="${FLOAT_TOLERANCE:-1e-12}"
mkdir -p "$WORK/go" "$WORK/results"

programs() {
  grep -rlE '^main ::' "$HERE/src" "$HERE/repro/src" | sort | while read -r file; do
    sed -n 's/^module \([A-Za-z0-9.]*\).*/\1/p' "$file"
  done
}

selected() {
  if [ "$#" -eq 0 ]; then
    programs
  else
    for filter in "$@"; do programs | grep -F -- "$filter"; done | awk '!seen[$0]++'
  fi
}

package_of() {
  if [ -f "$HERE/repro/src/$(echo "$1" | tr . /).purs" ]; then echo compat-repro; else echo compat-corpus; fi
}

build_javascript() {
  (cd "$HERE" && bun install --silent) || exit 1
  ln -sfn "$HERE/node_modules" "$WORK/node_modules"
  # Dhall.Parser's foreign module imports the nearley grammar from ../../grammar.js.
  "$HERE/node_modules/.bin/nearleyc" "$HERE/dhall/grammar.ne" -o "$WORK/grammar.js" >"$WORK/nearley.log" 2>&1 \
    || { cat "$WORK/nearley.log"; exit 1; }
  (cd "$HERE" && spago build --quiet) >"$WORK/spago.log" 2>&1 || { cat "$WORK/spago.log"; exit 1; }
  local sources=()
  while IFS= read -r source; do sources+=("$HERE/$source"); done < <(cd "$HERE" && spago sources -p compat-repro 2>/dev/null)
  # purs writes foreign.js next to corefn.json only when it also generates JavaScript.
  (cd "$HERE" && purs compile "${sources[@]}" --codegen corefn,js --output "$WORK/corefn") >"$WORK/purs.log" 2>&1 \
    || { cat "$WORK/purs.log"; exit 1; }
  rm -rf "$WORK/es"
  (cd "$HERE" && "$PURS_BACKEND_ES" build --corefn-dir "$WORK/corefn" --output-dir "$WORK/es") >"$WORK/es.log" 2>&1 \
    || { cat "$WORK/es.log"; exit 1; }
  cat > "$WORK/run.mjs" <<'JS'
const module = await import(new URL(`./es/${process.argv[2]}/index.js`, import.meta.url));
module.main();
JS
}

build_go() {
  local name="$1" package="$2" out="$WORK/go/$1"
  rm -rf "$out"
  mkdir -p "$out"
  cat > "$out/go.mod" <<GOMOD
module compat.example/program

go 1.27.0

require github.com/i-am-the-slime/iris-go v0.0.0

replace github.com/i-am-the-slime/iris-go => $GO_SUPPORT
GOMOD
  (cd "$HERE" && IRIS_GO_ANY_CENSUS=1 timeout 300 "$IRIS" go -p "$package" --entry "$name.main" "$out") \
    >"$out/compile.log" 2>&1
  local status=$?
  if [ "$status" = 124 ]; then echo "iris timed out after 300 s" >>"$out/compile.log"; fi
  if [ "$status" != 0 ]; then
    echo iris >"$out/stage"
    return
  fi
  if ! (cd "$out" && go build -o program .) >"$out/build.log" 2>&1; then
    echo go-build >"$out/stage"
    return
  fi
  echo built >"$out/stage"
}

# The category of an iris failure: the kind of its first blocker, with the construct, the foreign
# module or the unsupported state named, so that programs blocked by one root cause group together.
iris_category() {
  local log="$1" line
  line="$(grep -m1 '^cannot specialize ' "$log")"
  if [ -z "$line" ]; then
    grep -v '^go:' "$log" | grep -m1 . | cut -c1-120
    return
  fi
  local state="${line#*: }"
  case "$state" in
    *"is not supported by the Go backend yet") echo "Construct: ${state% is not supported by the Go backend yet}" ;;
    "foreign import "*" has no Go implementation") local name="${state#foreign import }"; name="${name% has no Go implementation}"; echo "UnknownForeign ${name%.*}" ;;
    "foreign data type "*) local name="${state#foreign data type }"; echo "ForeignData ${name%% *}" ;;
    "type "*" has no closed representation") echo "OpenType" ;;
    "type variable "*) echo "UninstantiatedVariable" ;;
    "type constructor "*" is applied to too few arguments") echo "UnsaturatedType" ;;
    "specialization exceeded "*) echo "SpecializationLimit" ;;
    "instance head does not match"*) echo "InstanceMismatch" ;;
    "instance has no member"*) echo "MissingInstanceMember" ;;
    "instance has no superclass"*) echo "MissingSuperclass" ;;
    *) echo "$state" | cut -c1-100 ;;
  esac
}

classify() {
  local name="$1" out="$WORK/go/$1" result="$WORK/results/$1"
  if [ "$(cat "$result.js.status")" != 0 ]; then echo "JS FAILS"; return; fi
  case "$(cat "$out/stage")" in
    iris) echo "IRIS ERROR $(iris_category "$out/compile.log")"; return ;;
    go-build) echo "GO BUILD ERROR"; return ;;
  esac
  if [ "$(cat "$result.go.status")" != 0 ]; then
    if grep -q '^panic: \|^fatal error: ' "$result.go.err"; then echo "RUNTIME PANIC"; else echo "RUNTIME PANIC (exit $(cat "$result.go.status"))"; fi
    return
  fi
  if cmp -s "$result.go.out" "$result.js.out"; then
    echo OK
  elif bun "$HERE/../../scripts/markgraf/float-close.ts" "$result.js.out" "$result.go.out" "$FLOAT_TOLERANCE" >/dev/null; then
    echo "FLOAT CLOSE"
  else
    echo "OUTPUT MISMATCH"
  fi
}

detail() {
  local name="$1" out="$WORK/go/$1" result="$WORK/results/$1"
  case "$2" in
    "JS FAILS") head -c 300 "$result.js.err" | tr '\n' ' ' ;;
    "IRIS ERROR"*) grep -m1 '^cannot specialize ' "$out/compile.log" | cut -c1-240 ;;
    "GO BUILD ERROR") grep -m1 -v '^#' "$out/build.log" | cut -c1-240 ;;
    "RUNTIME PANIC"*) grep -m1 -A1 '^panic: \|^fatal error: ' "$result.go.err" | tr '\n' ' ' | cut -c1-240 ;;
    "FLOAT CLOSE") bun "$HERE/../../scripts/markgraf/float-close.ts" "$result.js.out" "$result.go.out" "$FLOAT_TOLERANCE" ;;
    "OUTPUT MISMATCH") diff "$result.js.out" "$result.go.out" | grep -m2 '^[<>]' | tr '\n' ' ' | cut -c1-240 ;;
  esac
}

export -f build_go
export HERE IRIS GO_SUPPORT WORK

names=()
while IFS= read -r name; do names+=("$name"); done < <(selected "$@")
[ "${#names[@]}" -gt 0 ] || { echo "no program matches $*"; exit 1; }

[ "${SKIP_JS:-0}" = 1 ] || build_javascript || exit 1
for name in "${names[@]}"; do printf '%s %s\n' "$name" "$(package_of "$name")"; done \
  | xargs -P "$JOBS" -L1 bash -c 'build_go "$1" "$2"' _

for name in "${names[@]}"; do
  result="$WORK/results/$name"
  (cd "$WORK" && timeout "$TIMEOUT" bun run.mjs "$name") >"$result.js.out" 2>"$result.js.err"
  echo "$?" >"$result.js.status"
  if [ "$(cat "$WORK/go/$name/stage")" = built ]; then
    timeout "$TIMEOUT" "$WORK/go/$name/program" >"$result.go.out" 2>"$result.go.err"
    echo "$?" >"$result.go.status"
  fi
done

printf '| program | status | detail |\n|---|---|---|\n'
: >"$WORK/statuses.txt"
for name in "${names[@]}"; do
  status="$(classify "$name")"
  echo "$status" >>"$WORK/statuses.txt"
  printf '| %s | %s | %s |\n' "$name" "$status" "$(detail "$name" "$status" | sed 's/|/\\|/g')"
done
echo
echo "summary:"
sort "$WORK/statuses.txt" | uniq -c | sort -rn
! grep -qvE '^(OK|FLOAT CLOSE)$' "$WORK/statuses.txt"
