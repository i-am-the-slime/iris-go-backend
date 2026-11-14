#!/usr/bin/env bash
#
# Compiles purs-backend-go's example projects with `iris go`, builds each with
# `go build`, runs it, and compares stdout with the expectation recorded in
# purs-backend-go's examples/run.sh.
#
#   compiler-backend/go/scripts/run-examples.sh               # every example
#   compiler-backend/go/scripts/run-examples.sh Tco01 Array01 # selected examples
#   KEEP=1 ...                                                # keep generated Go
#
# Environment: IRIS (compiler binary), EXAMPLES (purs-backend-go/examples),
# GO_SUPPORT (purs-backend-go/go-support), JOBS (parallel workers).

set -uo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../../.." && pwd)"
IRIS="${IRIS:-$ROOT/target/release/iris}"
EXAMPLES="${EXAMPLES:-/Users/mark/Developer/purs-backend-go/examples}"
GO_SUPPORT="${GO_SUPPORT:-/Users/mark/Developer/purs-backend-go/go-support}"
JOBS="${JOBS:-8}"
WORK="${WORK:-$(mktemp -d)}"
mkdir -p "$WORK"

run_one() {
  local line name entry kind expected
  eval "line=\"$1\""
  IFS='|' read -r name entry kind expected <<< "$line"
  expected="$(printf '%b' "$expected")"
  local project="$EXAMPLES/$name" out="$WORK/$name"
  mkdir -p "$out"
  cat > "$out/go.mod" <<GOMOD
module example.com/t

go 1.23.2

require github.com/i-am-the-slime/purs-backend-go/go-support v0.0.0

replace github.com/i-am-the-slime/purs-backend-go/go-support => $GO_SUPPORT
GOMOD
  local started finished
  started=$(perl -MTime::HiRes=time -e 'printf "%.0f", time*1000')
  if ! (cd "$project" && timeout 120 "$IRIS" go --entry "$entry" "$out") >"$out/compile.log" 2>&1; then
    printf '%-26s %-8s %6s  %s\n' "$name" "COMPILE" "-" "$(grep -v '^go:' "$out/compile.log" | head -1 | cut -c1-150)"
    return 1
  fi
  finished=$(perl -MTime::HiRes=time -e 'printf "%.0f", time*1000')
  local elapsed=$((finished - started))
  if ! (cd "$out" && go build -gcflags="-c=$(sysctl -n hw.ncpu) -dwarf=false" -ldflags=-w -o program . ) >"$out/build.log" 2>&1; then
    printf '%-26s %-8s %6s  %s\n' "$name" "GO" "$elapsed" "$(grep -m1 -v '^#' "$out/build.log" | cut -c1-150)"
    return 1
  fi
  local actual
  actual="$("$out/program" 2>"$out/run.log")"
  if [ "$actual" != "$expected" ]; then
    printf '%-26s %-8s %6s  got %s\n' "$name" "OUTPUT" "$elapsed" "$(printf '%s' "$actual" | tr '\n' '/' | cut -c1-120)"
    return 1
  fi
  printf '%-26s %-8s %6s\n' "$name" "PASS" "$elapsed"
}
export -f run_one
export IRIS EXAMPLES GO_SUPPORT WORK

manifest() {
  grep -E '^  "[A-Za-z0-9_]+\|[^|]+\|(value|effect|program)\|' "$EXAMPLES/run.sh" | sed -E 's/^  "//; s/"$//'
}

selected() {
  if [ "$#" -eq 0 ]; then
    manifest
  else
    for name in "$@"; do manifest | grep -E "^$name\|"; done
  fi
}

selected "$@" > "$WORK/manifest.txt"
run_numbered() { run_one "$(sed -n "$1p" "$WORK/manifest.txt")"; }
export -f run_numbered
started=$(perl -MTime::HiRes=time -e 'printf "%.0f", time*1000')
seq 1 "$(wc -l < "$WORK/manifest.txt")" | xargs -P "$JOBS" -I{} bash -c 'run_numbered "$1"' _ {} | sort > "$WORK/results.txt"
finished=$(perl -MTime::HiRes=time -e 'printf "%.0f", time*1000')
cat "$WORK/results.txt"
passed=$(grep -c ' PASS ' "$WORK/results.txt")
total=$(wc -l < "$WORK/results.txt" | tr -d ' ')
echo "passed $passed/$total in $((finished - started)) ms (generated Go in $WORK)"
status=0
[ "$passed" = "$total" ] || status=1
if [ "$#" -eq 0 ]; then
  echo
  "$HERE/quality.sh" examples "$WORK" || status=1
fi
[ "${KEEP:-0}" = 1 ] || [ "$#" -gt 0 ] || rm -rf "$WORK"
exit "$status"
