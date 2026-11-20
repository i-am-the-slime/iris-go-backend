#!/usr/bin/env bash
#
# Records the Go that `iris go` generates for the Markgraf CLI and every
# example, or checks that the current compiler still generates exactly that.
# A refactoring that must not change behaviour records with the old binary and
# checks with the new one.
#
#   compiler-backend/go/scripts/same-output.sh record DIR   # write DIR
#   compiler-backend/go/scripts/same-output.sh check DIR    # diff against DIR
#
# Environment: IRIS (compiler binary), EXAMPLES (iris-go/examples),
# MARKGRAF (checkout; pinned.sh), JOBS (parallel workers).

set -uo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../../.." && pwd)"
IRIS="${IRIS:-$ROOT/target/release/iris}"
EXAMPLES="${EXAMPLES:-/Users/mark/Developer/iris-go/examples}"
JOBS="${JOBS:-8}"
source "$HERE/markgraf/pinned.sh"

mode="${1:-}"
target="${2:-}"
if [ -z "$target" ] || { [ "$mode" != record ] && [ "$mode" != check ]; }; then
  echo "usage: same-output.sh record|check DIR" >&2
  exit 2
fi

generate() {
  local out="$1"
  rm -rf "$out"
  mkdir -p "$out/markgraf" "$out/examples"
  printf 'module markgraf.example/cli\n\ngo 1.27.0\n' > "$out/markgraf/go.mod"
  (cd "$MARKGRAF/cli" && "$IRIS" go --entry Main.run "$out/markgraf") >"$out/markgraf.log" 2>&1 \
    || echo "markgraf: iris go failed (see $out/markgraf.log)"
  cut -d'|' -f1,2 "$EXAMPLES/examples.txt" | tr '|' ' ' \
    | OUT="$out" EXAMPLES="$EXAMPLES" IRIS="$IRIS" xargs -P "$JOBS" -n 2 sh -c '
        name="$0"; entry="$1"; dir="$OUT/examples/$name"
        mkdir -p "$dir"
        printf "module example.com/t\n\ngo 1.27.0\n" > "$dir/go.mod"
        (cd "$EXAMPLES/$name" && "$IRIS" go --entry "$entry" "$dir") >"$dir.log" 2>&1 \
          || echo "$name: iris go failed"
      '
}

if [ "$mode" = record ]; then
  generate "$target"
  echo "recorded $(find "$target" -name '*.go' | wc -l | tr -d ' ') Go files in $target"
  exit 0
fi

current="$(mktemp -d)"
generate "$current"
if diff -r -q -x '*.log' "$target" "$current" > "$current.diff"; then
  echo "same output: $(find "$current" -name '*.go' | wc -l | tr -d ' ') Go files identical"
  rm -rf "$current" "$current.diff"
  exit 0
fi
echo "output differs ($(wc -l < "$current.diff" | tr -d ' ') files); first differences:"
head -10 "$current.diff"
first="$(grep -m1 '^Files ' "$current.diff" | awk '{print $2" "$4}')"
[ -n "$first" ] && diff -u $first | head -40
echo "current output kept in $current"
exit 1
