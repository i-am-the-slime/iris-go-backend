#!/usr/bin/env bash
#
# Measures escape hatches and size (lines, functions) in generated Go, and
# ratchets them against compiler-backend/go/quality-baseline.txt: a scope fails
# when any metric rises above its baseline, and asks for the baseline to be
# lowered when one drops below it.
#
#   compiler-backend/go/scripts/quality.sh SCOPE DIR...           # check
#   compiler-backend/go/scripts/quality.sh --update SCOPE DIR...  # lower baseline
#
# SCOPE names a row group in the baseline (e.g. examples, markgraf-cli). DIR
# holds generated .go files, searched recursively. --update only ever lowers
# numbers; raising one requires editing the baseline by hand in a reviewed
# change that says why.

set -uo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
BASELINE="${BASELINE:-$HERE/../quality-baseline.txt}"

update=0
if [ "${1:-}" = "--update" ]; then
  update=1
  shift
fi
scope="${1:?usage: quality.sh [--update] SCOPE DIR...}"
shift
[ "$#" -gt 0 ] || { echo "quality.sh: no directories given" >&2; exit 2; }
for dir in "$@"; do
  [ -d "$dir" ] || { echo "quality.sh: no directory $dir" >&2; exit 2; }
done

files() { find "$@" -name '*.go' -type f -print0; }

count() {
  files "$@" | xargs -0 cat | perl -ne "$PATTERN"
}

measure() {
  local dirs=("$@")
  # Each metric is a perl snippet that adds its matches to $n and prints at END.
  PATTERN='$n += () = /\bany\b/g; END { print $n+0, "\n" }' count "${dirs[@]}" | sed 's/^/any /'
  PATTERN='$n += () = /\binterface\s*\{\s*\}/g; END { print $n+0, "\n" }' count "${dirs[@]}" | sed 's/^/empty-interface /'
  PATTERN='$n += () = /\.\((?!type\))[A-Za-z_*\[]/g; END { print $n+0, "\n" }' count "${dirs[@]}" | sed 's/^/type-assertion /'
  PATTERN='$n += () = /\breflect\./g; END { print $n+0, "\n" }' count "${dirs[@]}" | sed 's/^/reflect /'
  PATTERN='$n += () = /\bunsafe\./g; END { print $n+0, "\n" }' count "${dirs[@]}" | sed 's/^/unsafe /'
  PATTERN='$n += () = /\bfunc\(\)\s*[^{(,]*\{/g; END { print $n+0, "\n" }' count "${dirs[@]}" | sed 's/^/thunk /'
  PATTERN='$n += () = /\bpanic\(/g; END { print $n+0, "\n" }' count "${dirs[@]}" | sed 's/^/panic /'
  # Size: every line Go parses, and every function it compiles, top-level or
  # literal; a literal is `func(` not in a type (after `]`, `) ` or a name)
  # whose signature ends in `{`.
  PATTERN='$n++; END { print $n+0, "\n" }' count "${dirs[@]}" | sed 's/^/lines /'
  PATTERN='$n++ if /^func /;
    $n += () = /(?<![\]\w])(?<!\) )func(\((?:[^()]++|(?1))*\))(?:struct\{\}|[^(){};\n]|(?1))*\{(?!\})/g;
    END { print $n+0, "\n" }' count "${dirs[@]}" | sed 's/^/funcs /'
}

baseline_value() {
  awk -v s="$scope" -v m="$1" '$1 == s && $2 == m { print $3 }' "$BASELINE" 2>/dev/null
}

current="$(measure "$@")"

status=0
lowered=()
printf '%-16s %10s %10s\n' "$scope" "baseline" "current"
while read -r metric value; do
  base="$(baseline_value "$metric")"
  mark=""
  if [ -z "$base" ]; then
    mark="  (new: add to baseline with --update)"
    lowered+=("$metric $value")
  elif [ "$value" -gt "$base" ]; then
    mark="  REGRESSION (+$((value - base)))"
    status=1
  elif [ "$value" -lt "$base" ]; then
    mark="  improved (-$((base - value))): lower the baseline with --update"
    lowered+=("$metric $value")
  fi
  printf '%-16s %10s %10s%s\n' "$metric" "${base:--}" "$value" "$mark"
done <<< "$current"

if [ "$update" = 1 ]; then
  if [ "$status" != 0 ]; then
    echo "quality.sh: refusing to update while a metric regressed; fix the regression instead" >&2
    exit 1
  fi
  touch "$BASELINE"
  for entry in "${lowered[@]}"; do
    read -r metric value <<< "$entry"
    awk -v s="$scope" -v m="$metric" '!($1 == s && $2 == m)' "$BASELINE" > "$BASELINE.tmp"
    printf '%s %s %s\n' "$scope" "$metric" "$value" >> "$BASELINE.tmp"
    sort -o "$BASELINE" "$BASELINE.tmp" && rm "$BASELINE.tmp"
  done
  echo "baseline updated: $BASELINE"
  exit 0
fi

[ "$status" = 0 ] || echo "quality.sh: $scope regressed against $BASELINE" >&2
exit "$status"
