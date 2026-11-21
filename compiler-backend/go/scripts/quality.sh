#!/usr/bin/env bash
#
# Measures escape hatches, readability and size (lines, functions) in generated
# Go. The escape hatches (any and its causes, empty interfaces, type
# assertions, reflect, unsafe, panic) ratchet against
# compiler-backend/go/quality-baseline.txt: a scope fails when one rises above
# its baseline, and asks for the baseline to be lowered when one drops below
# it. The other metrics are printed for information and never fail.
#
#   compiler-backend/go/scripts/quality.sh SCOPE DIR...           # check
#   compiler-backend/go/scripts/quality.sh --update SCOPE DIR...  # lower baseline
#   compiler-backend/go/scripts/quality.sh --lint DIR...          # gofmt -s, staticcheck
#
# SCOPE names a row group in the baseline (e.g. examples, markgraf-cli). DIR
# holds generated .go files, searched recursively. --update only ever lowers
# numbers; raising one requires editing the baseline by hand in a reviewed
# change that says why.

set -uo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
BASELINE="${BASELINE:-$HERE/../quality-baseline.txt}"

update=0
lint=0
case "${1:-}" in
  --update) update=1; shift ;;
  --lint) lint=1; shift ;;
esac
if [ "$lint" = 1 ]; then
  [ "$#" -gt 0 ] || { echo "quality.sh: no directories given" >&2; exit 2; }
  unformatted="$(find "$@" -name '*.go' -type f -exec gofmt -s -l {} +)"
  echo "gofmt -s would change $(printf '%s' "$unformatted" | grep -c .) files"
  printf '%s\n' "$unformatted" | grep . | head -20
  if command -v staticcheck >/dev/null 2>&1; then
    for dir in "$@"; do
      (cd "$dir" && staticcheck ./... 2>&1 | head -40)
    done
  else
    echo "staticcheck is not installed; only gofmt was run"
  fi
  exit 0
fi
scope="${1:?usage: quality.sh [--update|--lint] SCOPE DIR...}"
shift
[ "$#" -gt 0 ] || { echo "quality.sh: no directories given" >&2; exit 2; }
for dir in "$@"; do
  [ -d "$dir" ] || { echo "quality.sh: no directory $dir" >&2; exit 2; }
done

files() { find "$@" -name '*.go' -type f -print0; }

count() {
  files "$@" | xargs -0 cat | perl -ne "$PATTERN"
}

causes() {
  find "$@" -name compile.log -type f -exec cat {} + 2>/dev/null \
    | awk '$1 == "any-cause" { n[$2] += $3 } END { for (c in n) print "any:" c, n[c] }' | sort
}

measure() {
  local dirs=("$@")
  # Each metric is a perl snippet that adds its matches to $n and prints at END.
  PATTERN='s/\[([^\[\]]*)\]/"[" . ($1 =~ s{\b\w+(?:\s*,\s*\w+)*\s+any\b}{}gr) . "]"/ge; $n += () = /\bany\b/g; END { print $n+0, "\n" }' count "${dirs[@]}" | sed 's/^/any /'
  causes "${dirs[@]}"
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
  PATTERN='$n++ if /^func [Cc]onvert\d*\(/; END { print $n+0, "\n" }' count "${dirs[@]}" | sed 's/^/converters /'
  PATTERN='$n++ if /^\s*Origin\s+any\b/; END { print $n+0, "\n" }' count "${dirs[@]}" | sed 's/^/origin-fields /'
  PATTERN='if (/^type (\w+)/) { $n = length($1) if length($1) > $n } END { print $n+0, "\n" }' count "${dirs[@]}" | sed 's/^/max-identifier /'
  PATTERN='if (/^(\t+)/) { $n = length($1) if length($1) > $n } END { print $n+0, "\n" }' count "${dirs[@]}" | sed 's/^/max-nesting /'
}

ratcheted() {
  case "$1" in
    any | any:* | empty-interface | type-assertion | reflect | unsafe | panic) return 0 ;;
  esac
  return 1
}

baseline_value() {
  awk -v s="$scope" -v m="$1" '$1 == s && $2 == m { print $3 }' "$BASELINE" 2>/dev/null
}

current="$(measure "$@")"

status=0
lowered=()
printf '%-16s %10s %10s\n' "$scope" "baseline" "current"
while read -r metric value; do
  if ! ratcheted "$metric"; then
    printf '%-16s %10s %10s  (info)\n' "$metric" "" "$value"
    continue
  fi
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
