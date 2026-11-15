#!/usr/bin/env bash
#
# Ratchets the size of the Go backend's own source, the lines of
# compiler-backend/go/src/**/*.rs, against the `go-backend source-lines` row of
# compiler-backend/go/quality-baseline.txt: it fails when the source grows
# beyond the baseline, and asks for the baseline to be lowered when it shrinks.
#
#   compiler-backend/go/scripts/source-size.sh           # check
#   compiler-backend/go/scripts/source-size.sh --update  # lower the baseline
#
# --update only ever lowers the number; raising it is a hand edit in a
# reviewed change that says why the backend has to grow.

set -uo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
SOURCE="${SOURCE:-$HERE/../src}"
BASELINE="${BASELINE:-$HERE/../quality-baseline.txt}"
SCOPE=go-backend
METRIC=source-lines

current="$(find "$SOURCE" -name '*.rs' -type f -print0 | xargs -0 cat | wc -l | tr -d ' ')"
base="$(awk -v s="$SCOPE" -v m="$METRIC" '$1 == s && $2 == m { print $3 }' "$BASELINE" 2>/dev/null)"

status=0
if [ -z "$base" ]; then
  mark="  (new: add to baseline with --update)"
elif [ "$current" -gt "$base" ]; then
  mark="  REGRESSION (+$((current - base)))"
  status=1
elif [ "$current" -lt "$base" ]; then
  mark="  improved (-$((base - current))): lower the baseline with --update"
else
  mark=""
fi
printf '%-16s %10s %10s\n' "$SCOPE" "baseline" "current"
printf '%-16s %10s %10s%s\n' "$METRIC" "${base:--}" "$current" "$mark"

if [ "${1:-}" = "--update" ]; then
  if [ "$status" != 0 ]; then
    echo "source-size.sh: refusing to update while the source grew; shrink it instead" >&2
    exit 1
  fi
  touch "$BASELINE"
  awk -v s="$SCOPE" -v m="$METRIC" '!($1 == s && $2 == m)' "$BASELINE" > "$BASELINE.tmp"
  printf '%s %s %s\n' "$SCOPE" "$METRIC" "$current" >> "$BASELINE.tmp"
  sort -o "$BASELINE" "$BASELINE.tmp" && rm "$BASELINE.tmp"
  echo "baseline updated: $BASELINE"
  exit 0
fi

[ "$status" = 0 ] || echo "source-size.sh: the backend source grew past $BASELINE" >&2
exit "$status"
