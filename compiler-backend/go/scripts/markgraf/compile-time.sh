#!/usr/bin/env bash
#
# Measures how long `iris go` takes to compile the Markgraf CLI (Main.run) and
# ratchets it against compiler-backend/go/compile-time-baseline.txt: the check
# fails when the time rises beyond the margin, and asks for the baseline to be
# lowered when it drops well below it.
#
#   compiler-backend/go/scripts/markgraf/compile-time.sh           # check
#   compiler-backend/go/scripts/markgraf/compile-time.sh --update  # record
#
# The time is the user + system CPU time of the iris process, not wall-clock
# time, so that other work on the machine does not count, and the best of RUNS
# compilations, so that one disturbed run does not fail the check. --update
# only ever lowers the baseline; raising it is a hand edit in a reviewed change
# that says why.
#
# Environment: IRIS, MARKGRAF (checkout; pinned.sh), RUNS (default 3), MARGIN_PERCENT
# (default 20), MARGIN_SECONDS (default 0.2), WORK.

set -uo pipefail
export LC_ALL=C

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../../../.." && pwd)"
IRIS="${IRIS:-$ROOT/target/release/iris}"
source "$(dirname "${BASH_SOURCE[0]}")/pinned.sh"
BASELINE="${BASELINE:-$HERE/../../compile-time-baseline.txt}"
RUNS="${RUNS:-3}"
MARGIN_PERCENT="${MARGIN_PERCENT:-20}"
MARGIN_SECONDS="${MARGIN_SECONDS:-0.2}"
WORK="${WORK:-$(mktemp -d)}"
SCOPE=markgraf-cli
mkdir -p "$WORK/go"
# The generated packages import each other through the module go.mod names.
printf 'module markgraf.example/cli\n\ngo 1.27.0\n' > "$WORK/go/go.mod"

update=0
[ "${1:-}" = "--update" ] && update=1

cpu_seconds() { # → user + sys seconds of one compilation
  local timing="$WORK/time.txt"
  (cd "$MARKGRAF/cli" && /usr/bin/time -p "$IRIS" go --entry Main.run "$WORK/go") \
    >/dev/null 2>"$timing" || { cat "$timing" >&2; return 1; }
  awk '$1 == "user" || $1 == "sys" { total += $2 } END { printf "%.2f\n", total }' "$timing"
}

best=""
for _ in $(seq 1 "$RUNS"); do
  seconds="$(cpu_seconds)" || exit 1
  if [ -z "$best" ] || awk -v a="$seconds" -v b="$best" 'BEGIN { exit !(a < b) }'; then
    best="$seconds"
  fi
done

base="$(awk -v s="$SCOPE" '$1 == s { print $2 }' "$BASELINE" 2>/dev/null)"
limit="$(awk -v b="${base:-0}" -v p="$MARGIN_PERCENT" -v s="$MARGIN_SECONDS" \
  'BEGIN { printf "%.2f", b * (100 + p) / 100 + s }')"
status=0
if [ -z "$base" ]; then
  mark="(new: record with --update)"
elif awk -v a="$best" -v l="$limit" 'BEGIN { exit !(a > l) }'; then
  mark="REGRESSION (limit $limit s)"
  status=1
elif awk -v a="$best" -v b="$base" -v p="$MARGIN_PERCENT" 'BEGIN { exit !(a * (100 + p) / 100 < b) }'; then
  mark="improved: lower the baseline with --update"
else
  mark="(limit $limit s)"
fi
echo "Markgraf CLI compile time: ${best} s CPU (best of $RUNS), baseline ${base:--} s $mark"

if [ "$update" = 1 ]; then
  if [ "$status" != 0 ]; then
    echo "compile-time.sh: refusing to raise the baseline; fix the regression instead" >&2
    exit 1
  fi
  if [ -z "$base" ] || awk -v a="$best" -v b="$base" 'BEGIN { exit !(a < b) }'; then
    touch "$BASELINE"
    grep -v "^$SCOPE " "$BASELINE" > "$WORK/baseline.txt"
    echo "$SCOPE $best" >> "$WORK/baseline.txt"
    sort "$WORK/baseline.txt" > "$BASELINE"
    echo "compile-time.sh: baseline for $SCOPE is now $best s"
  fi
fi
[ "${KEEP:-0}" = 1 ] || rm -rf "$WORK"
exit "$status"
