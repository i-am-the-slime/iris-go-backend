#!/usr/bin/env bash
#
# Measures how much work `iris go` does to compile the Markgraf CLI (Main.run)
# and ratchets it against compiler-backend/go/compile-time-baseline.txt: the
# check fails when the work rises beyond the margin, and asks for the baseline
# to be lowered when it drops well below it.
#
#   compiler-backend/go/scripts/markgraf/compile-time.sh           # check
#   compiler-backend/go/scripts/markgraf/compile-time.sh --update  # record
#
# The work is the instructions the iris process retires (`/usr/bin/time -l` on
# macOS), which does not move with other work on the machine the way CPU time
# does, and the best of RUNS compilations, so that one odd run does not fail
# the check. The CPU seconds of that run are printed for information only.
# --update only ever lowers the baseline; raising it is a hand edit in a
# reviewed change that says why.
#
# Environment: IRIS, MARKGRAF (checkout; pinned.sh), RUNS (default 3),
# MARGIN_PERCENT (default 5), WORK.

set -uo pipefail
export LC_ALL=C

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../../../.." && pwd)"
IRIS="${IRIS:-$ROOT/target/release/iris}"
source "$(dirname "${BASH_SOURCE[0]}")/pinned.sh"
BASELINE="${BASELINE:-$HERE/../../compile-time-baseline.txt}"
RUNS="${RUNS:-3}"
MARGIN_PERCENT="${MARGIN_PERCENT:-5}"
WORK="${WORK:-$(mktemp -d)}"
SCOPE=markgraf-cli
mkdir -p "$WORK/go"
# The generated packages import each other through the module go.mod names.
printf 'module markgraf.example/cli\n\ngo 1.27.0\n' > "$WORK/go/go.mod"

update=0
[ "${1:-}" = "--update" ] && update=1

measure() { # → "instructions cpu-seconds" of one compilation
  local timing="$WORK/time.txt"
  (cd "$MARKGRAF/cli" && /usr/bin/time -l "$IRIS" go --entry Main.run "$WORK/go") \
    >/dev/null 2>"$timing" || { cat "$timing" >&2; return 1; }
  awk '/instructions retired/ { instructions = $1 }
       $2 == "real" && $4 == "user" && $6 == "sys" { cpu = $3 + $5 }
       END { if (instructions == "") exit 1; printf "%.0f %.2f\n", instructions, cpu }' "$timing" \
    || { echo "compile-time.sh: no instruction count in /usr/bin/time -l output" >&2; cat "$timing" >&2; return 1; }
}

best="" best_cpu=""
for _ in $(seq 1 "$RUNS"); do
  measured="$(measure)" || exit 1
  read -r instructions cpu <<< "$measured"
  if [ -z "$best" ] || awk -v a="$instructions" -v b="$best" 'BEGIN { exit !(a < b) }'; then
    best="$instructions"
    best_cpu="$cpu"
  fi
done

giga() { if [ -n "${1:-}" ]; then awk -v n="$1" 'BEGIN { printf "%.2f G", n / 1e9 }'; else echo "-"; fi; }

base="$(awk -v s="$SCOPE" '$1 == s { print $2 }' "$BASELINE" 2>/dev/null)"
limit="$(awk -v b="${base:-0}" -v p="$MARGIN_PERCENT" 'BEGIN { printf "%.0f", b * (100 + p) / 100 }')"
status=0
if [ -z "$base" ]; then
  mark="(new: record with --update)"
elif awk -v a="$best" -v l="$limit" 'BEGIN { exit !(a > l) }'; then
  mark="REGRESSION (limit $(giga "$limit"))"
  status=1
elif awk -v a="$best" -v b="$base" -v p="$MARGIN_PERCENT" 'BEGIN { exit !(a * (100 + p) / 100 < b) }'; then
  mark="improved: lower the baseline with --update"
else
  mark="(limit $(giga "$limit"))"
fi
echo "Markgraf CLI compile time: $(giga "$best") instructions retired (best of $RUNS), baseline $(giga "$base") $mark; ${best_cpu} s CPU (informational)"

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
    echo "compile-time.sh: baseline for $SCOPE is now $best instructions ($(giga "$best"))"
  fi
fi
[ "${KEEP:-0}" = 1 ] || rm -rf "$WORK"
exit "$status"
