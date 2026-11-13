#!/usr/bin/env bash
#
# Compiles the Markgraf CLI (Main.run) with `iris go` and checks that the Go
# binary writes byte-identical SVG to the JavaScript CLI for real .markgraf
# files: a `--still` and a `--frame` export of each, plus stdout, stderr and
# exit status. Prints one line per export with both run times.
#
#   compiler-backend/go/scripts/markgraf/compare-svg.sh            # default files
#   compiler-backend/go/scripts/markgraf/compare-svg.sh a.markgraf # chosen files
#
# Environment: IRIS, MARKGRAF (checkout), GO_SUPPORT, MARKGRAF_JS (a JS CLI;
# built from the current sources with build-js-cli.sh when unset), WORK,
# TIMEOUT (seconds per run, default 600), KEEP=1 keeps the work directory.
# Finally checks the generated Go against the markgraf-cli quality baseline and
# the time `iris go` takes against the compile-time baseline (compile-time.sh).

set -uo pipefail
export LC_ALL=C

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../../../.." && pwd)"
IRIS="${IRIS:-$ROOT/target/release/iris}"
MARKGRAF="${MARKGRAF:-/Users/mark/Developer/markgraf}"
GO_SUPPORT="${GO_SUPPORT:-/Users/mark/Developer/purs-backend-go/go-support}"
WORK="${WORK:-$(mktemp -d)}"
TIMEOUT="${TIMEOUT:-600}"
SLOWER_PERCENT="${SLOWER_PERCENT:-5}"
SLOWER_MS="${SLOWER_MS:-10}"

milliseconds() { perl -MTime::HiRes=time -e 'printf "%.0f", time*1000'; }

if [ -z "${MARKGRAF_JS:-}" ]; then
  MARKGRAF_JS="$("$HERE/build-js-cli.sh" "$WORK/js")" || exit 1
fi

mkdir -p "$WORK/out"
MARKGRAF_GO="$(IRIS="$IRIS" MARKGRAF="$MARKGRAF" GO_SUPPORT="$GO_SUPPORT" "$HERE/build-go-cli.sh" "$WORK/go")" || exit 1

if [ $# -eq 0 ]; then
  set -- "$MARKGRAF"/examples/*.markgraf "$MARKGRAF"/npm/test/Animation/*.markgraf \
    "$MARKGRAF"/npm/test/Animation/EdgeLabels/*.markgraf "$MARKGRAF"/npm/test/Animation/Sequence/*.markgraf
fi

run() { # implementation input mode output → status and time in $WORK/out
  local cli="$1" input="$2" output="$3"; shift 3
  local started finished status
  started=$(milliseconds)
  (cd "$WORK/out" && timeout "$TIMEOUT" "$cli" "$input" "$@" -o "$output" \
    >"$output.stdout" 2>"$output.stderr")
  status=$?
  finished=$(milliseconds)
  echo "$status" > "$output.status"
  echo $((finished - started))
}

normalise() { sed -e "s|$WORK/out/||g" "$1"; }

run "$MARKGRAF_JS" "$1" "$WORK/out/warm-up.js.svg" --still "" >/dev/null
run "$MARKGRAF_GO" "$1" "$WORK/out/warm-up.go.svg" --still "" >/dev/null

passed=0 failed=0 slower=0 js_total=0 go_total=0 worst_ratio=0 worst=""
printf '%-44s %-7s %-9s %8s %8s %6s\n' file mode result js_ms go_ms go/js
for input in "$@"; do
  name="$(basename "$input" .markgraf)"
  for mode in still frame; do
    case "$mode" in
      still) arguments=(--still "") ;;
      frame) arguments=(--frame 1) ;;
    esac
    js="$WORK/out/$name.$mode.js.svg" go="$WORK/out/$name.$mode.go.svg"
    js_ms=$(run "$MARKGRAF_JS" "$input" "$js" "${arguments[@]}")
    go_ms=$(run "$MARKGRAF_GO" "$input" "$go" "${arguments[@]}")
    result=identical
    if [ "$(cat "$js.status")" != "$(cat "$go.status")" ]; then
      result="status $(cat "$js.status")/$(cat "$go.status")"
    elif ! cmp -s <(normalise "$js.stdout" | sed 's/\.js\.svg/.svg/') <(normalise "$go.stdout" | sed 's/\.go\.svg/.svg/'); then
      result=stdout
    elif ! cmp -s <(normalise "$js.stderr") <(normalise "$go.stderr"); then
      result=stderr
    elif [ -e "$js" ] || [ -e "$go" ]; then
      cmp -s "$js" "$go" || result=svg
    fi
    [ "$(cat "$js.status")" = 0 ] || [ "$result" != identical ] || result="identical (exit $(cat "$js.status"))"
    case "$result" in identical*) passed=$((passed + 1)) ;; *) failed=$((failed + 1)) ;; esac
    if [ $((go_ms * 100)) -gt $((js_ms * (100 + SLOWER_PERCENT) + SLOWER_MS * 100)) ]; then
      js_again=$(run "$MARKGRAF_JS" "$input" "$js" "${arguments[@]}")
      go_again=$(run "$MARKGRAF_GO" "$input" "$go" "${arguments[@]}")
      js_ms=$((js_again < js_ms ? js_again : js_ms)) go_ms=$((go_again < go_ms ? go_again : go_ms))
    fi
    js_total=$((js_total + js_ms)) go_total=$((go_total + go_ms))
    ratio=$(awk -v go="$go_ms" -v js="$js_ms" 'BEGIN { printf "%.2f", go / (js > 0 ? js : 1) }')
    if awk -v ratio="$ratio" -v worst="$worst_ratio" 'BEGIN { exit !(ratio > worst) }'; then
      worst_ratio=$ratio worst="$name $mode"
    fi
    if [ $((go_ms * 100)) -gt $((js_ms * (100 + SLOWER_PERCENT) + SLOWER_MS * 100)) ]; then
      slower=$((slower + 1))
      ratio="$ratio SLOWER"
    fi
    printf '%-44s %-7s %-9s %8s %8s %6s\n' "$name" "$mode" "$result" "$js_ms" "$go_ms" "$ratio"
  done
done
echo "Markgraf SVG: $passed identical, $failed different (work directory $WORK)"
total_ratio=$(awk -v go="$go_total" -v js="$js_total" 'BEGIN { printf "%.2f", go / (js > 0 ? js : 1) }')
echo "Markgraf time: JavaScript $js_total ms, Go $go_total ms (Go/JS $total_ratio), worst Go/JS $worst_ratio ($worst)"
if [ "$slower" -ne 0 ]; then
  echo "Markgraf time: Go is slower than JavaScript beyond $SLOWER_PERCENT% + $SLOWER_MS ms on $slower exports"
  failed=$((failed + 1))
fi
"$HERE/../quality.sh" markgraf-cli "$WORK/go" || failed=$((failed + 1))
IRIS="$IRIS" MARKGRAF="$MARKGRAF" WORK="$WORK/compile-time" "$HERE/compile-time.sh" || failed=$((failed + 1))
[ "${KEEP:-0}" = 1 ] || [ "$failed" -ne 0 ] || rm -rf "$WORK"
[ "$failed" -eq 0 ]
