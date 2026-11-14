#!/usr/bin/env bash
#
# Runs the Markgraf CLI in four implementations on the same .markgraf files and
# checks that all of them write the same bytes (SVG, stdout, stderr, exit
# status) as the Tauri reference, then prints a per-export timing table, the
# totals, each runtime's time relative to Go, and the heaviest exports.
#
#   tauri  build-js-cli.sh: engine.js in the Rust tauri-native-host (JavaScriptCore on macOS)
#   deno   the same engine.js under Deno (V8) through js-host/host.js
#   bun    the same engine.js under Bun (JavaScriptCore) through js-host/host.js
#   go     build-go-cli.sh: Main.run compiled by `iris go`
#
#   compiler-backend/go/scripts/markgraf/compare-js-runtimes.sh            # default files
#   compiler-backend/go/scripts/markgraf/compare-js-runtimes.sh a.markgraf # chosen files
#
# Environment: IRIS, MARKGRAF (checkout; pinned.sh), GO_SUPPORT, MARKGRAF_GO (a Go CLI;
# built with build-go-cli.sh when unset), WORK, TIMEOUT (seconds per run,
# default 600), KEEP=1 keeps the work directory. Timing follows compare-svg.sh:
# one warm-up run each, and an export where Go looks slower than a JavaScript
# runtime beyond SLOWER_PERCENT% + SLOWER_MS is run again, keeping the minima.
#
# Other benchmarks on the machine wait for this script by its name.

set -uo pipefail
export LC_ALL=C

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
source "$(dirname "${BASH_SOURCE[0]}")/pinned.sh"
WORK="${WORK:-$(mktemp -d)}"
TIMEOUT="${TIMEOUT:-600}"
SLOWER_PERCENT="${SLOWER_PERCENT:-5}"
SLOWER_MS="${SLOWER_MS:-10}"
RUNTIMES=(tauri deno bun go)

milliseconds() { perl -MTime::HiRes=time -e 'printf "%.0f", time*1000'; }

TAURI="$("$HERE/build-js-cli.sh" "$WORK/js")" || exit 1
ENGINE="$WORK/js/dist/engine.js"
MEASURE="$("$HERE/build-js-measure.sh" "$WORK/js")" || exit 1
GO="${MARKGRAF_GO:-$("$HERE/build-go-cli.sh" "$WORK/go")}" || exit 1
HOST="$HERE/js-host/host.js"

mkdir -p "$WORK/out"
if [ $# -eq 0 ]; then
  set -- "$MARKGRAF"/examples/*.markgraf "$MARKGRAF"/npm/test/Animation/*.markgraf \
    "$MARKGRAF"/npm/test/Animation/EdgeLabels/*.markgraf "$MARKGRAF"/npm/test/Animation/Sequence/*.markgraf
fi

command_of() { # runtime → the command line that runs the CLI
  case "$1" in
    tauri) echo "$TAURI" ;;
    deno) echo deno run --allow-all --no-config --no-lock --quiet "$HOST" "$ENGINE" "$MEASURE" -- ;;
    bun) echo bun "$HOST" "$ENGINE" "$MEASURE" -- ;;
    go) echo "$GO" ;;
  esac
}

run() { # runtime input output arguments… → milliseconds; status, stdout, stderr next to output
  local runtime="$1" input="$2" output="$3"; shift 3
  local started finished status command
  read -r -a command <<<"$(command_of "$runtime")"
  started=$(milliseconds)
  (cd "$WORK/out" && timeout "$TIMEOUT" "${command[@]}" "$input" "$@" -o "$output" \
    >"$output.stdout" 2>"$output.stderr")
  status=$?
  finished=$(milliseconds)
  echo "$status" > "$output.status"
  echo $((finished - started))
}

normalise() { sed -e "s|$WORK/out/||g" -e "s/\\.$2\\.svg/.svg/g" "$1"; }

difference() { # reference runtime output-stem → empty when identical
  local reference="$1.$2.svg" other="$1.$3.svg"
  if [ "$(cat "$reference.status")" != "$(cat "$other.status")" ]; then
    echo "$3:status"
  elif ! cmp -s <(normalise "$reference.stdout" "$2") <(normalise "$other.stdout" "$3"); then
    echo "$3:stdout"
  elif ! cmp -s <(normalise "$reference.stderr" "$2") <(normalise "$other.stderr" "$3"); then
    echo "$3:stderr"
  elif { [ -e "$reference" ] || [ -e "$other" ]; } && ! cmp -s "$reference" "$other"; then
    echo "$3:svg"
  fi
}

slower() { [ $(($1 * 100)) -gt $(($2 * (100 + SLOWER_PERCENT) + SLOWER_MS * 100)) ]; }

for runtime in "${RUNTIMES[@]}"; do
  run "$runtime" "$1" "$WORK/out/warm-up.$runtime.svg" --still "" >/dev/null
done

declare -A total
for runtime in "${RUNTIMES[@]}"; do total[$runtime]=0; done
passed=0 failed=0
: > "$WORK/times"
printf '%-40s %-6s %-10s %8s %8s %8s %8s\n' file mode result tauri_ms deno_ms bun_ms go_ms
for input in "$@"; do
  name="$(basename "$input" .markgraf)"
  for mode in still frame; do
    case "$mode" in
      still) arguments=(--still "") ;;
      frame) arguments=(--frame 1) ;;
    esac
    stem="$WORK/out/$name.$mode"
    declare -A ms=()
    for runtime in "${RUNTIMES[@]}"; do
      ms[$runtime]=$(run "$runtime" "$input" "$stem.$runtime.svg" "${arguments[@]}")
    done
    if slower "${ms[go]}" "${ms[tauri]}" || slower "${ms[go]}" "${ms[deno]}" || slower "${ms[go]}" "${ms[bun]}"; then
      for runtime in "${RUNTIMES[@]}"; do
        again=$(run "$runtime" "$input" "$stem.$runtime.svg" "${arguments[@]}")
        ms[$runtime]=$((again < ms[$runtime] ? again : ms[$runtime]))
      done
    fi
    differences="$(for runtime in deno bun go; do difference "$stem" tauri "$runtime"; done | paste -sd, -)"
    result="${differences:-identical}"
    [ "$(cat "$stem.tauri.svg.status")" = 0 ] || [ "$result" != identical ] \
      || result="identical (exit $(cat "$stem.tauri.svg.status"))"
    case "$result" in identical*) passed=$((passed + 1)) ;; *) failed=$((failed + 1)) ;; esac
    for runtime in "${RUNTIMES[@]}"; do total[$runtime]=$((total[$runtime] + ms[$runtime])); done
    printf '%-40s %-6s %-10s %8s %8s %8s %8s\n' "$name" "$mode" "$result" \
      "${ms[tauri]}" "${ms[deno]}" "${ms[bun]}" "${ms[go]}"
    printf '%s %s %s %s %s %s\n' "${ms[tauri]}" "${ms[deno]}" "${ms[bun]}" "${ms[go]}" "$name" "$mode" >> "$WORK/times"
  done
done

echo
echo "Markgraf runtimes: $passed exports identical in all four, $failed different (work directory $WORK)"
printf '%-8s %10s %10s\n' runtime total_ms "x Go"
for runtime in "${RUNTIMES[@]}"; do
  printf '%-8s %10s %10s\n' "$runtime" "${total[$runtime]}" \
    "$(awk -v ms="${total[$runtime]}" -v go="${total[go]}" 'BEGIN { printf "%.2f", ms / (go > 0 ? go : 1) }')"
done
echo
echo "Heaviest exports (by Tauri time):"
printf '%-40s %-6s %8s %8s %8s %8s\n' file mode tauri_ms deno_ms bun_ms go_ms
sort -k1,1nr "$WORK/times" | head -5 | while read -r tauri deno bun go name mode; do
  printf '%-40s %-6s %8s %8s %8s %8s\n' "$name" "$mode" "$tauri" "$deno" "$bun" "$go"
done
[ "${KEEP:-0}" = 1 ] || [ "$failed" -ne 0 ] || rm -rf "$WORK"
[ "$failed" -eq 0 ]
