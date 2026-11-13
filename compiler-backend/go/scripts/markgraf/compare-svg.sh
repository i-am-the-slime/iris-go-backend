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
# Finally checks the generated Go against the markgraf-cli quality baseline.

set -uo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../../../.." && pwd)"
IRIS="${IRIS:-$ROOT/target/release/iris}"
MARKGRAF="${MARKGRAF:-/Users/mark/Developer/markgraf}"
GO_SUPPORT="${GO_SUPPORT:-/Users/mark/Developer/purs-backend-go/go-support}"
WORK="${WORK:-$(mktemp -d)}"
TIMEOUT="${TIMEOUT:-600}"
FONTS="$MARKGRAF/cli/assets/native/fonts"

milliseconds() { perl -MTime::HiRes=time -e 'printf "%.0f", time*1000'; }

if [ -z "${MARKGRAF_JS:-}" ]; then
  MARKGRAF_JS="$("$HERE/build-js-cli.sh" "$WORK/js")" || exit 1
fi

mkdir -p "$WORK/go/fonts" "$WORK/out"
(cd "$MARKGRAF/cli" && "$IRIS" go --entry Main.run "$WORK/go") || exit 1
cp "$HERE/host/host.go" "$WORK/go/"
for font in Ilisarniq-Demi.otf Ilisarniq-Italic.otf VictorMono-Medium.ttf VictorMono-Bold.ttf \
  VictorMono-MediumItalic.ttf VictorMono-BoldItalic.ttf; do
  cp "$FONTS/$font" "$WORK/go/fonts/"
done
cat > "$WORK/go/go.mod" <<GOMOD
module markgraf.example/cli

go 1.23.2

require github.com/i-am-the-slime/purs-backend-go/go-support v0.0.0

replace github.com/i-am-the-slime/purs-backend-go/go-support => $GO_SUPPORT
GOMOD
# -tags libm: Math.sin and friends from the C library, as JavaScriptCore does.
(cd "$WORK/go" && go build -tags libm -o markgraf .) || exit 1
MARKGRAF_GO="$WORK/go/markgraf"

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

passed=0 failed=0
printf '%-44s %-7s %-9s %8s %8s\n' file mode result js_ms go_ms
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
    printf '%-44s %-7s %-9s %8s %8s\n' "$name" "$mode" "$result" "$js_ms" "$go_ms"
  done
done
echo "Markgraf SVG: $passed identical, $failed different (work directory $WORK)"
"$HERE/../quality.sh" markgraf-cli "$WORK/go" || failed=$((failed + 1))
[ "${KEEP:-0}" = 1 ] || [ "$failed" -ne 0 ] || rm -rf "$WORK"
[ "$failed" -eq 0 ]
