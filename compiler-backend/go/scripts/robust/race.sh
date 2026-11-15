#!/usr/bin/env bash
#
# Builds generated Go with `go vet` and `go build -race`, runs the race builds on a representative
# set of programs, and prints every vet complaint and every data race, deduplicated by location.
#
#   compiler-backend/go/scripts/robust/race.sh                       # every target
#   compiler-backend/go/scripts/robust/race.sh go-support markgraf   # chosen targets
#
# Targets:
#   go-support    go vet (default and libm tags) and go test -race over go-support itself
#   markgraf      the Markgraf CLI (build-go-cli.sh, pinned markgraf-gates): vet, a race build run
#                 over --still and --frame exports, and a second race build in which the camera
#                 plan's two parallelMap call sites call array.ParallelMap (iris maps parallelMap to
#                 the sequential array.Map) on a go-support copy whose parallel threshold is 2, so
#                 that the goroutines actually run on small diagrams
#   examples      every purs-backend-go example: vet, race build, run
#   pathological  every pathological benchmark: vet and race build; runs RACE_PATHO (Aff.*, Om.*
#                 and the Persistent/Lazy ones by default) once each
#
# Environment: IRIS, GO_SUPPORT, EXAMPLES, MARKGRAF (pinned.sh), WORK (kept; default
# $TMPDIR/iris-race), JOBS, TIMEOUT (seconds per race run, default 600), MARKGRAF_INPUTS (files),
# GOEXPERIMENT (default simd).
#
# Exit status 1 when any target has a race, a vet complaint not on the noise list, or a failed
# build. Vet's `unreachable code` after an emitted panic is reported but counted as noise.

set -uo pipefail
export LC_ALL=C

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
GO_DIR="$(cd "$HERE/../.." && pwd)"
ROOT="$(cd "$GO_DIR/../.." && pwd)"
IRIS="${IRIS:-$ROOT/target/release/iris}"
GO_SUPPORT="${GO_SUPPORT:-/Users/mark/Developer/purs-backend-go/go-support}"
EXAMPLES="${EXAMPLES:-/Users/mark/Developer/purs-backend-go/examples}"
export GOEXPERIMENT="${GOEXPERIMENT:-simd}"
WORK="${WORK:-${TMPDIR:-/tmp}/iris-race}"
JOBS="${JOBS:-6}"
TIMEOUT="${TIMEOUT:-600}"
RACE_PATHO="${RACE_PATHO:-Aff. Om. Persistent. Lazy. Exception.}"
# halt_on_error=0: report every race of a run, not only the first.
export GORACE="halt_on_error=0 history_size=2"
mkdir -p "$WORK"
export IRIS GO_SUPPORT EXAMPLES WORK GOEXPERIMENT TIMEOUT

VET_NOISE='unreachable code'

go_mod() { # module-name go-support-dir
  cat <<GOMOD
module $1

go 1.27.0

require github.com/i-am-the-slime/purs-backend-go/go-support v0.0.0

replace github.com/i-am-the-slime/purs-backend-go/go-support => $2
GOMOD
}
export -f go_mod

# vet_into DIR LOG [TAGS]: `go vet` over a generated module, complaints as `file:line: message`.
vet_into() {
  (cd "$1" && go vet ${3:+-tags "$3"} ./... 2>&1) | grep -E '^[^#].*:[0-9]+:[0-9]+: ' \
    | sed -E "s|^\./||" >"$2"
}
export -f vet_into

# A race report's key: the innermost frame of each of its two accesses, as `function file:line`.
race_keys() { # stderr-file label
  awk -v label="$2" '
    /^WARNING: DATA RACE/ { inrace = 1; n = 0; next }
    inrace && /^(Read|Write|Previous read|Previous write|Atomic)/ { want = 1; kind = $1 " " $2; next }
    inrace && want && /^  [^ ]/ { fn = $1; next }
    inrace && want && /^      / { sub(/^ +/, ""); sub(/ \+0x.*/, ""); keys[++n] = kind " " fn " " $0; want = 0; next }
    inrace && /^==================/ { if (n) { line = label ":"; for (i = 1; i <= n; i++) line = line " | " keys[i]; print line }; inrace = 0 }
  ' "$1"
}
export -f race_keys

run_race() { # label binary args... ; runs in $WORK/runs, appends race keys to $WORK/races.txt
  local label="$1"; shift
  local log="$WORK/runs/$(echo "$label" | tr '/ ' '__').err"
  mkdir -p "$WORK/runs"
  (cd "$WORK/runs" && timeout "$TIMEOUT" "$@" >"$log.out" 2>"$log")
  local status=$?
  # The CLI's own refusal of a file without a still frame (JS exits 1 the same way).
  if [ "$status" = 1 ] && grep -q 'No `still` or `title` frame found' "$log"; then status="0 (no still frame)"; fi
  if grep -q '^WARNING: DATA RACE' "$log"; then
    race_keys "$log" "$label" >>"$WORK/races.txt"
  fi
  echo "$label exit $status races $(grep -c '^WARNING: DATA RACE' "$log")" >>"$WORK/runs.txt"
}
export -f run_race

# A deliberately racy program, so that a clean summary means the detector and race_keys work.
self_check() {
  local dir="$WORK/self-check"
  rm -rf "$dir"; mkdir -p "$dir"
  printf 'module selfcheck\n\ngo 1.27.0\n' >"$dir/go.mod"
  cat >"$dir/main.go" <<'GO'
package main

var counter int

func main() {
	done := make(chan bool)
	go func() { counter++; done <- true }()
	counter++
	<-done
}
GO
  (cd "$dir" && go build -race -o racy . && ./racy) 2>"$dir/stderr" >/dev/null
  if [ "$(race_keys "$dir/stderr" self-check | grep -c 'main.go:')" = 0 ]; then
    echo "self-check: the race detector or race_keys found no race in a racy program" >&2
    exit 2
  fi
}

target_go_support() {
  echo "== go-support ($GO_SUPPORT)"
  (cd "$GO_SUPPORT" && go vet ./... 2>&1) | grep -E ':[0-9]+:[0-9]+: ' | sed 's/^/go-support: /' >>"$WORK/vet.txt"
  (cd "$GO_SUPPORT" && go vet -tags libm ./... 2>&1) | grep -E ':[0-9]+:[0-9]+: ' | sed 's/^/go-support(libm): /' >>"$WORK/vet.txt"
  (cd "$GO_SUPPORT" && go test -race -count=1 ./... >"$WORK/go-support-race.txt" 2>&1)
  local status=$?
  race_keys "$WORK/go-support-race.txt" go-support-tests >>"$WORK/races.txt"
  grep -E '^(FAIL|--- FAIL)' "$WORK/go-support-race.txt" | sed 's/^/go-support test: /' >>"$WORK/failures.txt"
  echo "go-support go test -race exit $status" >>"$WORK/runs.txt"
}

target_markgraf() {
  echo "== markgraf"
  source "$GO_DIR/scripts/markgraf/pinned.sh" || return
  local out="$WORK/markgraf"
  rm -rf "$out"
  if ! IRIS="$IRIS" GO_SUPPORT="$GO_SUPPORT" "$GO_DIR/scripts/markgraf/build-go-cli.sh" "$out/go" >"$out.build.log" 2>&1; then
    echo "markgraf: build-go-cli.sh failed (see $out.build.log)" >>"$WORK/failures.txt"; return
  fi
  vet_into "$out/go" "$out.vet" libm
  sed 's/^/markgraf: /' "$out.vet" >>"$WORK/vet.txt"
  (cd "$out/go" && go build -race -tags libm -gcflags=-dwarf=false -ldflags=-w -o bin/markgraf-race .) >>"$out.build.log" 2>&1 \
    || { echo "markgraf: race build failed" >>"$WORK/failures.txt"; return; }

  # The camera plan's parallelMap call sites, made parallel. They are found by their callees, so
  # that a renamed temporary does not silently skip the experiment.
  rm -rf "$out/parallel" "$WORK/go-support-parallel"
  cp -c -R "$out/go" "$out/parallel" 2>/dev/null || cp -R "$out/go" "$out/parallel"
  rsync -a --exclude .jj "$GO_SUPPORT/" "$WORK/go-support-parallel/"
  sed -i '' 's/const parallelMapMinimum = [0-9]*/const parallelMapMinimum = 2/' "$WORK/go-support-parallel/array/parallel.go"
  go_mod markgraf.example/cli "$WORK/go-support-parallel" >"$out/parallel/go.mod"
  local plan
  plan="$(ls "$out"/parallel/Markgraf/Animation/Camera/Plan/*.go | head -1)"
  local sites
  sites="$(grep -nE 'array\.Map\(func\(.*\) [A-Za-z.]*(HandoffsSegment|SegmentSpans) \{' "$plan" | cut -d: -f1)"
  if [ "$(echo "$sites" | grep -c .)" != 2 ]; then
    echo "markgraf: expected 2 parallelMap sites in $plan, found: $sites" >>"$WORK/failures.txt"
  else
    for line in $sites; do sed -i '' -E "${line}s/array\.Map\(/array.ParallelMap(/" "$plan"; done
    (cd "$out/parallel" && go build -race -tags libm -gcflags=-dwarf=false -ldflags=-w -o bin/markgraf-race-parallel .) >>"$out.build.log" 2>&1 \
      || echo "markgraf: parallel race build failed" >>"$WORK/failures.txt"
  fi

  local inputs=()
  if [ -n "${MARKGRAF_INPUTS:-}" ]; then
    read -r -a inputs <<<"$MARKGRAF_INPUTS"
  else
    inputs=("$MARKGRAF"/examples/*.markgraf "$MARKGRAF"/npm/test/Animation/Sequence/*.markgraf)
  fi
  export out MARKGRAF_INPUT_LIST="${inputs[*]}"
  for input in "${inputs[@]}"; do
    local name
    name="$(basename "$input" .markgraf)"
    for binary in markgraf-race markgraf-race-parallel; do
      local dir=go; [ "$binary" = markgraf-race-parallel ] && dir=parallel
      [ -x "$out/$dir/bin/$binary" ] || continue
      echo "markgraf $binary $name still"
      echo "markgraf $binary $name frame 1"
      echo "markgraf $binary $name frame 3.5"
    done
  done | xargs -P "$JOBS" -I{} bash -c 'markgraf_run_one $1' _ {}
}

markgraf_run_one() { # markgraf binary name mode [at]
  local binary="$2" name="$3" mode="$4" at="${5:-}" dir=go input args
  [ "$binary" = markgraf-race-parallel ] && dir=parallel
  for input in $MARKGRAF_INPUT_LIST; do [ "$(basename "$input" .markgraf)" = "$name" ] && break; done
  if [ "$mode" = still ]; then args=(--still ""); else args=(--frame "$at"); fi
  run_race "markgraf/$binary/$name/$mode$at" "$out/$dir/bin/$binary" "$input" "${args[@]}" \
    -o "$WORK/runs/$binary.$name.$mode$at.svg"
}
export -f markgraf_run_one

build_example() { # manifest line
  local line name entry kind expected
  eval "line=\"$1\""
  IFS='|' read -r name entry kind expected <<<"$line"
  local out="$WORK/examples/$name"
  rm -rf "$out"; mkdir -p "$out"
  go_mod example.com/t "$GO_SUPPORT" >"$out/go.mod"
  if ! (cd "$EXAMPLES/$name" && timeout 120 "$IRIS" go --entry "$entry" "$out") >"$out/compile.log" 2>&1; then
    echo "example $name: iris go failed" >>"$WORK/failures.txt"; return
  fi
  vet_into "$out" "$out/vet.txt"
  sed "s|^|example $name: |" "$out/vet.txt" >>"$WORK/vet.txt"
  if ! (cd "$out" && go build -race -gcflags=-dwarf=false -ldflags=-w -o program-race .) >"$out/build.log" 2>&1; then
    echo "example $name: race build failed: $(grep -m1 -v '^#' "$out/build.log" | cut -c1-160)" >>"$WORK/failures.txt"; return
  fi
  run_race "example/$name" "$out/program-race"
}
export -f build_example

target_examples() {
  echo "== examples ($EXAMPLES)"
  grep -E '^  "[A-Za-z0-9_]+\|[^|]+\|(value|effect|program)\|' "$EXAMPLES/run.sh" | sed -E 's/^  "//; s/"$//' \
    >"$WORK/examples.manifest"
  mkdir -p "$WORK/examples"
  local count
  count="$(wc -l <"$WORK/examples.manifest" | tr -d ' ')"
  seq 1 "$count" | xargs -P "$JOBS" -I{} bash -c 'build_example "$(sed -n "$1p" "$WORK/examples.manifest")"' _ {}
}

build_patho() { # module
  local name="$1" out="$WORK/pathological/$1" here="$GO_DIR/benchmarks/pathological"
  rm -rf "$out"; mkdir -p "$out"
  go_mod patho.example/bench "$GO_SUPPORT" >"$out/go.mod"
  if ! (cd "$here" && timeout 300 "$IRIS" go --entry "$name.main" "$out") >"$out/compile.log" 2>&1; then
    echo "pathological $name: iris go failed: $(grep -v '^go:' "$out/compile.log" | head -1 | cut -c1-160)" >>"$WORK/failures.txt"; return
  fi
  vet_into "$out" "$out/vet.txt"
  sed "s|^|pathological $name: |" "$out/vet.txt" >>"$WORK/vet.txt"
  if ! (cd "$out" && go build -race -gcflags=-dwarf=false -ldflags=-w -o program-race .) >"$out/build.log" 2>&1; then
    echo "pathological $name: race build failed: $(grep -m1 -v '^#' "$out/build.log" | cut -c1-160)" >>"$WORK/failures.txt"; return
  fi
  for filter in $RACE_PATHO; do
    case "$name" in "Bench.$filter"*) PATHO_REPETITIONS=1 run_race "pathological/$name" "$out/program-race"; break ;; esac
  done
}
export -f build_patho
export GO_DIR RACE_PATHO

target_pathological() {
  echo "== pathological"
  mkdir -p "$WORK/pathological"
  # Fetch the package set once: parallel `iris go` runs would each start the same Spago fetch.
  (cd "$GO_DIR/benchmarks/pathological" && spago build --quiet) >"$WORK/pathological.spago.log" 2>&1 \
    || { echo "pathological: spago build failed (see $WORK/pathological.spago.log)" >>"$WORK/failures.txt"; return; }
  grep -rl '^hypothesis = ' "$GO_DIR/benchmarks/pathological/src" | sort \
    | xargs sed -n 's/^module \([A-Za-z0-9.]*\).*/\1/p' \
    | xargs -P "$JOBS" -I{} bash -c 'build_patho "$1"' _ {}
}

targets=("$@")
[ "${#targets[@]}" -gt 0 ] || targets=(go-support markgraf examples pathological)
: >"$WORK/vet.txt"; : >"$WORK/races.txt"; : >"$WORK/runs.txt"; : >"$WORK/failures.txt"
self_check
for target in "${targets[@]}"; do
  case "$target" in
    go-support) target_go_support ;;
    markgraf) target_markgraf ;;
    examples) target_examples ;;
    pathological) target_pathological ;;
    *) echo "unknown target $target"; exit 2 ;;
  esac
done

echo
echo "== vet complaints, by location ($(wc -l <"$WORK/vet.txt" | tr -d ' ') in all; details in $WORK/vet.txt)"
# The program prefix (`example X: `) is dropped for deduplication only where the location is in
# go-support; generated files are per program.
sort "$WORK/vet.txt" | awk -F': ' '{ count[$0]++ } END { for (k in count) print count[k] "x " k }' | sort -k2 | sed 's/^/  /'
noise="$(grep -c -- "$VET_NOISE" "$WORK/vet.txt")"
real="$(grep -vc -- "$VET_NOISE" "$WORK/vet.txt")"
echo "  ($noise noise: '$VET_NOISE' after an emitted panic; $real other)"

echo
echo "== data races, by location pair ($(grep -c . "$WORK/races.txt") reports)"
sed -E 's/^[^:]*: //' "$WORK/races.txt" | sort | uniq -c | sort -rn | sed 's/^/  /'
echo
echo "== race runs: $(wc -l <"$WORK/runs.txt" | tr -d ' '), with races: $(awk '$NF != 0' "$WORK/runs.txt" | wc -l | tr -d ' '), nonzero exit: $(grep -vc 'exit 0 ' "$WORK/runs.txt") (details in $WORK/runs.txt)"
grep -v 'exit 0 ' "$WORK/runs.txt" | sed 's/^/  /'
echo
echo "== build failures: $(grep -c . "$WORK/failures.txt")"
sed 's/^/  /' "$WORK/failures.txt"

status=0
[ "$real" = 0 ] || status=1
[ -s "$WORK/races.txt" ] && status=1
[ -s "$WORK/failures.txt" ] && status=1
exit "$status"
