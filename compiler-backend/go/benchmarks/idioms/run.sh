#!/usr/bin/env bash
#
# Idiomatic, FFI-free PureScript against hand-written Go. Builds every idiom benchmark with
# `iris go` and with purs-backend-es, builds its hand-written Go reference from go/cmd/<name>,
# runs the four under Go (generated), Go (hand-written), Bun (JavaScriptCore) and Deno (V8),
# checks that all four print the same result, and prints
#
#   benchmark | idiom | ps→go ms | hand ms | ps→go/hand | bun ms | deno ms | ps→go allocs | hand allocs
#
# Each program runs its workload PATHO_REPETITIONS times (5 by default) in one process and reports
# the best time; allocations are the heap objects allocated over every repetition together. The
# benchmarks share Bench.Harness with ../pathological (a local package dependency), so every
# PATHO_* variable of that suite applies here.
#
#   compiler-backend/go/benchmarks/idioms/run.sh                    # every benchmark
#   compiler-backend/go/benchmarks/idioms/run.sh STArray Pure.GoLoops  # module name filters
#   SKIP_BUILD=1 ...                                                # reuse WORK's builds
#   PATHO_CPUPROFILE=/path/prof ...                                 # Go CPU profile (one benchmark, generated side)
#   HAND_CPUPROFILE=/path/prof ...                                  # Go CPU profile (one benchmark, hand side)
#   PATHO_SIZE=40000 ...                                            # replace each benchmark's size
#   BUILD_ONLY=1 ...                                                # build into WORK, run nothing
#   RUNTIMES="go hand" ...                                          # which runtimes to run (default: go hand bun deno)
#
# Environment: IRIS, GO_SUPPORT, PURS_BACKEND_ES, WORK (build directory, kept), JOBS,
# GOEXPERIMENT (default simd).

set -uo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../../../.." && pwd)"
IRIS="${IRIS:-$ROOT/target/release/iris}"
GO_SUPPORT="${GO_SUPPORT:-/Users/mark/Developer/iris-go}"
export GOEXPERIMENT="${GOEXPERIMENT:-simd}"
PURS_BACKEND_ES="${PURS_BACKEND_ES:-${MARKGRAF_GATES:-/Users/mark/Developer/markgraf-gates}/npm/node_modules/.bin/purs-backend-es}"
WORK="${WORK:-${TMPDIR:-/tmp}/iris-idioms}"
JOBS="${JOBS:-4}"
TIMEOUT="${TIMEOUT:-600}"
RUNTIMES="${RUNTIMES:-go hand bun deno}"
mkdir -p "$WORK/go" "$WORK/hand" "$WORK/results"

benchmarks() {
  grep -rl '^idiom = ' "$HERE/src" | sort | while read -r file; do
    sed -n 's/^module \([A-Za-z0-9.]*\).*/\1/p' "$file"
  done
}

selected() {
  if [ "$#" -eq 0 ]; then
    benchmarks
  else
    for filter in "$@"; do benchmarks | grep -F -- "$filter"; done | awk '!seen[$0]++'
  fi
}

idiom_of() {
  local file="$HERE/src/$(echo "$1" | tr . /).purs"
  sed -n 's/^idiom = "\(.*\)"$/\1/p' "$file"
}

# Bench.Idiom.STArray.Sieve has its hand-written reference in go/cmd/starray_sieve.
hand_name() {
  echo "${1#Bench.Idiom.}" | tr . _ | tr '[:upper:]' '[:lower:]'
}

build_javascript() {
  (cd "$HERE" && spago build --quiet) >"$WORK/spago.log" 2>&1 || { cat "$WORK/spago.log"; exit 1; }
  local sources=()
  while IFS= read -r source; do sources+=("$HERE/$source"); done < <(cd "$HERE" && spago sources 2>/dev/null)
  (cd "$HERE" && purs compile "${sources[@]}" --codegen js,corefn --output "$WORK/corefn") >"$WORK/purs.log" 2>&1 \
    || { cat "$WORK/purs.log"; exit 1; }
  rm -rf "$WORK/es"
  (cd "$HERE" && "$PURS_BACKEND_ES" build --corefn-dir "$WORK/corefn" --output-dir "$WORK/es") >"$WORK/es.log" 2>&1 \
    || { cat "$WORK/es.log"; exit 1; }
  cat > "$WORK/run.mjs" <<'JS'
const name = typeof Deno !== "undefined" ? Deno.args[0] : process.argv[2];
const module = await import(new URL(`./es/${name}/index.js`, import.meta.url));
module.main();
JS
}

go_mod() {
  cat <<GOMOD
module idioms.example/$1

go 1.27.0

require github.com/i-am-the-slime/iris-go v0.0.0

replace github.com/i-am-the-slime/iris-go => $GO_SUPPORT
GOMOD
}

build_go() {
  local name="$1" out="$WORK/go/$1"
  rm -rf "$out"
  mkdir -p "$out"
  go_mod bench > "$out/go.mod"
  if ! (cd "$HERE" && IRIS_GO_ANY_CENSUS=1 timeout 300 "$IRIS" go --entry "$name.main" "$out") >"$out/compile.log" 2>&1; then
    echo "$name: iris go failed: $(grep -v '^go:' "$out/compile.log" | head -1 | cut -c1-200)"
    return 1
  fi
  if ! (cd "$out" && go build -gcflags="-c=4 -dwarf=false" -ldflags=-w -o program .) >"$out/build.log" 2>&1; then
    echo "$name: go build failed: $(grep -m1 -v '^#' "$out/build.log" | cut -c1-200)"
    return 1
  fi
}
export -f build_go go_mod
export HERE IRIS GO_SUPPORT WORK

# The hand-written references share one module; a go.mod is written next to a copy so that the
# checked-in sources carry no machine-specific path to go-support.
build_hand() {
  local src="$WORK/hand/src"
  rm -rf "$src"
  mkdir -p "$src"
  cp -R "$HERE/go/." "$src/"
  go_mod hand > "$src/go.mod"
  (cd "$src" && go mod tidy) >"$WORK/hand/tidy.log" 2>&1
  local failed=0
  for name in "$@"; do
    local hand; hand="$(hand_name "$name")"
    [ -d "$src/cmd/$hand" ] || { echo "$name: no hand-written reference at go/cmd/$hand"; failed=1; continue; }
    if ! (cd "$src" && go build -gcflags="-c=4 -dwarf=false" -ldflags=-w -o "$WORK/hand/$hand" "./cmd/$hand") >"$WORK/hand/$hand.build.log" 2>&1; then
      echo "$name: hand go build failed: $(grep -m1 -v '^#' "$WORK/hand/$hand.build.log" | cut -c1-200)"
      failed=1
    fi
  done
  return "$failed"
}

run_one() {
  local name="$1" runtime="$2" result="$WORK/results/$1.$2"
  case "$runtime" in
    go) [ -x "$WORK/go/$name/program" ] || { echo "MISSING" >"$result.out"; : >"$result.err"; return; }
        PATHO_MEMSTATS=1 timeout "$TIMEOUT" "$WORK/go/$name/program" >"$result.out" 2>"$result.err" ;;
    hand) local hand; hand="$(hand_name "$name")"
        [ -x "$WORK/hand/$hand" ] || { echo "MISSING" >"$result.out"; : >"$result.err"; return; }
        PATHO_MEMSTATS=1 PATHO_CPUPROFILE="${HAND_CPUPROFILE:-}" timeout "$TIMEOUT" "$WORK/hand/$hand" >"$result.out" 2>"$result.err" ;;
    bun) (cd "$WORK" && timeout "$TIMEOUT" bun run.mjs "$name") >"$result.out" 2>"$result.err" ;;
    deno) (cd "$WORK" && timeout "$TIMEOUT" deno run -A --v8-flags=--stack-size=4096 run.mjs "$name") >"$result.out" 2>"$result.err" ;;
  esac
  [ "$?" = 0 ] || echo "EXIT $?" >>"$result.out"
}

best_of() {
  sed -n 's/^BENCH \([0-9.]*\) .*/\1/p' "$WORK/results/$1.$2.err" | tail -1
}

allocs_of() {
  sed -n 's/^ALLOCS \([0-9]*\) .*/\1/p' "$WORK/results/$1.$2.err" | tail -1
}

wait_for_quiet_machine() {
  while ps -axo command= | grep -E 'compare-svg.sh|measure.py|bin/iris-go/run' | grep -qvE 'pgrep|until |grep'; do
    sleep 5
  done
}

ratio() {
  if [ -n "$1" ] && [ -n "$2" ]; then LC_ALL=C awk -v a="$1" -v b="$2" 'BEGIN { printf "%.2f", a / b }'; else echo "-"; fi
}

names=()
while IFS= read -r name; do names+=("$name"); done < <(selected "$@")
[ "${#names[@]}" -gt 0 ] || { echo "no benchmark matches $*"; exit 1; }

if [ "${SKIP_BUILD:-0}" != 1 ]; then
  build_javascript || exit 1
  printf '%s\n' "${names[@]}" | xargs -P "$JOBS" -I{} bash -c 'build_go "$1"' _ {}
  build_hand "${names[@]}"
fi
[ "${BUILD_ONLY:-0}" != 1 ] || exit 0

: >"$WORK/load.txt"
for name in "${names[@]}"; do
  wait_for_quiet_machine
  echo "$name $(sysctl -n vm.loadavg | tr , .)" >>"$WORK/load.txt"
  for runtime in $RUNTIMES; do run_one "$name" "$runtime"; done
done

status=0
printf '| benchmark | idiom | ps→go ms | hand ms | ps→go/hand | bun ms | deno ms | ps→go allocs | hand allocs |\n|---|---|---:|---:|---:|---:|---:|---:|---:|\n'
for name in "${names[@]}"; do
  go_ms="$(best_of "$name" go)" hand_ms="$(best_of "$name" hand)" bun_ms="$(best_of "$name" bun)" deno_ms="$(best_of "$name" deno)"
  printf '| %s | %s | %s | %s | %s | %s | %s | %s | %s |\n' "${name#Bench.Idiom.}" "$(idiom_of "$name")" \
    "${go_ms:--}" "${hand_ms:--}" "$(ratio "$go_ms" "$hand_ms")" "${bun_ms:--}" "${deno_ms:--}" \
    "$(allocs_of "$name" go)" "$(allocs_of "$name" hand)"
done
echo
echo "load average (1/5/15 min) before each benchmark: $(LC_ALL=C awk '{ sum += $3; if ($3 + 0 > high) high = $3 + 0 } END { printf "mean 1-min %.1f, highest %.1f", sum / NR, high }' "$WORK/load.txt") (details in $WORK/load.txt)"
for name in "${names[@]}"; do
  reference="$WORK/results/$name.go.out"
  for runtime in $RUNTIMES; do
    if ! cmp -s "$reference" "$WORK/results/$name.$runtime.out"; then
      status=1
      echo "MISMATCH $name"
      for shown in $RUNTIMES; do
        printf '  %-5s %s\n' "$shown" "$(head -c 300 "$WORK/results/$name.$shown.out" | tr '\n' '/')"
      done
      break
    fi
  done
done
exit "$status"
