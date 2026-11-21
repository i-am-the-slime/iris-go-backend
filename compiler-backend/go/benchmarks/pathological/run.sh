#!/usr/bin/env bash
#
# Builds every pathological benchmark with `iris go` and with purs-backend-es, runs each under Go,
# Bun (JavaScriptCore) and Deno (V8), checks that the three print the same result, and prints
#
#   benchmark | hypothesis | go ms | bun ms | deno ms | go/bun | go/deno
#
# Each program runs its workload PATHO_REPETITIONS times (5 by default) in one process and reports
# the best time, so that the JavaScript engines time warmed-up code.
#
#   compiler-backend/go/benchmarks/pathological/run.sh                    # every benchmark
#   compiler-backend/go/benchmarks/pathological/run.sh String Record.Wide # module name filters
#   SKIP_BUILD=1 ...                                                      # reuse WORK's builds
#   PATHO_CPUPROFILE=/path/prof ...                                       # Go CPU profile (one benchmark)
#   PATHO_MEMSTATS=1 ...                                                  # Go heap allocations (ALLOCS line on stderr)
#   PATHO_SIZE=40000 ...                                                  # replace each benchmark's size
#   BUILD_ONLY=1 ...                                                      # build into WORK, run nothing
#
# Environment: IRIS, GO_SUPPORT, PURS_BACKEND_ES, WORK (build directory, kept), JOBS,
# GOEXPERIMENT (default simd).

set -uo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../../../.." && pwd)"
IRIS="${IRIS:-$ROOT/target/release/iris}"
GO_SUPPORT="${GO_SUPPORT:-/Users/mark/Developer/iris-go}"
# go-support scans strings sixteen bytes at a time with SIMD, an experiment
# in Go 1.27.0 (simd/archsimd) whose API may change in later releases.
export GOEXPERIMENT="${GOEXPERIMENT:-simd}"
PURS_BACKEND_ES="${PURS_BACKEND_ES:-${MARKGRAF_GATES:-/Users/mark/Developer/markgraf-gates}/npm/node_modules/.bin/purs-backend-es}"
WORK="${WORK:-${TMPDIR:-/tmp}/iris-pathological}"
JOBS="${JOBS:-6}"
TIMEOUT="${TIMEOUT:-600}"
mkdir -p "$WORK/go" "$WORK/results"

benchmarks() {
  grep -rl '^hypothesis = ' "$HERE/src" | sort | while read -r file; do
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

hypothesis_of() {
  local file="$HERE/src/$(echo "$1" | tr . /).purs"
  sed -n 's/^hypothesis = "\(.*\)"$/\1/p' "$file"
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
const module = await import(new URL(`./es/${process.argv[2] ?? Deno.args[0]}/index.js`, import.meta.url));
module.main();
JS
  sed -i '' 's/process.argv\[2\] ?? Deno.args\[0\]/typeof Deno !== "undefined" ? Deno.args[0] : process.argv[2]/' "$WORK/run.mjs"
}

build_go() {
  local name="$1" out="$WORK/go/$1"
  rm -rf "$out"
  mkdir -p "$out"
  cat > "$out/go.mod" <<GOMOD
module patho.example/bench

go 1.27.0

require github.com/i-am-the-slime/iris-go v0.0.0

replace github.com/i-am-the-slime/iris-go => $GO_SUPPORT
GOMOD
  if ! (cd "$HERE" && IRIS_GO_ANY_CENSUS=1 timeout 300 "$IRIS" go --entry "$name.main" "$out") >"$out/compile.log" 2>&1; then
    echo "$name: iris go failed: $(grep -v '^go:' "$out/compile.log" | head -1 | cut -c1-200)"
    return 1
  fi
  if ! (cd "$out" && go build -gcflags="-c=4 -dwarf=false" -ldflags=-w -o program .) >"$out/build.log" 2>&1; then
    echo "$name: go build failed: $(grep -m1 -v '^#' "$out/build.log" | cut -c1-200)"
    return 1
  fi
}
export -f build_go
export HERE IRIS GO_SUPPORT WORK

# Runs one benchmark under one runtime and records its stdout and its BENCH line.
run_one() {
  local name="$1" runtime="$2" result="$WORK/results/$1.$2"
  case "$runtime" in
    go) [ -x "$WORK/go/$name/program" ] || { echo "MISSING" >"$result.out"; : >"$result.err"; return; }
        timeout "$TIMEOUT" "$WORK/go/$name/program" >"$result.out" 2>"$result.err" ;;
    bun) (cd "$WORK" && timeout "$TIMEOUT" bun run.mjs "$name") >"$result.out" 2>"$result.err" ;;
    deno) (cd "$WORK" && timeout "$TIMEOUT" deno run -A run.mjs "$name") >"$result.out" 2>"$result.err" ;;
  esac
  [ "$?" = 0 ] || echo "EXIT $?" >>"$result.out"
}

best_of() {
  sed -n 's/^BENCH \([0-9.]*\) .*/\1/p' "$WORK/results/$1.$2.err" | tail -1
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
fi
[ "${BUILD_ONLY:-0}" != 1 ] || exit 0

: >"$WORK/load.txt"
for name in "${names[@]}"; do
  echo "$name $(sysctl -n vm.loadavg | tr , .)" >>"$WORK/load.txt"
  for runtime in go bun deno; do run_one "$name" "$runtime"; done
done

status=0
printf '| benchmark | hypothesis | go ms | bun ms | deno ms | go/bun | go/deno |\n|---|---|---:|---:|---:|---:|---:|\n'
for name in "${names[@]}"; do
  go_ms="$(best_of "$name" go)" bun_ms="$(best_of "$name" bun)" deno_ms="$(best_of "$name" deno)"
  printf '| %s | %s | %s | %s | %s | %s | %s |\n' "${name#Bench.}" "$(hypothesis_of "$name")" \
    "${go_ms:--}" "${bun_ms:--}" "${deno_ms:--}" "$(ratio "$go_ms" "$bun_ms")" "$(ratio "$go_ms" "$deno_ms")"
done
echo
echo "load average (1/5/15 min) before each benchmark: $(LC_ALL=C awk '{ sum += $3; if ($3 + 0 > high) high = $3 + 0 } END { printf "mean 1-min %.1f, highest %.1f", sum / NR, high }' "$WORK/load.txt") (details in $WORK/load.txt)"
for name in "${names[@]}"; do
  if ! cmp -s "$WORK/results/$name.go.out" "$WORK/results/$name.bun.out" \
    || ! cmp -s "$WORK/results/$name.bun.out" "$WORK/results/$name.deno.out"; then
    status=1
    echo "MISMATCH $name"
    for runtime in go bun deno; do
      printf '  %-5s %s\n' "$runtime" "$(head -c 300 "$WORK/results/$name.$runtime.out" | tr '\n' '/')"
    done
  fi
done
exit "$status"
