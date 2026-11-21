#!/usr/bin/env bash
#
# Finds programs whose generated Go grows faster than linearly in their input size while the
# JavaScript build of the same program does not.
#
# Each program runs at sizes n, 2n and 4n under Go, Bun (JavaScriptCore) and Deno (V8). For every
# runtime the growth ratio r = t(4n) / t(2n) is printed; a linear program has r = 2, an n log n one
# about 2.1, a quadratic one 4. A program is flagged
#
#   GO-SUPERLINEAR    r(go) > GO_RATIO (2.6) while the more linear JS engine has r < JS_RATIO (2.3),
#                     confirmed by a fourth run at 8n whose r(8n/4n) also exceeds GO_RATIO
#   UNCONFIRMED       as above, but the 8n run did not repeat it (noise or a cache cliff)
#   BOTH-SUPERLINEAR  r > GO_RATIO under Go and under both JS engines: the algorithm itself is
#                     super-linear (information only)
#   TOO-FAST          the 2n run of some runtime took under MIN_MS even at the largest size tried,
#                     so its ratio is noise
#
# Why these thresholds: timings are the best of REPETITIONS runs, which on a loaded machine still
# leaves roughly ±10% per point, so a linear program's ratio reads anywhere in 1.7..2.3 and an
# n log n one up to about 2.3. Go's GC adds a little more (the heap doubles with the input, and
# GOGC=400 makes cycles rarer but longer), so 2.6, an exponent of 1.38, is the smallest Go ratio
# that noise and logarithmic factors do not explain, while n^1.5 (2.83) and n^2 (4.0) clear it.
# JS must stay under 2.3 (exponent 1.2) so that a program that is super-linear by construction is
# not blamed on Go. The 8n confirmation removes one-off spikes from a GC cycle or another agent's
# build landing on one point.
#
# Every runtime gets its own n: starting from half the module's default size, n is halved while
# one run takes over CALIBRATE_MS (1500) and doubled while it takes under GROW_MS (20), so that Go
# and JS are both timed where their curves are measurable; linearity is a property of each curve,
# so the runtimes need not share sizes. `depth` programs (scaling-sizes.txt: the size is a tree
# depth) step d, d+1, d+2, and their ratios are divided by half the tree's branching factor
# before the same thresholds apply.
#
#   compiler-backend/go/scripts/robust/scaling.sh                       # pathological + compat
#   compiler-backend/go/scripts/robust/scaling.sh patho Om. String.     # one suite, name filters
#   compiler-backend/go/scripts/robust/scaling.sh compat TailRec
#   SKIP_BUILD=1 ...                                                    # reuse WORK's builds
#
# Environment: IRIS, GO_SUPPORT, PURS_BACKEND_ES, WORK (default $TMPDIR/iris-robust-scaling),
# REPETITIONS (3), GO_RATIO, JS_RATIO, MIN_MS (5), GROW_MS, CALIBRATE_MS, TIMEOUT (180 s per run),
# JOBS, NO_DENO=1, NO_WAIT=1 (do not wait for other agents' timing runs).

set -uo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
GO_DIR="$(cd "$HERE/../.." && pwd)"
ROOT="$(cd "$GO_DIR/../.." && pwd)"
export IRIS="${IRIS:-$ROOT/target/release/iris}"
export GO_SUPPORT="${GO_SUPPORT:-/Users/mark/Developer/iris-go}"
export PURS_BACKEND_ES="${PURS_BACKEND_ES:-/Users/mark/Developer/markgraf-gates/npm/node_modules/.bin/purs-backend-es}"
WORK="${WORK:-${TMPDIR:-/tmp}/iris-robust-scaling}"
REPETITIONS="${REPETITIONS:-3}"
GO_RATIO="${GO_RATIO:-2.6}"
JS_RATIO="${JS_RATIO:-2.3}"
MIN_MS="${MIN_MS:-5}"
GROW_MS="${GROW_MS:-20}"
CALIBRATE_MS="${CALIBRATE_MS:-1500}"
TIMEOUT="${TIMEOUT:-180}"
JOBS="${JOBS:-4}"
RUNTIMES="go bun deno"
[ "${NO_DENO:-0}" = 1 ] && RUNTIMES="go bun"
mkdir -p "$WORK"

suite="all"
case "${1:-}" in patho|compat|all) suite="$1"; shift ;; esac
filters=("$@")
ROWS="$WORK/rows-$suite.tsv"

matches() {
  [ "${#filters[@]}" -eq 0 ] && return 0
  local filter
  for filter in "${filters[@]}"; do case "$1" in *"$filter"*) return 0 ;; esac; done
  return 1
}

# The timing runs of other agents, which must not overlap ours. Shells of other agents that are
# themselves waiting (`until ! pgrep -f measure.py ...`) mention the same names and do not
# count; our own pathological build runs run.sh with BUILD_ONLY=1 and times nothing.
wait_for_quiet_machine() {
  [ "${NO_WAIT:-0}" = 1 ] && return
  local waited=0
  while ps -axo command= | grep -E 'measure.py|benchmarks/pathological/run.sh|benchmarks/compat/run.sh' \
    | grep -qvE 'pgrep|until |grep|BUILD_ONLY'; do
    [ "$waited" = 0 ] && echo "waiting for other timing runs to finish ..." >&2
    waited=$((waited + 5))
    sleep 5
  done
}

load_average() { sysctl -n vm.loadavg | tr -d '{}' | tr , . | awk '{ print $1 }'; }

# ---------------------------------------------------------------- pathological suite
#
# Sizes come from each module's `size:` field; PATHO_SIZE replaces it at run time (Bench.Harness).

PATHO="$GO_DIR/benchmarks/pathological"

sizing() { # name column (2 kind, 3 base or branching factor)
  awk -v name="$1" -v column="$2" '$1 == name { print $column; exit }' "$HERE/scaling-sizes.txt"
}

patho_kind() { local kind; kind="$(sizing "$1" 2)"; echo "${kind:-linear}"; }

# Ratios of a depth program are divided by this, so that one more level of a binary tree reads 2.
patho_scale() {
  if [ "$(patho_kind "$1")" = depth ]; then LC_ALL=C awk -v b="$(sizing "$1" 3)" 'BEGIN { print b / 2 }'; else echo 1; fi
}

patho_base() {
  local override default
  override="$(sizing "$1" 3)"
  [ "$(patho_kind "$1")" = linear ] && [ -n "$override" ] && { echo "$override"; return; }
  default="$(sed -n 's/.*benchmark[A-Za-z]* { size: \([0-9]*\).*/\1/p' "$PATHO/src/$(echo "$1" | tr . /).purs" | head -1)"
  case "$(patho_kind "$1")" in
    depth) echo "$((default - 1))" ;;
    *) echo "$(((default + 1) / 2))" ;;
  esac
}

patho_size() { # kind base step(0..3)
  case "$1" in
    depth) echo "$(($2 + $3))" ;;
    *) echo "$(($2 << $3))" ;;
  esac
}

# Prints the best time in ms of one run, TIMEOUT or FAIL.
patho_time() { # name runtime size [repetitions] [timeout]
  local name="$1" runtime="$2" size="$3" repetitions="${4:-$REPETITIONS}" limit="${5:-$TIMEOUT}"
  local out="$WORK/patho-runs/$1.$2.$3" status
  mkdir -p "$WORK/patho-runs"
  case "$runtime" in
    go) PATHO_SIZE="$size" PATHO_REPETITIONS="$repetitions" timeout "$limit" "$WORK/patho/go/$name/program" >"$out.out" 2>"$out.err" ;;
    bun) (cd "$WORK/patho" && PATHO_SIZE="$size" PATHO_REPETITIONS="$repetitions" timeout "$limit" bun run.mjs "$name") >"$out.out" 2>"$out.err" ;;
    deno) (cd "$WORK/patho" && PATHO_SIZE="$size" PATHO_REPETITIONS="$repetitions" timeout "$limit" deno run -A run.mjs "$name") >"$out.out" 2>"$out.err" ;;
  esac
  status=$?
  if [ "$status" = 124 ]; then echo TIMEOUT; return; fi
  local best
  best="$(sed -n 's/^BENCH \([0-9.]*\) .*/\1/p' "$out.err" | tail -1)"
  if [ "$status" != 0 ] || [ -z "$best" ]; then echo FAIL; return; fi
  echo "$best"
}

# The n at which one run of this runtime takes between GROW_MS and CALIBRATE_MS (two warm runs, so
# that the JS engines are timed after their JIT has run).
calibrate() { # name runtime kind base
  local name="$1" runtime="$2" kind="$3" base="$4" ms attempt shrunk=0
  local largest=$((1 << 28))
  [ "$kind" = depth ] && largest=$((base + 6))
  for attempt in $(seq 16); do
    ms="$(patho_time "$name" "$runtime" "$base" 2 "${CALIBRATE_TIMEOUT:-30}")"
    case "$ms" in
      TIMEOUT) shrunk=1; base="$([ "$kind" = depth ] && echo $((base - 2)) || echo $(((base + 7) / 8)))" ;;
      FAIL) break ;;
      *)
        if LC_ALL=C awk -v ms="$ms" -v limit="$CALIBRATE_MS" 'BEGIN { exit !(ms > limit) }'; then
          shrunk=1; base="$([ "$kind" = depth ] && echo $((base - 1)) || echo $(((base + 1) / 2)))"
        elif [ "$shrunk" = 0 ] && [ "$base" -lt "$largest" ] && LC_ALL=C awk -v ms="$ms" -v grow="$GROW_MS" 'BEGIN { exit !(ms < grow) }'; then
          base="$([ "$kind" = depth ] && echo $((base + 1)) || echo $((base * 2)))"
        else
          break
        fi ;;
    esac
    [ "$base" -ge 1 ] || { base=1; break; }
  done
  echo "$base"
}

patho_names() {
  grep -rl '^hypothesis = ' "$PATHO/src" | sort | while read -r file; do
    sed -n 's/^module \([A-Za-z0-9.]*\).*/\1/p' "$file"
  done
}

run_patho() {
  local names=() name
  while IFS= read -r name; do
    matches "$name" || continue
    [ "$(patho_kind "$name")" = skip ] && { echo "skip $name" >&2; continue; }
    names+=("$name")
  done < <(patho_names)
  [ "${#names[@]}" -gt 0 ] || return 0
  if [ "${SKIP_BUILD:-0}" != 1 ]; then
    echo "building ${#names[@]} pathological benchmarks ..." >&2
    BUILD_ONLY=1 WORK="$WORK/patho" JOBS="$JOBS" "$PATHO/run.sh" "${names[@]}" >"$WORK/patho-build.log" 2>&1 \
      || { echo "pathological build failed, see $WORK/patho-build.log" >&2; tail -5 "$WORK/patho-build.log" >&2; }
  fi
  for name in "${names[@]}"; do
    [ -x "$WORK/patho/go/$name/program" ] || { printf 'patho\t%s\t-\t%s\tMISSING\t-\n' "$name" "$(patho_kind "$name")" >>"$ROWS"; continue; }
    wait_for_quiet_machine
    local base kind load runtime bases=()
    base="$(patho_base "$name")" kind="$(patho_kind "$name")" load="$(load_average)"
    for runtime in $RUNTIMES; do bases+=("$(calibrate "$name" "$runtime" "$kind" "$base")"); done
    echo "timing $name ($kind, n = ${bases[*]} for $RUNTIMES, load $load)" >&2
    measure_patho "$name" "$kind" "$load" "${bases[@]}"
  done
}

measure_patho() { # name kind load base...
  local name="$1" kind="$2" load="$3"; shift 3
  local bases=("$@") runtime step index=0 times=()
  for runtime in $RUNTIMES; do
    local row=""
    for step in 0 1 2; do row+="$(patho_time "$name" "$runtime" "$(patho_size "$kind" "${bases[$index]}" "$step")") "; done
    times+=("$row")
    index=$((index + 1))
  done
  local verdict scale
  scale="$(patho_scale "$name")"
  verdict="$(classify ratio "$scale" "${times[@]}")"
  if [ "$verdict" = CANDIDATE ]; then
    local extended=()
    index=0
    for runtime in $RUNTIMES; do
      extended+=("${times[$index]}$(patho_time "$name" "$runtime" "$(patho_size "$kind" "${bases[$index]}" 3)")")
      index=$((index + 1))
    done
    times=("${extended[@]}")
    verdict="$(classify ratio "$scale" "${times[@]}")"
  fi
  local label="$kind"
  [ "$kind" = depth ] && label="depth/$scale"
  row "patho" "$name" "$(IFS=/; echo "${bases[*]}")" "$label" "$verdict" "$load" "${times[@]}"
}

# ---------------------------------------------------------------- compatibility corpus
#
# Corpus programs have no size parameter, so compat-scales.txt names, per program, a literal in its
# source and the base n it is replaced with. Each scale gets its own copy of the corpus built by
# the corpus's run.sh; programs are timed as whole processes, and the ratio uses increments,
# r = (t(4n) - t(2n)) / (t(2n) - t(n)), which cancels start-up time (2 for linear, 4 for quadratic).
# The scales are compiled ahead, so all runtimes share n.

COMPAT="$GO_DIR/benchmarks/compat"

compat_entries() { grep -v '^#' "$HERE/compat-scales.txt" | grep -v '^[[:space:]]*$'; }

build_compat_scale() { # step programs...
  local step="$1"; shift
  local copy="$WORK/compat-copy-$step"
  rm -rf "$copy"
  mkdir -p "$copy"
  (cd "$COMPAT" && tar --exclude .spago --exclude output --exclude node_modules -cf - .) | (cd "$copy" && tar -xf -)
  local module pattern template base
  while IFS='|' read -r module pattern template base; do
    matches "$module" || continue
    local file="$copy/src/$(echo "$module" | tr . /).purs"
    [ -f "$file" ] || file="$copy/repro/src/$(echo "$module" | tr . /).purs"
    local replacement="${template//@N@/$((base << step))}"
    perl -0pi -e "s/$pattern/$replacement/g" "$file"
    grep -qF -- "$replacement" "$file" || echo "compat-scales: $module: pattern /$pattern/ did not match" >&2
  done < <(compat_entries)
  echo "building compat scale $step ..." >&2
  # Go builds land in WORK/compat-<step>/go/<program>/program and the JS build in
  # WORK/compat-<step>/es; the corpus's own OK / IRIS ERROR / ... table is in compat-build-<step>.log.
  WORK="$WORK/compat-$step" JOBS="$JOBS" "$copy/run.sh" "$@" >"$WORK/compat-build-$step.log" 2>&1
  return 0
}

compat_time() { # name runtime step
  local name="$1" runtime="$2" step="$3" dir="$WORK/compat-$3" best="" attempt
  for attempt in $(seq "$REPETITIONS"); do
    local start end status ms
    start="$(perl -MTime::HiRes=time -e 'printf "%.6f", time')"
    case "$runtime" in
      go) timeout "$TIMEOUT" "$dir/go/$name/program" >"$dir/$name.$runtime.out" 2>/dev/null ;;
      bun) (cd "$dir" && timeout "$TIMEOUT" bun run.mjs "$name") >"$dir/$name.$runtime.out" 2>/dev/null ;;
      deno) (cd "$dir" && timeout "$TIMEOUT" deno run -A run.mjs "$name") >"$dir/$name.$runtime.out" 2>/dev/null ;;
    esac
    status=$?
    end="$(perl -MTime::HiRes=time -e 'printf "%.6f", time')"
    [ "$status" = 124 ] && { echo TIMEOUT; return; }
    [ "$status" = 0 ] || { echo FAIL; return; }
    ms="$(LC_ALL=C awk -v a="$start" -v b="$end" 'BEGIN { printf "%.3f", (b - a) * 1000 }')"
    if [ -z "$best" ] || LC_ALL=C awk -v a="$ms" -v b="$best" 'BEGIN { exit !(a < b) }'; then best="$ms"; fi
  done
  echo "$best"
}

run_compat() {
  local unique=() module
  while IFS= read -r module; do matches "$module" && unique+=("$module"); done \
    < <(compat_entries | cut -d'|' -f1 | awk '!seen[$0]++')
  [ "${#unique[@]}" -gt 0 ] || return 0
  if [ "${SKIP_BUILD:-0}" != 1 ]; then
    local step
    for step in 0 1 2 3; do build_compat_scale "$step" "${unique[@]}"; done
  fi
  for module in "${unique[@]}"; do
    if [ ! -x "$WORK/compat-0/go/$module/program" ]; then
      local why
      why="$(grep -F "| $module |" "$WORK/compat-build-0.log" 2>/dev/null | cut -d'|' -f3 | sed 's/^ *//; s/ *$//' | cut -c1-60)"
      printf 'compat\t%s\t-\tincrement\tMISSING (%s)\t-\n' "$module" "${why:-not built}" >>"$ROWS"
      continue
    fi
    wait_for_quiet_machine
    local load base runtime step times=() mismatch=""
    load="$(load_average)"
    base="$(compat_entries | awk -F'|' -v m="$module" '$1 == m { print $4; exit }')"
    echo "timing $module (n = $base, literal, load $load)" >&2
    for runtime in $RUNTIMES; do
      local row=""
      for step in 0 1 2; do row+="$(compat_time "$module" "$runtime" "$step") "; done
      times+=("$row")
      # The outputs at 4n must agree; a divergence is a correctness finding.
      [ "$runtime" = go ] || cmp -s "$WORK/compat-2/$module.go.out" "$WORK/compat-2/$module.$runtime.out" || mismatch="$runtime"
    done
    local verdict
    verdict="$(classify increment 1 "${times[@]}")"
    if [ "$verdict" = CANDIDATE ]; then
      local extended=() index=0
      for runtime in $RUNTIMES; do extended+=("${times[$index]}$(compat_time "$module" "$runtime" 3)"); index=$((index + 1)); done
      times=("${extended[@]}")
      verdict="$(classify increment 1 "${times[@]}")"
    fi
    [ -n "$mismatch" ] && verdict="$verdict+MISMATCH($mismatch)"
    row compat "$module" "$base" increment "$verdict" "$load" "${times[@]}"
  done
}

# ---------------------------------------------------------------- verdicts and report

row() { # suite name n kind verdict load times...
  local suite="$1" name="$2" n="$3" kind="$4" verdict="$5" load="$6"; shift 6
  printf '%s\t%s\t%s\t%s\t%s\t%s' "$suite" "$name" "$n" "$kind" "$verdict" "$load" >>"$ROWS"
  local column
  for column in "$@"; do printf '\t%s' "$column" >>"$ROWS"; done
  printf '\n' >>"$ROWS"
}

# The growth ratios r(4n/2n) and r(8n/4n) of one "t0 t1 t2 [t3]" column, shared by classify and
# report: `ratio` is t(4n)/t(2n), `increment` is (t(4n)-t(2n))/(t(2n)-t(n)), both divided by scale.
RATIO_AWK='
  function growth(mode, scale, a, b, c) {
    if (a !~ /^[0-9.]+$/ || b !~ /^[0-9.]+$/ || c !~ /^[0-9.]+$/) return -1
    if (mode == "increment") return (b - a) > 0 ? (c - b) / (b - a) / scale : 99
    return b > 0 ? c / b / scale : 99
  }'

# classify mode scale "go t0 t1 t2 [t3]" "bun ..." ["deno ..."]
classify() {
  local mode="$1" scale="$2"; shift 2
  LC_ALL=C awk -v mode="$mode" -v scale="$scale" -v go_ratio="$GO_RATIO" -v js_ratio="$JS_RATIO" \
    -v min_ms="$MIN_MS" -v columns="$*" -v count="$#" "$RATIO_AWK"'
    BEGIN {
      # One argument per runtime: go first, then the JS engines.
      n = split(columns, flat, " ")
      per = n / count
      for (r = 0; r < count; r++) for (s = 0; s < per; s++) t[r, s] = flat[r * per + s + 1]
      for (r = 0; r < count; r++) for (s = 0; s < per; s++) {
        if (t[r, s] == "TIMEOUT") { print (r == 0 ? "GO-TIMEOUT" : "JS-TIMEOUT"); exit }
        if (t[r, s] == "FAIL") { print (r == 0 ? "GO-FAIL" : "JS-FAIL"); exit }
      }
      for (r = 0; r < count; r++) {
        fast = mode == "increment" ? t[r, 1] - t[r, 0] : t[r, 1]
        if (fast < min_ms) { print "TOO-FAST"; exit }
      }
      go = growth(mode, scale, t[0, 0], t[0, 1], t[0, 2])
      js = 99; js_high = 0
      for (r = 1; r < count; r++) {
        x = growth(mode, scale, t[r, 0], t[r, 1], t[r, 2])
        if (x < js) js = x
        if (x > js_high) js_high = x
      }
      if (go > go_ratio && js < js_ratio) {
        if (per < 4) { print "CANDIDATE"; exit }
        print (growth(mode, scale, t[0, 1], t[0, 2], t[0, 3]) > go_ratio ? "GO-SUPERLINEAR" : "UNCONFIRMED"); exit
      }
      if (go > go_ratio && js > go_ratio) { print "BOTH-SUPERLINEAR"; exit }
      print "OK"
    }'
}

report() {
  LC_ALL=C awk -F'\t' -v runtimes="$RUNTIMES" "$RATIO_AWK"'
    function mode_of(kind) { return kind == "increment" ? "increment" : "ratio" }
    function scale_of(kind,   parts) { if (split(kind, parts, "/") == 2) return parts[2]; return 1 }
    function ratios(kind, list,   t, k, r, r8) {
      k = split(list, t, " ")
      r = growth(mode_of(kind), scale_of(kind), t[1], t[2], t[3])
      if (r < 0) return "-"
      r8 = k >= 4 ? growth(mode_of(kind), scale_of(kind), t[2], t[3], t[4]) : -1
      return sprintf("%.2f", r) (r8 >= 0 ? sprintf(" (8n %.2f)", r8) : "")
    }
    function times(list,   t, k, s, out) {
      k = split(list, t, " "); out = ""
      for (s = 1; s <= k; s++) out = out (s > 1 ? " / " : "") (t[s] ~ /^[0-9.]+$/ ? sprintf("%.0f", t[s]) : t[s])
      return out
    }
    BEGIN {
      nr = split(runtimes, names, " ")
      printf "| suite | program | n (%s) | kind | load | ", runtimes
      for (r = 1; r <= nr; r++) printf "%s ms (n/2n/4n[/8n]) | ", names[r]
      for (r = 1; r <= nr; r++) printf "r %s | ", names[r]
      printf "verdict |\n|---|---|---:|---|---:|"
      for (r = 1; r <= 2 * nr; r++) printf "---:|"
      printf "---|\n"
    }
    {
      printf "| %s | %s | %s | %s | %s | ", $1, $2, $3, $4, $6
      for (r = 1; r <= nr; r++) printf "%s | ", times($(6 + r))
      for (r = 1; r <= nr; r++) printf "%s | ", ratios($4, $(6 + r))
      printf "%s |\n", $5
    }' "$ROWS"
  echo
  echo "Ranked Go-only super-linear findings (r(go) / min r(js)):"
  LC_ALL=C awk -F'\t' "$RATIO_AWK"'
    function value(kind, list,   t, parts, scale) {
      split(list, t, " "); scale = split(kind, parts, "/") == 2 ? parts[2] : 1
      return growth(kind == "increment" ? "increment" : "ratio", scale, t[1], t[2], t[3])
    }
    $5 ~ /^(GO-SUPERLINEAR|UNCONFIRMED|GO-TIMEOUT)/ {
      go = value($4, $7); js = 99
      for (i = 8; i <= NF; i++) { x = value($4, $i); if (x > 0 && x < js) js = x }
      printf "%8.2f  %-16s %s %s (r go %.2f, best r js %.2f)\n", (js > 0 && js < 99 ? go / js : 0), $5, $1, $2, go, js
    }' "$ROWS" | sort -rn | sed 's/^/  /'
  echo
  echo "Both Go and JS super-linear (information):"
  awk -F'\t' '$5 ~ /^BOTH-SUPERLINEAR/ { print "  " $1 " " $2 }' "$ROWS"
  echo
  echo "Not measured or failing:"
  awk -F'\t' '$5 !~ /^(OK|GO-SUPERLINEAR|UNCONFIRMED|BOTH-SUPERLINEAR)$/ { print "  " $1 " " $2 ": " $5 }' "$ROWS"
  echo
  LC_ALL=C awk -F'\t' '$6 ~ /^[0-9.]+$/ { sum += $6; count++; if ($6 + 0 > high) high = $6 + 0 }
    END { if (count) printf "load average (1 min) before each program: mean %.1f, highest %.1f\n", sum / count, high }' "$ROWS"
  echo "thresholds: GO_RATIO=$GO_RATIO JS_RATIO=$JS_RATIO MIN_MS=$MIN_MS GROW_MS=$GROW_MS CALIBRATE_MS=$CALIBRATE_MS REPETITIONS=$REPETITIONS; rows in $ROWS"
}

: >"$ROWS"
case "$suite" in
  patho) run_patho ;;
  compat) run_compat ;;
  all) run_patho; run_compat ;;
esac
report
grep -q $'\t\\(GO-SUPERLINEAR\\|GO-TIMEOUT\\)' "$ROWS" && exit 1
exit 0
