#!/usr/bin/env bash
#
# Runs the test suites of core registry packages under JavaScript (purs's own JS codegen, Bun) and Go
# (`iris go`), with JavaScript as the oracle, and prints one row per suite:
#
#   suite | js | go | detail
#
# where `go` is one of OK (same stdout and exit status as JS), IRIS ERROR, GO BUILD ERROR,
# RUNTIME PANIC, EXIT MISMATCH or OUTPUT MISMATCH, and `detail` names the first blocker or the
# first differing lines.
#
# The first suite, lcg-parity (scripts/robust/suites/lcg-parity), prints Random.LCG steps and
# thousands of QuickCheck-generated Ints, Numbers, Chars, Strings and Arrays from fixed seeds, so
# that a mismatch there says the random streams themselves diverge and every QuickCheck result
# below it is meaningless.
#
# Determinism: QuickCheck seeds every `quickCheck` call from Random.LCG.randomSeed, which reads
# Effect.Random. Every suite project replaces the registry `lcg` with a vendored copy whose
# `randomSeed` is `pure (mkSeed 20261115)`, so both backends test the same generated cases and
# print the same counterexamples. Nothing else in the test sources is changed.
#
# The test sources are each package's `test/` directory at the git tag of the version in the
# registry package set (registry tarballs carry no tests). A suite's dependencies are the package
# itself plus its bower.json dependencies and devDependencies.
#
#   compiler-backend/go/scripts/robust/suites.sh                # every suite
#   compiler-backend/go/scripts/robust/suites.sh strings lists  # name filters
#   compiler-backend/go/scripts/robust/suites.sh repro          # the minimal reproductions of
#                                                               # findings (suites/repro), each
#                                                               # one program
#
# The oracle is purs's JS output rather than purs-backend-es: backend-es 1.4 cannot decode the
# corefn of string literals holding lone surrogates (strings' CodePoints tests), which purs
# encodes as arrays of code units.
#
# Environment: IRIS, GO_SUPPORT, WORK (kept between runs; repositories are
# cloned once), JOBS, TIMEOUT, GOEXPERIMENT (default simd).

set -uo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../../../.." && pwd)"
IRIS="${IRIS:-$ROOT/target/release/iris}"
[ -x "$IRIS" ] || IRIS=/Users/mark/Developer/purescript-iris/target/release/iris
GO_SUPPORT="${GO_SUPPORT:-/Users/mark/Developer/purs-backend-go/go-support}"
export GOEXPERIMENT="${GOEXPERIMENT:-simd}"
WORK="${WORK:-${TMPDIR:-/tmp}/iris-robust-suites}"
JOBS="${JOBS:-4}"
TIMEOUT="${TIMEOUT:-300}"
PACKAGE_SET=75.9.1
SEED=20261115
mkdir -p "$WORK/repos" "$WORK/projects"

# name | GitHub repository | tag (the package set's version)
SUITES="
arrays|purescript/purescript-arrays|v7.3.0
strings|purescript/purescript-strings|v6.0.1
integers|purescript/purescript-integers|v6.0.0
numbers|purescript/purescript-numbers|v9.0.1
ordered-collections|purescript/purescript-ordered-collections|v3.2.0
lists|purescript/purescript-lists|v7.0.0
foldable-traversable|purescript/purescript-foldable-traversable|v6.0.0
quickcheck|purescript/purescript-quickcheck|v8.0.1
quickcheck-laws|purescript-contrib/purescript-quickcheck-laws|v7.0.0
foreign-object|purescript/purescript-foreign-object|v4.1.0
prelude|purescript/purescript-prelude|v6.0.2
enums|purescript/purescript-enums|v6.0.1
either|purescript/purescript-either|v6.1.0
nonempty|purescript/purescript-nonempty|v7.0.0
unfoldable|purescript/purescript-unfoldable|v6.0.0
control|purescript/purescript-control|v6.0.0
st|purescript/purescript-st|v6.2.0
tailrec|purescript/purescript-tailrec|v6.1.0
unicode|purescript-contrib/purescript-unicode|v6.0.0
"

# Extra entry points into a suite, so that one blocked test module does not hide the others:
# suite | label | module | body of `main` (the module is imported as T). Each runs as its own
# program next to the suite's Test.Main.
#
# prelude has no splits: its tests are `Unit -> Unit` functions (AlmostEff) whose only effect is
# a foreign throw, and optimizing backends (iris and purs-backend-es alike) fold `show (test unit)`
# to "unit" without running them, so a split would pass vacuously.
SPLITS="
strings|String|Test.Data.String|T.testString
strings|CaseInsensitive|Test.Data.String.CaseInsensitive|T.testCaseInsensitiveString
strings|CodePoints|Test.Data.String.CodePoints|T.testStringCodePoints
strings|CodeUnits|Test.Data.String.CodeUnits|T.testStringCodeUnits
strings|NonEmpty|Test.Data.String.NonEmpty|T.testNonEmptyString
strings|NonEmptyCodeUnits|Test.Data.String.NonEmpty.CodeUnits|T.testNonEmptyStringCodeUnits
strings|Regex|Test.Data.String.Regex|T.testStringRegex
strings|Unsafe|Test.Data.String.Unsafe|T.testStringUnsafe
arrays|Array|Test.Data.Array|T.testArray
arrays|ArrayST|Test.Data.Array.ST|T.testArrayST
arrays|ArrayPartial|Test.Data.Array.Partial|T.testArrayPartial
arrays|ArraySTPartial|Test.Data.Array.ST.Partial|T.testArraySTPartial
arrays|NonEmptyArray|Test.Data.Array.NonEmpty|T.testNonEmptyArray
ordered-collections|Map|Test.Data.Map|T.mapTests
ordered-collections|Set|Test.Data.Set|T.setTests
"

suite_names() { echo "$SUITES" | grep . | cut -d'|' -f1; }

selected() {
  echo lcg-parity
  if [ "$#" -eq 0 ]; then suite_names; echo repro; else for f in "$@"; do { suite_names; echo repro; } | grep -F -- "$f"; done | awk '!seen[$0]++'; fi
}

clone() {
  local name="$1" repo="$2" tag="$3" dir="$WORK/repos/$1"
  [ -d "$dir/.git" ] && return
  git -c advice.detachedHead=false clone -q --depth 1 --branch "$tag" "https://github.com/$repo" "$dir"
}

# The registry lcg with a fixed randomSeed.
vendor_lcg() {
  local dir="$WORK/lcg"
  [ -f "$dir/spago.yaml" ] && return
  clone lcg purescript/purescript-lcg v4.0.0
  mkdir -p "$dir"
  cp -R "$WORK/repos/lcg/src" "$dir/"
  sed -i '' "s/^randomSeed = mkSeed <\$> randomInt seedMin seedMax$/randomSeed = pure (mkSeed $SEED)/" "$dir/src/Random/LCG.purs"
  grep -q "^randomSeed = pure (mkSeed $SEED)" "$dir/src/Random/LCG.purs" || { echo "lcg patch failed"; exit 1; }
  cat >"$dir/spago.yaml" <<YAML
package:
  name: lcg
  dependencies: [effect, integers, maybe, numbers, partial, prelude, random]
YAML
}

dependencies_of() {
  local name="$1" bower="$WORK/repos/$1/bower.json"
  {
    echo "$name"
    echo console; echo effect; echo prelude
    bun -e "const b = require('$bower'); for (const d of Object.keys({...b.dependencies, ...b.devDependencies})) console.log(d.replace(/^purescript-/, ''))"
  } | grep -vx 'psci-support' | sort -u
}

make_project() {
  local name="$1" project="$WORK/projects/$1"
  rm -rf "$project"
  mkdir -p "$project/src"
  if [ "$name" = lcg-parity ]; then
    cp -R "$HERE/suites/lcg-parity/src/." "$project/src/"
    printf '%s\n' arrays console effect foldable-traversable integers lcg maybe partial prelude quickcheck strings tuples >"$project/deps"
  elif [ "$name" = repro ]; then
    cp -R "$HERE/suites/repro/src/." "$project/src/"
    cp "$HERE/suites/repro/deps" "$project/deps"
  else
    cp -R "$WORK/repos/$name/test/." "$project/src/"
    dependencies_of "$name" >"$project/deps"
  fi
  # Go ports of the test-only foreigns: purescript-assert and quickcheck's float32ToInt32 for
  # every suite, plus a suite's own test/*.js foreigns from go-ffi-<suite>.
  cp -R "$HERE/suites/go-ffi" "$project/go-ffi"
  [ -d "$HERE/suites/go-ffi-$name" ] && cp -R "$HERE/suites/go-ffi-$name/." "$project/go-ffi/"
  [ "$name" = repro ] && cp -R "$HERE/suites/repro/go-ffi/." "$project/go-ffi/"
  # A suite's patch-<suite>.sh rewrites test code that relies on the JS representation of a type
  # (each patch says what and why); it runs in the project's src directory.
  [ -f "$HERE/suites/patch-$name.sh" ] && (cd "$project/src" && bash "$HERE/suites/patch-$name.sh")
  {
    echo "package:"
    echo "  name: robust-suite-$name"
    echo "  dependencies:"
    sed 's/^/    - /' "$project/deps"
    echo "workspace:"
    echo "  packageSet:"
    echo "    registry: $PACKAGE_SET"
    echo "  extraPackages:"
    echo "    lcg:"
    echo "      path: $WORK/lcg"
  } >"$project/spago.yaml"
  # The units: the suite's own entry module (Test.Main, or Main), then its SPLITS.
  if [ "$name" = repro ]; then
    # Every module of suites/repro is one minimal reproduction of a finding, run on its own.
    ls "$project/src" | sed -n 's/^Repro\(.*\)\.purs$/\1 Repro\1/p' >"$project/units.txt"
    return
  fi
  if grep -rqs '^module Test.Main' "$project/src"; then echo "main Test.Main" >"$project/units.txt"; else echo "main Main" >"$project/units.txt"; fi
  echo "$SPLITS" | grep "^$name|" | while IFS='|' read -r _ label module body; do
    mkdir -p "$project/src/Robust/Entry"
    printf 'module Robust.Entry.%s where\n\nimport Prelude\nimport Effect (Effect)\nimport Effect.Console (log)\nimport %s as T\n\nmain :: Effect Unit\nmain = %s\n' \
      "$label" "$module" "$body" >"$project/src/Robust/Entry/$label.purs"
    echo "$label Robust.Entry.$label" >>"$project/units.txt"
  done
}

build_js() {
  local project="$1"
  (cd "$project" && spago build) >"$project/spago.log" 2>&1
}

build_go() {
  local project="$1" unit="$2" entry="$3" out="$1/units/$2/go"
  rm -rf "$out"
  mkdir -p "$out"
  cat >"$out/go.mod" <<GOMOD
module robust.example/suite

go 1.27.0

require github.com/i-am-the-slime/purs-backend-go/go-support v0.0.0

replace github.com/i-am-the-slime/purs-backend-go/go-support => $GO_SUPPORT
GOMOD
  if ! (cd "$project" && IRIS_GO_ANY_CENSUS=1 timeout 600 "$IRIS" go --entry "$entry.main" "$out") >"$out/../iris.log" 2>&1; then
    echo iris >"$out/../stage"; return
  fi
  if ! (cd "$out" && go build -o program .) >"$out/../gobuild.log" 2>&1; then
    echo go-build >"$out/../stage"; return
  fi
  echo built >"$out/../stage"
}

run_unit() {
  local project="$1" unit="$2" entry="$3" dir="$1/units/$2"
  mkdir -p "$dir"
  echo "import { main } from \"../../output/$entry/index.js\"; main();" >"$dir/run.mjs"
  (cd "$dir" && timeout "$TIMEOUT" bun run.mjs) >"$dir/js.out" 2>"$dir/js.err"
  echo $? >"$dir/js.status"
  build_go "$project" "$unit" "$entry"
  [ "$(cat "$dir/stage")" = built ] || return
  (cd "$dir" && timeout "$TIMEOUT" go/program) >"$dir/go.out" 2>"$dir/go.err"
  echo $? >"$dir/go.status"
}

run_suite() {
  local name="$1" project="$WORK/projects/$1"
  if [ "$name" != lcg-parity ] && [ "$name" != repro ]; then
    local line; line="$(echo "$SUITES" | grep "^$name|")"
    clone "$name" "$(echo "$line" | cut -d'|' -f2)" "$(echo "$line" | cut -d'|' -f3)" || { mkdir -p "$project"; echo clone >"$project/stage"; return; }
  fi
  make_project "$name"
  if ! build_js "$project"; then echo js-build >"$project/stage"; return; fi
  while read -r unit entry; do run_unit "$project" "$unit" "$entry"; done <"$project/units.txt"
}
export -f run_suite run_unit make_project build_js build_go clone dependencies_of
export HERE IRIS GO_SUPPORT WORK TIMEOUT PACKAGE_SET SEED SUITES SPLITS

first_error() { grep -v '^go:' "$1" | grep -m1 -iE 'cannot|error|unknown|not ' | cut -c1-200; }

# classify <unit directory>: js|go|detail
classify() {
  local dir="$1" js
  js="$(if [ "$(cat "$dir/js.status")" = 0 ]; then echo pass; else echo "fail (exit $(cat "$dir/js.status"))"; fi)"
  case "$(cat "$dir/stage" 2>/dev/null)" in
    iris) echo "$js|IRIS ERROR|$(first_error "$dir/iris.log")"; return ;;
    go-build) echo "$js|GO BUILD ERROR|$(grep -m1 -v '^#' "$dir/gobuild.log" | cut -c1-200)"; return ;;
    built) ;;
    *) echo "$js|-|not run"; return ;;
  esac
  if grep -q '^panic: \|^fatal error: ' "$dir/go.err" && [ "$(cat "$dir/js.status")" = 0 ]; then
    echo "$js|RUNTIME PANIC|after $(wc -l <"$dir/go.out" | tr -d ' ') of $(wc -l <"$dir/js.out" | tr -d ' ') lines; last line \"$(tail -1 "$dir/go.out" | cut -c1-80)\"; $(grep -m1 -A3 '^panic: \|^fatal error: ' "$dir/go.err" | grep -v '^$\|^goroutine' | tr '\n' ' ' | cut -c1-200)"; return
  fi
  if ! cmp -s "$dir/js.out" "$dir/go.out"; then
    echo "$js|OUTPUT MISMATCH|$(diff "$dir/js.out" "$dir/go.out" | grep -m4 '^[<>]' | tr '\n' ' ' | cut -c1-300)"; return
  fi
  # An uncaught exception exits with status 1 in both, also one thrown while the program loads.
  if [ "$(cat "$dir/js.status")" != "$(cat "$dir/go.status")" ]; then
    echo "$js|EXIT MISMATCH|go exit $(cat "$dir/go.status"): $(tail -2 "$dir/go.err" | tr '\n' ' ' | cut -c1-200)"; return
  fi
  echo "$js|OK|$(wc -l <"$dir/js.out" | tr -d ' ') lines"
}

names=()
while IFS= read -r name; do names+=("$name"); done < <(selected "$@")
vendor_lcg
printf '%s\n' "${names[@]}" | xargs -P "$JOBS" -I{} bash -c 'run_suite "$1"' _ {}

printf '| suite | js | go | detail |\n|---|---|---|---|\n'
summary=""
for name in "${names[@]}"; do
  project="$WORK/projects/$name"
  case "$(cat "$project/stage" 2>/dev/null)" in
    js-build) row="JS BUILD ERROR|-|$(grep -m1 -A3 'ERROR' "$project/spago.log" | tr '\n' ' ' | cut -c1-200)"
      printf '| %s | %s |\n' "$name" "$(echo "$row" | sed 's/|/ | /g')"; summary+="-"$'\n'; continue ;;
    clone) printf '| %s | clone failed | - | - |\n' "$name"; continue ;;
  esac
  while read -r unit _; do
    row="$(classify "$project/units/$unit")"
    label="$name"; [ "$unit" = main ] || label="$name/$unit"
    printf '| %s | %s |\n' "$label" "$(echo "$row" | sed 's/|/ | /g')"
    summary+="$(echo "$row" | cut -d'|' -f2)"$'\n'
  done <"$project/units.txt"
done
echo
echo "$summary" | grep . | sort | uniq -c | sort -rn
echo "logs and outputs: $WORK/projects/<suite>/units/<unit>/{js.out,go.out,go.err,iris.log,gobuild.log}"
