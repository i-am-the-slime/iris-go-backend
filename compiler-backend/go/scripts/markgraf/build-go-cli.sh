#!/usr/bin/env bash
#
# Compiles the Markgraf CLI (Main.run) with `iris go` and builds it with the
# Markgraf host and fonts, exactly as compare-svg.sh does. Prints the path of
# the executable; the generated Go stays in OUT_DIR.
#
#   compiler-backend/go/scripts/markgraf/build-go-cli.sh OUT_DIR
#
# Environment: IRIS, MARKGRAF (checkout; pinned.sh), GO_SUPPORT, GOEXPERIMENT (default simd).

set -euo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../../../.." && pwd)"
IRIS="${IRIS:-$ROOT/target/release/iris}"
source "$(dirname "${BASH_SOURCE[0]}")/pinned.sh"
GO_SUPPORT="${GO_SUPPORT:-/Users/mark/Developer/purs-backend-go/go-support}"
# go-support scans strings sixteen bytes at a time with SIMD, an experiment
# in Go 1.27.0 (simd/archsimd) whose API may change in later releases.
export GOEXPERIMENT="${GOEXPERIMENT:-simd}"
OUT="$1"
FONTS="$MARKGRAF/cli/assets/native/fonts"

mkdir -p "$OUT/fonts"
# The generated packages import each other through the module go.mod names.
cat > "$OUT/go.mod" <<GOMOD
module markgraf.example/cli

go 1.27.0

require github.com/i-am-the-slime/purs-backend-go/go-support v0.0.0

replace github.com/i-am-the-slime/purs-backend-go/go-support => $GO_SUPPORT
GOMOD
(cd "$MARKGRAF/cli" && "$IRIS" go --entry Main.run "$OUT") >&2
cp "$HERE/host/host.go" "$OUT/"
for font in Ilisarniq-Demi.otf Ilisarniq-Italic.otf VictorMono-Medium.ttf VictorMono-Bold.ttf \
  VictorMono-MediumItalic.ttf VictorMono-BoldItalic.ttf; do
  cp "$FONTS/$font" "$OUT/fonts/"
done
# -tags libm: Math.sin and friends from the C library, as JavaScriptCore does.
# -c: compile each package on every core instead of four.
# -dwarf=false and -w: no DWARF; the compiler would generate it only for the
# linker to drop, and without it link time more than halves.
# The executable goes in bin/, since a package directory such as Markgraf/
# takes its name on a case-insensitive file system.
(cd "$OUT" && go build -tags libm -gcflags="-c=$(sysctl -n hw.ncpu) -dwarf=false" -ldflags=-w -o bin/markgraf .) >&2
echo "$OUT/bin/markgraf"
