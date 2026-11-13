#!/usr/bin/env bash
#
# Compiles the Markgraf CLI (Main.run) with `iris go` and builds it with the
# Markgraf host and fonts, exactly as compare-svg.sh does. Prints the path of
# the executable; the generated Go stays in OUT_DIR.
#
#   compiler-backend/go/scripts/markgraf/build-go-cli.sh OUT_DIR
#
# Environment: IRIS, MARKGRAF (checkout), GO_SUPPORT.

set -euo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../../../.." && pwd)"
IRIS="${IRIS:-$ROOT/target/release/iris}"
MARKGRAF="${MARKGRAF:-/Users/mark/Developer/markgraf}"
GO_SUPPORT="${GO_SUPPORT:-/Users/mark/Developer/purs-backend-go/go-support}"
OUT="$1"
FONTS="$MARKGRAF/cli/assets/native/fonts"

mkdir -p "$OUT/fonts"
(cd "$MARKGRAF/cli" && "$IRIS" go --entry Main.run "$OUT") >&2
cp "$HERE/host/host.go" "$OUT/"
for font in Ilisarniq-Demi.otf Ilisarniq-Italic.otf VictorMono-Medium.ttf VictorMono-Bold.ttf \
  VictorMono-MediumItalic.ttf VictorMono-BoldItalic.ttf; do
  cp "$FONTS/$font" "$OUT/fonts/"
done
cat > "$OUT/go.mod" <<GOMOD
module markgraf.example/cli

go 1.23.2

require github.com/i-am-the-slime/purs-backend-go/go-support v0.0.0

replace github.com/i-am-the-slime/purs-backend-go/go-support => $GO_SUPPORT
GOMOD
# -tags libm: Math.sin and friends from the C library, as JavaScriptCore does.
(cd "$OUT" && go build -tags libm -o markgraf .) >&2
echo "$OUT/markgraf"
