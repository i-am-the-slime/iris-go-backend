#!/usr/bin/env bash

set -euo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../../../.." && pwd)"
IRIS="${IRIS:-$ROOT/target/release/iris}"
MARKGRAF="${MARKGRAF:-/Users/mark/Developer/markgraf}"
LAYERED_LAYOUT="${LAYERED_LAYOUT:-$MARKGRAF/.spago/p/layered-layout/d7cf719be196556fe9e2d55b6ea1d6f4ca5a5713}"
GO_SUPPORT="${GO_SUPPORT:-/Users/mark/Developer/purs-backend-go/go-support}"
WORK="${WORK:-$(mktemp -d)}"

mkdir -p "$WORK/driver" "$WORK/go"
cp -R "$HERE/src" "$WORK/driver/"
sed "s|@LAYERED_LAYOUT@|$LAYERED_LAYOUT|" "$HERE/spago.yaml.in" > "$WORK/driver/spago.yaml"

cd "$WORK/driver"
spago build --quiet >"$WORK/spago.log" 2>&1 || { cat "$WORK/spago.log"; exit 1; }
bun --eval "import('$WORK/driver/output/CompactionDriver/index.js').then(module => module.main())" >"$WORK/expected.txt"

cat > "$WORK/go/go.mod" <<GOMOD
module markgraf.example/compaction

go 1.27.0

require github.com/i-am-the-slime/purs-backend-go/go-support v0.0.0

replace github.com/i-am-the-slime/purs-backend-go/go-support => $GO_SUPPORT
GOMOD
started=$(perl -MTime::HiRes=time -e 'printf "%.0f", time*1000')
"$IRIS" go --entry CompactionDriver.main "$WORK/go"
finished=$(perl -MTime::HiRes=time -e 'printf "%.0f", time*1000')
(cd "$WORK/go" && go build -gcflags="-c=$(sysctl -n hw.ncpu) -dwarf=false" -ldflags=-w -o compaction .)
"$WORK/go/compaction" >"$WORK/actual.txt"

if ! diff -u "$WORK/expected.txt" "$WORK/actual.txt"; then
  echo "Markgraf compaction: JavaScript and Go differ (work directory $WORK)"
  exit 1
fi
echo "Markgraf compaction: JavaScript and Go match exactly (iris go $((finished - started)) ms)"
[ "${KEEP:-0}" = 1 ] || rm -rf "$WORK"
