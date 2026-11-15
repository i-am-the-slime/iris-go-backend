#!/usr/bin/env bash
#
# Measures what the Go Markgraf CLI allocates: builds it with a report of
# runtime.MemStats added at exit, runs a `--frame 1` export of each file, and
# prints bytes and objects allocated per file plus the totals. The totals are
# what an allocation-reducing change is judged by.
#
#   compiler-backend/go/scripts/markgraf/allocations.sh              # default files
#   compiler-backend/go/scripts/markgraf/allocations.sh a.markgraf   # chosen files
#
# Environment: IRIS, MARKGRAF (checkout; pinned.sh), GO_SUPPORT, WORK (kept when set).

set -euo pipefail
export LC_ALL=C

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
source "$HERE/pinned.sh"
WORK="${WORK:-$(mktemp -d)}"
mkdir -p "$WORK/out"

if [ "$#" -eq 0 ]; then
  set -- "$MARKGRAF"/examples/*.markgraf
fi

"$HERE/build-go-cli.sh" "$WORK/go" >/dev/null
cat > "$WORK/go/memstats.go" <<'GO'
package main

import (
	"fmt"
	"os"
	"runtime"
)

// reportMemStats prints what the program allocated in total, for allocations.sh.
func reportMemStats() {
	var stats runtime.MemStats
	runtime.ReadMemStats(&stats)
	fmt.Fprintf(os.Stderr, "memstats %d %d\n", stats.TotalAlloc, stats.Mallocs)
}
GO
sed -i '' 's/^\tos\.Exit(int(exitStatus))$/\treportMemStats()\n\tos.Exit(int(exitStatus))/' "$WORK/go/main.go"
grep -q 'reportMemStats()' "$WORK/go/main.go" || { echo "allocations.sh: could not find main's os.Exit" >&2; exit 1; }
(cd "$WORK/go" && go build -tags libm -gcflags="-dwarf=false" -ldflags=-w -o bin/markgraf-memstats .)

total_bytes=0
total_objects=0
printf '%-32s %12s %12s\n' file MB objects
for input in "$@"; do
  name="$(basename "$input" .markgraf)"
  line="$(cd "$WORK/out" && "$WORK/go/bin/markgraf-memstats" "$input" --frame 1 -o "$name.svg" 2>&1 >/dev/null | grep '^memstats ' || true)"
  [ -n "$line" ] || { printf '%-32s %12s\n' "$name" "no report"; continue; }
  read -r _ bytes objects <<< "$line"
  total_bytes=$((total_bytes + bytes))
  total_objects=$((total_objects + objects))
  printf '%-32s %12.1f %12d\n' "$name" "$(echo "$bytes / 1000000" | bc -l)" "$objects"
done
printf '%-32s %12.1f %12d\n' TOTAL "$(echo "$total_bytes / 1000000" | bc -l)" "$total_objects"
