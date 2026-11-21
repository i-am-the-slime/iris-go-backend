#!/usr/bin/env bash
#
# Prints the size of the Go backend's own source, the lines of
# compiler-backend/go/src/**/*.rs, for information. It never fails.
#
#   compiler-backend/go/scripts/source-size.sh

set -uo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
SOURCE="${SOURCE:-$HERE/../src}"

current="$(find "$SOURCE" -name '*.rs' -type f -print0 | xargs -0 cat | wc -l | tr -d ' ')"
printf '%-16s %10s\n' "go-backend" "current"
printf '%-16s %10s  (info)\n' "source-lines" "$current"
