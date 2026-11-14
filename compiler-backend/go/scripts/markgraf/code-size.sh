#!/usr/bin/env bash
#
# Attributes the lines and closures of generated Go to their likely causes:
# duplicate functions modulo renaming, specialisation families, statements
# that inlining repeats, and closures by kind. See codesize/main.go.
#
#   compiler-backend/go/scripts/markgraf/code-size.sh GENERATED_DIR_OR_FILE
#
# Build the Markgraf CLI's Go first with build-go-cli.sh OUT_DIR.

set -euo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
target="${1:?usage: code-size.sh GENERATED_DIR_OR_FILE}"
[ -d "$target" ] && target="$target/main.go"
tool="$(mktemp -d)"
trap 'rm -rf "$tool"' EXIT
(cd "$HERE/codesize" && go build -o "$tool/codesize" main.go)
"$tool/codesize" "$target"
