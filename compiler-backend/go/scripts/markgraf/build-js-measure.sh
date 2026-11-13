#!/usr/bin/env bash
#
# Builds js-host/measure as a cdylib: the Tauri native host's measureText
# behind a C ABI, with the Markgraf CLI's bundled fonts, for js-host/host.js
# under Deno and Bun. Prints the path of the library.
#
#   compiler-backend/go/scripts/markgraf/build-js-measure.sh [OUT_DIR]
#
# Environment: MARKGRAF (checkout), CARGO_TARGET_DIR (defaults to the Markgraf
# CLI's own target directory so Skia is not rebuilt).

set -euo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
MARKGRAF="${MARKGRAF:-/Users/mark/Developer/markgraf}"
OUT="${1:-${TMPDIR:-/tmp}/markgraf-js-cli}"
CLI="$MARKGRAF/cli"
CRATE="$OUT/measure"
export CARGO_TARGET_DIR="${CARGO_TARGET_DIR:-$CLI/target}"

mkdir -p "$CRATE/src"
cp "$HERE/js-host/measure/lib.rs" "$CRATE/src/lib.rs"
{
  echo "fn fonts() -> Vec<FontAsset> {"
  echo "    vec!["
  # The FontAsset literals of the CLI's `fonts: vec![...]`, assets made absolute.
  awk '/fonts: vec!\[/ { inside = 1; next } inside && /^ *\],/ { exit } inside' "$CLI/native/main.rs" \
    | sed -e "s|\.\./assets/|$CLI/assets/|g"
  echo "    ]"
  echo "}"
} > "$CRATE/src/fonts.rs"
grep -q 'FontAsset {' "$CRATE/src/fonts.rs" || { echo "no fonts found in $CLI/native/main.rs" >&2; exit 1; }
cat > "$CRATE/Cargo.toml" <<TOML
[package]
name = "markgraf-measure"
version = "0.0.0"
edition = "2021"
publish = false

[lib]
crate-type = ["cdylib"]
path = "src/lib.rs"

[dependencies]
tauri-native-host = { path = "$MARKGRAF/../purescript-tauri/native/runtime" }

[profile.release]
lto = "thin"
strip = true
TOML
cp "$CLI/Cargo.lock" "$CRATE/Cargo.lock"
(cd "$CRATE" && cargo build --release --quiet) >"$OUT/measure.log" 2>&1 || { cat "$OUT/measure.log" >&2; exit 1; }
case "$(uname)" in
  Darwin) library=libmarkgraf_measure.dylib ;;
  *) library=libmarkgraf_measure.so ;;
esac
cp "$CARGO_TARGET_DIR/release/$library" "$OUT/$library"
echo "$OUT/$library"
