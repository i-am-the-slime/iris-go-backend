#!/usr/bin/env bash
#
# Builds the JavaScript reference `markgraf` CLI from the current Markgraf
# sources: the engine of build-js-engine.sh embedded in the Rust
# tauri-native-host, exactly as cli/scripts/build-native.mjs does, but without
# writing into the Markgraf checkout. Prints the path of the executable.
#
#   compiler-backend/go/scripts/markgraf/build-js-cli.sh [OUT_DIR]
#
# Environment: MARKGRAF (checkout; pinned.sh), CARGO_TARGET_DIR (defaults to the Markgraf
# CLI's own target directory so Skia is not rebuilt).

set -euo pipefail

source "$(dirname "${BASH_SOURCE[0]}")/pinned.sh"
OUT="${1:-${TMPDIR:-/tmp}/markgraf-js-cli}"
CLI="$MARKGRAF/cli"
export CARGO_TARGET_DIR="${CARGO_TARGET_DIR:-$CLI/target}"

mkdir -p "$OUT/crate/native"
"$(dirname "${BASH_SOURCE[0]}")/build-js-engine.sh" "$OUT" >/dev/null

sed -e "s|\.\./dist/engine.js|$OUT/dist/engine.js|" \
    -e "s|\.\./assets/|$CLI/assets/|g" \
    "$CLI/native/main.rs" > "$OUT/crate/native/main.rs"
cat > "$OUT/crate/Cargo.toml" <<TOML
[package]
name = "markgraf-js-reference"
version = "0.0.0"
edition = "2021"
publish = false

[[bin]]
name = "markgraf-js-reference"
path = "native/main.rs"

[dependencies]
tauri-native-host = { path = "$MARKGRAF/../purescript-tauri/native/runtime" }

[profile.release]
lto = "thin"
strip = true
TOML
cp "$CLI/Cargo.lock" "$OUT/crate/Cargo.lock"
(cd "$OUT/crate" && cargo build --release --quiet) >"$OUT/cargo.log" 2>&1 || { cat "$OUT/cargo.log"; exit 1; }
cp "$CARGO_TARGET_DIR/release/markgraf-js-reference" "$OUT/markgraf"
if [ "$(uname)" = Darwin ]; then
  # JavaScriptCore only compiles to native code with the JIT entitlement.
  codesign --force --sign - --options runtime \
    --entitlements "$MARKGRAF/desktop/src-tauri/Entitlements.plist" "$OUT/markgraf" 2>/dev/null
fi
echo "$OUT/markgraf"
