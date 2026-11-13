#!/usr/bin/env bash
#
# Builds the JavaScript reference `markgraf` CLI from the current Markgraf
# sources: purs → purs-backend-es → one IIFE engine embedded in the Rust
# tauri-native-host, exactly as cli/scripts/build-native.mjs does, but without
# writing into the Markgraf checkout. Prints the path of the executable.
#
#   compiler-backend/go/scripts/markgraf/build-js-cli.sh [OUT_DIR]
#
# Environment: MARKGRAF (checkout), CARGO_TARGET_DIR (defaults to the Markgraf
# CLI's own target directory so Skia is not rebuilt).

set -euo pipefail

MARKGRAF="${MARKGRAF:-/Users/mark/Developer/markgraf}"
OUT="${1:-${TMPDIR:-/tmp}/markgraf-js-cli}"
CLI="$MARKGRAF/cli"
NPM="$MARKGRAF/npm"
export CARGO_TARGET_DIR="${CARGO_TARGET_DIR:-$CLI/target}"
export PATH="$NPM/node_modules/.bin:$PATH"

mkdir -p "$OUT/crate/native" "$OUT/dist"
rm -rf "$OUT/corefn" "$OUT/optimized"

(cd "$CLI" && spago fetch >/dev/null 2>&1)
sources=()
while IFS= read -r source; do sources+=("$CLI/$source"); done < <(
  cd "$CLI" && spago sources --json 2>/dev/null | bun -e '
    const sources = JSON.parse(await Bun.stdin.text());
    for (const source of sources) if (!source.startsWith("test/")) console.log(source);'
)
purs compile "${sources[@]}" --codegen js,corefn --output "$OUT/corefn" >"$OUT/purs.log" 2>&1 \
  || { cat "$OUT/purs.log"; exit 1; }
(cd "$NPM" && purs-backend-es build --corefn-dir "$OUT/corefn" --output-dir "$OUT/optimized" >"$OUT/es.log" 2>&1) \
  || { cat "$OUT/es.log"; exit 1; }

cat > "$OUT/entry.js" <<JS
import { run } from "$OUT/optimized/Main/index.js";

globalThis.__purescriptMain = run;
JS
cat > "$OUT/vite.config.js" <<JS
import { isBuiltin } from "node:module";
export default {
  publicDir: false,
  logLevel: "warn",
  build: {
    target: "es2020",
    outDir: "$OUT/dist",
    emptyOutDir: true,
    lib: { entry: "$OUT/entry.js", name: "MarkgrafNativeEngine", formats: ["iife"], fileName: () => "engine.js" },
    rollupOptions: {
      external: isBuiltin,
      treeshake: { moduleSideEffects: false },
      output: { inlineDynamicImports: true },
    },
  },
};
JS
(cd "$NPM" && vite build --config "$OUT/vite.config.js" >"$OUT/vite.log" 2>&1) || { cat "$OUT/vite.log"; exit 1; }

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
