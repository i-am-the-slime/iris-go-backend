#!/usr/bin/env bash
#
# Builds the JavaScript engine of the reference `markgraf` CLI from the current
# Markgraf sources: purs → purs-backend-es → one IIFE that sets
# `globalThis.__purescriptMain`, exactly as cli/scripts/build-native.mjs does,
# but without writing into the Markgraf checkout. Prints the path of engine.js.
#
#   compiler-backend/go/scripts/markgraf/build-js-engine.sh [OUT_DIR]
#
# Every JavaScript baseline runs this one file: the Tauri native host embeds it
# (build-js-cli.sh), and js-host/host.js runs it under Deno and Bun.
#
# Environment: MARKGRAF (checkout; pinned.sh).

set -euo pipefail

source "$(dirname "${BASH_SOURCE[0]}")/pinned.sh"
OUT="${1:-${TMPDIR:-/tmp}/markgraf-js-cli}"
CLI="$MARKGRAF/cli"
NPM="$MARKGRAF/npm"
export PATH="$NPM/node_modules/.bin:$PATH"

mkdir -p "$OUT/dist"
rm -rf "$OUT/corefn" "$OUT/optimized"

(cd "$CLI" && spago fetch >/dev/null 2>&1)
sources=()
while IFS= read -r source; do sources+=("$CLI/$source"); done < <(
  cd "$CLI" && spago sources --json 2>/dev/null | bun -e '
    const sources = JSON.parse(await Bun.stdin.text());
    for (const source of sources) if (!source.startsWith("test/")) console.log(source);'
)
purs compile "${sources[@]}" --codegen js,corefn --output "$OUT/corefn" >"$OUT/purs.log" 2>&1 \
  || { cat "$OUT/purs.log" >&2; exit 1; }
(cd "$NPM" && purs-backend-es build --corefn-dir "$OUT/corefn" --output-dir "$OUT/optimized" >"$OUT/es.log" 2>&1) \
  || { cat "$OUT/es.log" >&2; exit 1; }

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
(cd "$NPM" && vite build --config "$OUT/vite.config.js" >"$OUT/vite.log" 2>&1) || { cat "$OUT/vite.log" >&2; exit 1; }
echo "$OUT/dist/engine.js"
