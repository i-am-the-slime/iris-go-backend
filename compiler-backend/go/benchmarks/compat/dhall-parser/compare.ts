// Parses Dhall sources with the JavaScript parser (nearley and the grammar compiled from
// dhall/grammar.ne, as Dhall/Parser.js does) and with its Go port (iris-go's ffi/Dhall_Parser_ffi), and
// compares every parse, as JSON, in order. The Go side goes through ParseImpl, so the values it
// prints are the Foreign values the compiled PureScript receives.
//
//   GO_SUPPORT=/path/to/iris-go bun dhall-parser/compare.ts
//
// Exits non-zero when any source parses differently.

import { createRequire } from "node:module";
import { mkdirSync, mkdtempSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { dirname, join } from "node:path";
import { cases } from "./cases.ts";

const compat = join(dirname(new URL(import.meta.url).pathname), "..");
const goSupport = process.env.GO_SUPPORT ?? "/Users/mark/Developer/iris-go";
const require = createRequire(join(compat, "package.json"));
const nearley = require("nearley");
const work = mkdtempSync(join(tmpdir(), "dhall-parser-compare-"));

const grammar = require(compileGrammar());

function main() {
  const javascript = cases.map((source) => JSON.stringify(parseInJavaScript(source)));
  const go = parseInGo(cases);

  let mismatches = 0;
  cases.forEach((source, index) => {
    const goJson = JSON.stringify(JSON.parse(go[index]));
    if (goJson !== javascript[index]) {
      mismatches++;
      console.log(`MISMATCH ${JSON.stringify(source)}\n  js: ${javascript[index].slice(0, 400)}\n  go: ${goJson.slice(0, 400)}`);
    }
  });
  const parses = javascript.map((json) => JSON.parse(json)?.length ?? "null");
  console.log(`${cases.length - mismatches}/${cases.length} sources parse identically (parse counts: ${parses.join(" ")})`);
  process.exit(mismatches === 0 ? 0 : 1);
}

function compileGrammar(): string {
  const target = join(work, "grammar.cjs");
  const compiling = Bun.spawnSync(["bun", join(compat, "node_modules/.bin/nearleyc"), join(compat, "dhall/grammar.ne"), "-o", target]);
  if (compiling.exitCode !== 0) throw new Error(compiling.stderr.toString());
  return target;
}

// Dhall/Parser.js's parseImpl.
function parseInJavaScript(source: string): unknown {
  const parser = new nearley.Parser(nearley.Grammar.fromCompiled(grammar));
  try {
    parser.feed(source);
    return parser.results;
  } catch {
    return null;
  }
}

function parseInGo(sources: string[]): string[] {
  const module = join(work, "go");
  mkdirSync(module, { recursive: true });
  writeFileSync(
    join(module, "go.mod"),
    `module compat.example/program\n\ngo 1.27.0\n\nrequire github.com/i-am-the-slime/iris-go v0.0.0\n\nreplace github.com/i-am-the-slime/iris-go => ${goSupport}\n`,
  );
  writeFileSync(join(module, "main.go"), printer);
  writeFileSync(join(work, "sources.json"), JSON.stringify(sources));
  const running = Bun.spawnSync(["go", "run", ".", join(work, "sources.json")], { cwd: module });
  if (running.exitCode !== 0) throw new Error(running.stderr.toString());
  return running.stdout.toString().trimEnd().split("\n");
}

// Prints ParseImpl's result for each source as one line of JSON.
const printer = `package main

import (
	"encoding/json"
	"fmt"
	"math"
	"os"
	"strconv"
	"strings"

	parser "github.com/i-am-the-slime/iris-go/ffi/Dhall_Parser_ffi"
	"github.com/i-am-the-slime/iris-go/object"
)

func main() {
	text, err := os.ReadFile(os.Args[1])
	if err != nil {
		panic(err)
	}
	var sources []string
	if err := json.Unmarshal(text, &sources); err != nil {
		panic(err)
	}
	for _, source := range sources {
		results := parser.ParseImpl(source)
		if results == nil {
			fmt.Println("null")
			continue
		}
		fmt.Println(toJSON(*results))
	}
}

func toJSON(value any) string {
	switch value := value.(type) {
	case nil:
		return "null"
	case *any:
		if value == nil {
			return "null"
		}
		return toJSON(*value)
	case string:
		quoted, _ := json.Marshal(value)
		return string(quoted)
	case int32:
		return strconv.Itoa(int(value))
	case float64:
		if math.IsInf(value, 0) || math.IsNaN(value) {
			return "null"
		}
		return strconv.FormatFloat(value, 'g', -1, 64)
	case []any:
		elements := make([]string, len(value))
		for i, element := range value {
			elements[i] = toJSON(element)
		}
		return "[" + strings.Join(elements, ",") + "]"
	case *struct {
		Index map[string]int
		Ints  int
		Keys  []string
		Vals  []any
	}:
		var fields []string
		for _, key := range object.Keys(value) {
			quoted, _ := json.Marshal(key)
			fields = append(fields, string(quoted)+":"+toJSON(object.UnsafeIndex(value, key)))
		}
		return "{" + strings.Join(fields, ",") + "}"
	}
	panic(fmt.Sprintf("not a Foreign value: %T", value))
}
`;

main();
