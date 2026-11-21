// Compares the Go and JS outputs of the FFI fuzz programs case by case and prints the
// divergences grouped by function, smallest input first.
//
//   bun compare.ts <work-dir> <module>...

import { existsSync, readFileSync } from "node:fs";
import { join } from "node:path";

const [work, ...modules] = process.argv.slice(2);
const { seed, cases } = JSON.parse(readFileSync(join(work, "cases.json"), "utf8")) as {
  seed: number;
  cases: { label: string; fn: string; inputs: string[]; lone: boolean }[];
};
const byLabel = new Map(cases.map((c) => [c.label, c]));
const examplesPerFunction = Number(process.env.FUZZ_EXAMPLES ?? 3);

const read = (path: string) => (existsSync(path) ? readFileSync(path, "utf8") : "");
const lines = (text: string) =>
  new Map(
    text
      .split("\n")
      .filter((line) => line.includes("\t"))
      .map((line) => [line.slice(0, line.indexOf("\t")), line.slice(line.indexOf("\t") + 1)] as const),
  );

// An unpaired `\uD800`..`\uDFFF` escape in a rendered result.
const loneEscape = (text: string) => {
  const units = [...text.matchAll(/\\u([0-9a-f]{4})/g)].map((m) => [m.index!, parseInt(m[1], 16)] as const);
  for (let k = 0; k < units.length; k++) {
    const [at, unit] = units[k];
    if (unit >= 0xd800 && unit <= 0xdbff) {
      const next = units[k + 1];
      if (next && next[0] === at + 6 && next[1] >= 0xdc00 && next[1] <= 0xdfff) { k++; continue; }
      return true;
    }
    if (unit >= 0xdc00 && unit <= 0xdfff) return true;
  }
  return false;
};

type Divergence = { label: string; inputs: string[]; js: string; go: string; deno?: string };
const real = new Map<string, Divergence[]>();
const surrogate = new Map<string, Divergence[]>();
const notAnInt = new Map<string, Divergence[]>();
const proto = new Map<string, Divergence[]>();
const engines = new Map<string, Divergence[]>();
const documented = new Map<string, Divergence[]>();

// Differences documentation/go-output.md lists: Foreign.Object keeps insertion order where JS
// enumerates integer-like keys first, and String.replace inserts its Replacement literally where
// JS expands `$$`, `$&`, `` $` `` and `$'`.
const integerLikeKey = /"(0|[1-9][0-9]{0,9})\\?"/;
const documentedDifference = (fn: string, inputs: string[]) =>
  (/^(Object\.|JSON\.(write|read)Object)/.test(fn) && inputs.some((input) => integerLikeKey.test(input))) ||
  (/^Common\.replace(All)?$/.test(fn) && inputs[1].includes("$"));

// A rendered Int result that no int32 can produce: JS arithmetic escaped the Int range.
const notInt32 = (fn: string, text: string) =>
  /^(Int|Bits)\./.test(fn) && /^-?[0-9.e+]+$|^NaN$|Infinity/.test(text) &&
  !(Number.isInteger(Number(text)) && (Number(text) | 0) === Number(text));
const programProblems: string[] = [];
let compared = 0, agreed = 0;

for (const module of modules) {
  const result = join(work, "results", module);
  const stage = read(join(work, "go", module, "stage")).trim();
  const js = lines(read(`${result}.js.out`));
  const go = lines(read(`${result}.go.out`));
  const deno = existsSync(`${result}.deno.out`) ? lines(read(`${result}.deno.out`)) : undefined;
  if (read(`${result}.js.status`).trim() !== "0") {
    programProblems.push(`${module}: JS FAILS ${read(`${result}.js.err`).slice(0, 300).replace(/\n/g, " ")}`);
  }
  if (stage === "iris") {
    const log = read(join(work, "go", module, "compile.log")).split("\n").filter((l) => l && !l.startsWith("go:"));
    programProblems.push(`${module}: IRIS ERROR ${log.slice(0, 6).join(" | ").slice(0, 400)}`);
    continue;
  }
  if (stage === "go-build") {
    const log = read(join(work, "go", module, "build.log")).split("\n").filter((l) => l && !l.startsWith("#"));
    programProblems.push(`${module}: GO BUILD ERROR ${log.slice(0, 3).join(" | ").slice(0, 400)}`);
    continue;
  }
  const goStatus = read(`${result}.go.status`).trim();
  if (goStatus !== "0") {
    const err = read(`${result}.go.err`).split("\n");
    const panic = err.findIndex((l) => /^panic: |^fatal error: /.test(l));
    const last = [...go.keys()].pop();
    programProblems.push(
      `${module}: GO EXIT ${goStatus} after ${last ?? "no case"}: ${(panic >= 0 ? err.slice(panic, panic + 2) : err.slice(0, 2)).join(" ").slice(0, 300)}`,
    );
  }
  for (const [label, jsResult] of js) {
    compared++;
    const goResult = go.get(label);
    if (goResult === jsResult) { agreed++; continue; }
    const info = byLabel.get(label)!;
    if (goResult === undefined) continue; // reported as a program problem above
    const denoResult = deno?.get(label);
    const divergence = { label, inputs: info.inputs, js: jsResult, go: goResult, deno: denoResult };
    const bucket =
      info.lone || loneEscape(jsResult.replaceAll("\\u005c", "\\").replace(/\\+u/g, "\\u")) ? surrogate
      : documentedDifference(info.fn, info.inputs) ? documented
      : denoResult !== undefined && denoResult !== jsResult ? engines
      : notInt32(info.fn, jsResult) ? notAnInt
      : info.inputs.some((input) => input.includes("__proto__")) ? proto
      : real;
    bucket.set(info.fn, [...(bucket.get(info.fn) ?? []), divergence]);
  }
}

const size = (d: Divergence) => d.inputs.join(" ").length;
const report = (title: string, groups: Map<string, Divergence[]>) => {
  console.log(`\n## ${title}: ${[...groups.values()].reduce((n, ds) => n + ds.length, 0)} cases in ${groups.size} functions`);
  for (const [fn, divergences] of [...groups].sort((a, b) => a[0].localeCompare(b[0]))) {
    const total = cases.filter((c) => c.fn === fn).length;
    console.log(`\n### ${fn}: ${divergences.length}/${total} cases diverge`);
    for (const d of [...divergences].sort((a, b) => size(a) - size(b)).slice(0, examplesPerFunction)) {
      console.log(`  ${d.label}  input: ${d.inputs.join("  ")}`);
      console.log(`    js: ${d.js.slice(0, 300)}`);
      if (d.deno !== undefined && d.deno !== d.js) console.log(`    deno: ${d.deno.slice(0, 300)}`);
      console.log(`    go: ${d.go.slice(0, 300)}`);
    }
  }
};

console.log(`# FFI fuzz, seed ${seed}: ${compared} cases compared in ${modules.length} programs, ${agreed} agree`);
if (programProblems.length) {
  console.log(`\n## program problems: ${programProblems.length}`);
  for (const p of programProblems) console.log(`  ${p}`);
}
report("divergences", real);
report("documented differences (documentation/go-output.md)", documented);
report("Bun and Deno disagree (no single JS answer)", engines);
report("JS result is not an Int (JS arithmetic left the int32 range)", notAnInt);
report("__proto__ keys (a JS object literal makes them its prototype)", proto);
report("lone-surrogate divergences (an input or the JS result holds a lone surrogate)", surrogate);
process.exit(real.size > 0 || programProblems.length > 0 ? 1 : 0);
