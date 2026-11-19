// Differential fuzzing of the Go backend against Iris's JavaScript backend.
//
//   bun fuzz.ts gen --seed N [--features LIST] [--statements S] [--depth D]
//   bun fuzz.ts run --seed-from N --count K [--features LIST] [--jobs J] [--batch B]
//                   [--work DIR] [--results DIR] [--statements S] [--depth D] [--keep-ok]
//   bun fuzz.ts minimise RESULT_DIR... [--work DIR]
//
// Features: a comma list of names, each optionally weighted (`prims=2`), or signed (`+surrogates`,
// `-aff`) to adjust the defaults; a list of bare names enables only those.

import { appendFileSync, cpSync, existsSync, mkdirSync, readFileSync, readdirSync, rmSync, statSync, writeFileSync } from "node:fs";
import { join } from "node:path";
import { Program, printProgram } from "./ast.ts";
import { FEATURES, GeneratorOptions, defaultWeights, generateProgram, parseFeatures } from "./generate.ts";
import { failureKey, minimise } from "./minimise.ts";
import {
  Classification,
  FAILURE_CLASSES,
  FUZZ_DIRECTORY,
  ProgramInput,
  ProgramResult,
  Worker,
  defaultToolchain,
  ensureTemplate,
  run,
  saveResult,
} from "./pipeline.ts";

type Arguments = { positional: string[]; flags: Map<string, string | true> };

const parseArguments = (argv: string[]): Arguments => {
  const positional: string[] = [];
  const flags = new Map<string, string | true>();
  for (let i = 0; i < argv.length; i++) {
    const argument = argv[i];
    if (argument.startsWith("--")) {
      const [name, inlineValue] = argument.slice(2).split("=", 2);
      if (inlineValue !== undefined) flags.set(name, inlineValue);
      else if (i + 1 < argv.length && !argv[i + 1].startsWith("--")) flags.set(name, argv[++i]);
      else flags.set(name, true);
    } else {
      positional.push(argument);
    }
  }
  return { positional, flags };
};

const flagNumber = (flags: Map<string, string | true>, name: string, fallback: number): number => {
  const value = flags.get(name);
  if (value === undefined || value === true) return fallback;
  const parsed = Number(value);
  if (Number.isNaN(parsed)) throw new Error(`--${name} needs a number, got ${value}`);
  return parsed;
};

const flagString = (flags: Map<string, string | true>, name: string, fallback: string): string => {
  const value = flags.get(name);
  return value === undefined || value === true ? fallback : value;
};

export const moduleNameFor = (seed: number): string => `Fuzz.P${seed}`;

export const generatorOptions = (flags: Map<string, string | true>): GeneratorOptions => ({
  weights: parseFeatures(flagString(flags, "features", "")),
  statements: flagNumber(flags, "statements", 8),
  depth: flagNumber(flags, "depth", 4),
});

export const programFor = (seed: number, options: GeneratorOptions): ProgramInput & { program: Program } => {
  const program = generateProgram(seed, moduleNameFor(seed), options);
  return { seed, moduleName: program.moduleName, source: printProgram(program), program };
};

const SCRATCHPAD = process.env.FUZZ_SCRATCHPAD ?? "/private/tmp/claude-501/-Users-mark-Developer/6b879e15-cbd5-43a2-bd86-225dca16f6f0/scratchpad";

const commandGenerate = (arguments_: Arguments): void => {
  const seed = flagNumber(arguments_.flags, "seed", 1);
  process.stdout.write(programFor(seed, generatorOptions(arguments_.flags)).source);
};

const commandRun = async (arguments_: Arguments): Promise<void> => {
  const { flags } = arguments_;
  const seedFrom = flagNumber(flags, "seed-from", 1);
  const count = flagNumber(flags, "count", 10);
  const jobs = flagNumber(flags, "jobs", 6);
  const batchSize = flagNumber(flags, "batch", 8);
  const work = flagString(flags, "work", join(SCRATCHPAD, "fuzz-work"));
  const results = flagString(flags, "results", join(SCRATCHPAD, "fuzz-results"));
  const keepOk = flags.has("keep-ok");
  const options = generatorOptions(flags);
  const toolchain = defaultToolchain();
  if (!existsSync(toolchain.iris)) throw new Error(`no iris binary at ${toolchain.iris}`);
  mkdirSync(results, { recursive: true });
  const template = await ensureTemplate(work, toolchain);
  const workers = Array.from({ length: jobs }, (_, index) => new Worker(join(work, `worker-${index}`), toolchain));
  await Promise.all(workers.map((worker) => worker.prepare(template)));

  const seeds = Array.from({ length: count }, (_, index) => seedFrom + index);
  const batches: number[][] = [];
  for (let start = 0; start < seeds.length; start += batchSize) batches.push(seeds.slice(start, start + batchSize));
  let nextBatch = 0;
  const counts = new Map<Classification, number>();
  const started = performance.now();
  const summaryPath = join(results, "summary.jsonl");
  const campaignLine = JSON.stringify({ started: new Date().toISOString(), seedFrom, count, features: options.weights, statements: options.statements, depth: options.depth });
  appendFileSync(summaryPath, `${campaignLine}\n`);

  const report = (program: ProgramInput & { program: Program }, result: ProgramResult) => {
    counts.set(result.classification, (counts.get(result.classification) ?? 0) + 1);
    const failing = FAILURE_CLASSES.includes(result.classification);
    const directory = failing || keepOk ? saveResult(results, program, result) : null;
    if (directory) {
      writeFileSync(join(directory, "options.json"), JSON.stringify(options, null, 2) + "\n");
      writeFileSync(join(directory, "program.json"), JSON.stringify(program.program) + "\n");
    }
    const row = `${program.moduleName.padEnd(14)} ${result.classification.padEnd(20)} ${result.detail}`;
    console.log(row);
    appendFileSync(summaryPath, `${JSON.stringify({ seed: result.seed, classification: result.classification, detail: result.detail, directory, millis: result.millis, js: result.js?.millis, go: result.go?.millis })}\n`);
  };

  const runWorker = async (worker: Worker) => {
    while (nextBatch < batches.length) {
      const batch = batches[nextBatch++];
      const programs = batch.map((seed) => programFor(seed, options));
      const batchResults = await worker.runBatch(programs);
      for (const result of batchResults) {
        const program = programs.find((p) => p.seed === result.seed)!;
        report(program, result);
      }
    }
  };
  await Promise.all(workers.map(runWorker));

  const elapsed = (performance.now() - started) / 1000;
  console.log(`\n${count} programs in ${elapsed.toFixed(1)}s (${(count / elapsed).toFixed(2)} programs/s, ${jobs} jobs)`);
  for (const [classification, number] of [...counts].sort((a, b) => b[1] - a[1])) {
    console.log(`  ${String(number).padStart(6)}  ${classification}`);
  }
  console.log(`failures kept under ${results}`);
};

const commandMinimise = async (arguments_: Arguments): Promise<void> => {
  const { flags, positional } = arguments_;
  const work = flagString(flags, "work", join(SCRATCHPAD, "fuzz-work"));
  const toolchain = defaultToolchain();
  const template = await ensureTemplate(work, toolchain);
  const worker = new Worker(join(work, "minimiser"), toolchain);
  await worker.prepare(template);
  for (const directory of positional) {
    const result = JSON.parse(readFileSync(join(directory, "result.json"), "utf8")) as { seed: number; classification: Classification; detail: string };
    const campaign = readCampaignOptions(directory);
    const programPath = join(directory, "program.json");
    const saved = existsSync(programPath) ? (JSON.parse(readFileSync(programPath, "utf8")) as Program) : null;
    console.log(`minimising ${directory} (${result.classification}${saved ? ", from program.json" : ", regenerated from seed"})`);
    const minimal = await minimise(result.seed, campaign, result.classification, worker, (step) => console.log(`  ${step}`), result.detail, saved);
    const target = join(directory, "minimal.purs");
    writeFileSync(target, minimal.source);
    writeFileSync(join(directory, "minimal.json"), JSON.stringify({ classification: minimal.classification, detail: minimal.detail, signature: minimal.signature, lines: minimal.source.split("\n").length }, null, 2) + "\n");
    if (minimal.js) writeFileSync(join(directory, "minimal.js.out"), minimal.js.stdout + (minimal.js.stderr ? `\n[stderr]\n${minimal.js.stderr}` : ""));
    if (minimal.go) writeFileSync(join(directory, "minimal.go.out"), minimal.go.stdout + (minimal.go.stderr ? `\n[stderr]\n${minimal.go.stderr}` : ""));
    console.log(`  -> ${target} (${minimal.source.split("\n").length} lines): ${minimal.classification} ${minimal.detail}`);
  }
};

/** Runs kept programs (minimal.purs where present) again, with the current compiler, and prints the classification. */
const commandRecheck = async (arguments_: Arguments): Promise<void> => {
  const { flags, positional } = arguments_;
  const work = flagString(flags, "work", join(SCRATCHPAD, "fuzz-work"));
  const toolchain = defaultToolchain();
  const template = await ensureTemplate(work, toolchain);
  const worker = new Worker(join(work, "recheck"), toolchain);
  await worker.prepare(template);
  const counts = new Map<string, number>();
  const again = flags.has("all");
  for (const directory of positional) {
    // A crash part-way through a long recheck must not cost the results already written.
    if (!again && existsSync(join(directory, "recheck.json"))) continue;
    const sources = readdirSync(directory).filter((name) => name.endsWith(".purs"));
    const source = sources.includes("minimal.purs") ? "minimal.purs" : sources[0];
    const text = readFileSync(join(directory, source), "utf8");
    const moduleName = /^module (\S+)/m.exec(text)?.[1] ?? "Fuzz.Unknown";
    const previous = JSON.parse(readFileSync(join(directory, "result.json"), "utf8")) as { classification: Classification };
    const [result] = await worker.runBatch([{ seed: 0, moduleName, source: text }]);
    const change = result.classification === previous.classification ? "same" : `was ${previous.classification}`;
    counts.set(result.classification, (counts.get(result.classification) ?? 0) + 1);
    console.log(`${directory.replace(/.*fuzz-results\//, "").padEnd(40)} ${result.classification.padEnd(20)} (${change}) ${result.detail.slice(0, 120)}`);
    writeFileSync(join(directory, "recheck.json"), JSON.stringify({ iris: toolchain.iris, classification: result.classification, detail: result.detail, source }, null, 2) + "\n");
  }
  console.log();
  for (const [classification, number] of [...counts].sort((a, b) => b[1] - a[1])) console.log(`  ${String(number).padStart(5)}  ${classification}`);
};

/**
 * Runs a kept program's minimal.purs (or its source) through purs's own JavaScript backend via
 * spago, a third opinion that says whether Iris's JavaScript or its Go disagrees with purs.
 */
const commandAttribute = async (arguments_: Arguments): Promise<void> => {
  const { flags, positional } = arguments_;
  const work = flagString(flags, "work", join(SCRATCHPAD, "fuzz-work"));
  const toolchain = defaultToolchain();
  const template = await ensureTemplate(work, toolchain);
  const project = join(work, "purs-oracle");
  if (!existsSync(join(project, "spago.lock"))) {
    mkdirSync(join(project, "src", "Fuzz"), { recursive: true });
    cpSync(join(template, "spago.yaml"), join(project, "spago.yaml"));
    cpSync(join(template, "spago.lock"), join(project, "spago.lock"));
  }
  for (const directory of positional) {
    const sources = readdirSync(directory).filter((name) => name.endsWith(".purs"));
    const source = sources.includes("minimal.purs") ? "minimal.purs" : sources[0];
    const text = readFileSync(join(directory, source), "utf8");
    const moduleName = /^module (\S+)/m.exec(text)?.[1] ?? "Fuzz.Unknown";
    for (const stale of readdirSync(join(project, "src", "Fuzz"))) rmSync(join(project, "src", "Fuzz", stale));
    writeFileSync(join(project, "src", "Fuzz", `${moduleName.replace(/^Fuzz\./, "")}.purs`), text);
    const build = await run(["spago", "build", "--quiet"], { cwd: project, timeoutMs: 600_000 });
    if (build.status !== 0) {
      console.log(`${directory}: purs build failed\n${(build.stdout + build.stderr).split("\n").filter((l) => /Error|error/.test(l)).slice(0, 5).join("\n")}`);
      continue;
    }
    const indexPath = join(project, "output", moduleName, "index.js");
    const purs = await run(["bun", "-e", `import(${JSON.stringify(indexPath)}).then((module) => module.main())`], { cwd: project, timeoutMs: toolchain.timeouts.run });
    const read = (name: string) => (existsSync(join(directory, name)) ? readFileSync(join(directory, name), "utf8") : null);
    const js = read("minimal.js.out")?.split("\n[stderr]\n")[0] ?? read("js.out");
    const go = read("minimal.go.out")?.split("\n[stderr]\n")[0] ?? read("go.out");
    const verdict = purs.stdout === js && purs.stdout === go ? "all three agree"
      : purs.stdout === js ? "purs agrees with Iris JS: Go-side"
      : purs.stdout === go ? "purs agrees with Iris Go: JS-side"
      : "purs disagrees with both";
    writeFileSync(join(directory, "purs.out"), purs.stdout + (purs.stderr ? `\n[stderr]\n${purs.stderr}` : ""));
    writeFileSync(join(directory, "attribution.txt"), `${verdict}\npurs exit ${purs.status}\n`);
    console.log(`${directory}: ${verdict} (purs exit ${purs.status})`);
  }
};

/** Groups every kept failure by signature, preferring the minimised form where one exists. */
const commandReport = (arguments_: Arguments): void => {
  const results = flagString(arguments_.flags, "results", join(SCRATCHPAD, "fuzz-results"));
  type Entry = { directory: string; seed: number; classification: Classification; detail: string; signature: string; minimised: boolean; lines: number | null };
  const entries: Entry[] = [];
  for (const classDirectory of readdirSync(results)) {
    const classPath = join(results, classDirectory);
    if (!statSync(classPath).isDirectory()) continue;
    for (const program of readdirSync(classPath)) {
      const directory = join(classPath, program);
      const resultPath = join(directory, "result.json");
      if (!existsSync(resultPath)) continue;
      let result = JSON.parse(readFileSync(resultPath, "utf8")) as { seed: number; classification: Classification; detail: string };
      // A recheck with a newer compiler supersedes the campaign's verdict.
      const recheckPath = join(directory, "recheck.json");
      if (existsSync(recheckPath)) {
        const recheck = JSON.parse(readFileSync(recheckPath, "utf8")) as { classification: Classification; detail: string };
        if (recheck.classification === "OK") continue;
        result = { ...result, classification: recheck.classification, detail: recheck.detail };
      }
      const minimalPath = join(directory, "minimal.json");
      if (existsSync(minimalPath)) {
        const minimal = JSON.parse(readFileSync(minimalPath, "utf8")) as { classification: Classification; detail: string; signature: string; lines: number };
        entries.push({ directory, seed: result.seed, classification: minimal.classification, detail: minimal.detail, signature: failureKey(minimal.classification, minimal.detail), minimised: true, lines: minimal.lines });
      } else {
        entries.push({ directory, seed: result.seed, classification: result.classification, detail: result.detail, signature: failureKey(result.classification, result.detail), minimised: false, lines: null });
      }
    }
  }
  const groups = new Map<string, Entry[]>();
  for (const entry of entries) groups.set(entry.signature, [...(groups.get(entry.signature) ?? []), entry]);
  const sorted = [...groups].sort((a, b) => b[1].length - a[1].length);
  const copyTo = flagString(arguments_.flags, "copy", "");
  if (copyTo) mkdirSync(copyTo, { recursive: true });
  console.log(`${entries.length} kept failures in ${groups.size} signatures\n`);
  let index = 0;
  for (const [signature, members] of sorted) {
    index++;
    const minimised = members.filter((m) => m.minimised).sort((a, b) => (a.lines ?? 1e9) - (b.lines ?? 1e9));
    const representative = minimised[0] ?? members[0];
    console.log(`## ${members.length}x ${signature.slice(0, 220)}`);
    console.log(`   detail: ${representative.detail.slice(0, 200)}`);
    console.log(`   seeds: ${members.map((m) => m.seed).slice(0, 12).join(", ")}${members.length > 12 ? ", ..." : ""}`);
    console.log(`   repro: ${representative.directory}${representative.minimised ? `/minimal.purs (${representative.lines} lines)` : ""}`);
    console.log();
    if (copyTo) {
      const sourceName = representative.minimised ? "minimal.purs" : readdirSync(representative.directory).find((name) => name.endsWith(".purs"))!;
      const slug = signature.toLowerCase().replace(/[^a-z0-9]+/g, "-").replace(/^-|-$/g, "").slice(0, 60);
      const target = join(copyTo, `${String(index).padStart(2, "0")}-${slug}.purs`);
      const header = [
        `-- ${representative.classification}: ${representative.detail}`,
        `-- ${members.length} program(s) with this signature; seeds ${members.map((m) => m.seed).slice(0, 8).join(", ")}`,
        `-- from ${representative.directory}${representative.minimised ? " (minimised)" : " (not minimised)"}`,
        "",
      ].join("\n");
      writeFileSync(target, header + readFileSync(join(representative.directory, sourceName), "utf8"));
    }
  }
};

/** The generator options a result's campaign used, recorded in the results directory's summary. */
const readCampaignOptions = (directory: string): GeneratorOptions => {
  const optionsPath = join(directory, "options.json");
  if (existsSync(optionsPath)) {
    const saved = JSON.parse(readFileSync(optionsPath, "utf8")) as GeneratorOptions;
    // Features added after a campaign ran were, in effect, enabled for it.
    return { ...saved, weights: { ...defaultWeights(), ...saved.weights } };
  }
  throw new Error(`${optionsPath} is missing; the result was not produced by fuzz.ts run`);
};

const main = async () => {
  const [command, ...rest] = process.argv.slice(2);
  const arguments_ = parseArguments(rest);
  switch (command) {
    case "gen":
      commandGenerate(arguments_);
      break;
    case "run":
      await commandRun(arguments_);
      break;
    case "minimise":
    case "minimize":
      await commandMinimise(arguments_);
      break;
    case "report":
      commandReport(arguments_);
      break;
    case "attribute":
      await commandAttribute(arguments_);
      break;
    case "recheck":
      await commandRecheck(arguments_);
      break;
    case "features":
      console.log(FEATURES.join("\n"));
      break;
    default:
      console.error("usage: bun fuzz.ts gen|run|minimise|report|features ...");
      process.exit(2);
  }
};

void FUZZ_DIRECTORY;
await main();
