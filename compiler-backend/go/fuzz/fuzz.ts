// Differential fuzzing of the Go backend against Iris's JavaScript backend.
//
//   bun fuzz.ts gen --seed N [--features LIST] [--statements S] [--depth D]
//   bun fuzz.ts run --seed-from N --count K [--features LIST] [--jobs J] [--batch B]
//                   [--work DIR] [--results DIR] [--statements S] [--depth D] [--keep-ok]
//   bun fuzz.ts minimise RESULT_DIR... [--work DIR]
//
// Features: a comma list of names, each optionally weighted (`prims=2`), or signed (`+surrogates`,
// `-aff`) to adjust the defaults; a list of bare names enables only those.

import { appendFileSync, existsSync, mkdirSync, readFileSync, writeFileSync } from "node:fs";
import { join } from "node:path";
import { printProgram } from "./ast.ts";
import { FEATURES, GeneratorOptions, generateProgram, parseFeatures } from "./generate.ts";
import {
  Classification,
  FAILURE_CLASSES,
  FUZZ_DIRECTORY,
  ProgramInput,
  ProgramResult,
  Worker,
  defaultToolchain,
  ensureTemplate,
  saveResult,
} from "./pipeline.ts";
import { minimise } from "./minimise.ts";

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

export const programFor = (seed: number, options: GeneratorOptions): ProgramInput => {
  const program = generateProgram(seed, moduleNameFor(seed), options);
  return { seed, moduleName: program.moduleName, source: printProgram(program) };
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

  const report = (program: ProgramInput, result: ProgramResult) => {
    counts.set(result.classification, (counts.get(result.classification) ?? 0) + 1);
    const failing = FAILURE_CLASSES.includes(result.classification);
    const directory = failing || keepOk ? saveResult(results, program, result) : null;
    if (directory) writeFileSync(join(directory, "options.json"), JSON.stringify(options, null, 2) + "\n");
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
    console.log(`minimising ${directory} (${result.classification})`);
    const minimal = await minimise(result.seed, campaign, result.classification, worker, (step) => console.log(`  ${step}`));
    const target = join(directory, "minimal.purs");
    writeFileSync(target, minimal.source);
    writeFileSync(join(directory, "minimal.json"), JSON.stringify({ classification: minimal.classification, detail: minimal.detail, signature: minimal.signature, lines: minimal.source.split("\n").length }, null, 2) + "\n");
    if (minimal.js) writeFileSync(join(directory, "minimal.js.out"), minimal.js.stdout + (minimal.js.stderr ? `\n[stderr]\n${minimal.js.stderr}` : ""));
    if (minimal.go) writeFileSync(join(directory, "minimal.go.out"), minimal.go.stdout + (minimal.go.stderr ? `\n[stderr]\n${minimal.go.stderr}` : ""));
    console.log(`  -> ${target} (${minimal.source.split("\n").length} lines): ${minimal.classification} ${minimal.detail}`);
  }
};

/** The generator options a result's campaign used, recorded in the results directory's summary. */
const readCampaignOptions = (directory: string): GeneratorOptions => {
  const optionsPath = join(directory, "options.json");
  if (existsSync(optionsPath)) return JSON.parse(readFileSync(optionsPath, "utf8")) as GeneratorOptions;
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
    case "features":
      console.log(FEATURES.join("\n"));
      break;
    default:
      console.error("usage: bun fuzz.ts gen|run|minimise|features ...");
      process.exit(2);
  }
};

void FUZZ_DIRECTORY;
await main();
