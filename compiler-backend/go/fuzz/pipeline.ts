// Compiles generated modules with Iris to JavaScript and to Go, runs both, and classifies each
// program by how the two disagree. A worker owns one Spago project directory and reuses it across
// batches, so that the dependencies compile once.

import { cpSync, existsSync, mkdirSync, readdirSync, rmSync, writeFileSync, readFileSync } from "node:fs";
import { join, dirname } from "node:path";

export const FUZZ_DIRECTORY = dirname(new URL(import.meta.url).pathname);

export type Classification =
  | "OK"
  | "OUTPUT MISMATCH"
  | "EXIT MISMATCH"
  | "IRIS ERROR"
  | "IRIS JS ERROR"
  | "GO BUILD ERROR"
  | "GO PANIC"
  | "TIMEOUT JS"
  | "TIMEOUT GO"
  | "TIMEOUT BOTH"
  | "JS STACK OVERFLOW"
  | "GENERATOR ILL-TYPED";

export const FAILURE_CLASSES: Classification[] = [
  "OUTPUT MISMATCH",
  "EXIT MISMATCH",
  "IRIS ERROR",
  "IRIS JS ERROR",
  "GO BUILD ERROR",
  "GO PANIC",
  "TIMEOUT JS",
  "TIMEOUT GO",
  "GENERATOR ILL-TYPED",
];

export type RunResult = { stdout: string; stderr: string; status: number; timedOut: boolean; millis: number };

export type ProgramInput = { seed: number; moduleName: string; source: string };

export type ProgramResult = {
  seed: number;
  moduleName: string;
  classification: Classification;
  detail: string;
  js: RunResult | null;
  go: RunResult | null;
  irisLog: string;
  goBuildLog: string;
  diagnostics: string;
  goDirectory: string | null;
  millis: { build: number; irisGo: number; goBuild: number };
};

export type Toolchain = {
  iris: string;
  goSupport: string;
  timeouts: { build: number; irisGo: number; goBuild: number; run: number };
};

export const defaultToolchain = (): Toolchain => ({
  iris: process.env.IRIS ?? join(FUZZ_DIRECTORY, "..", "..", "..", "target", "release", "iris"),
  goSupport: process.env.GO_SUPPORT ?? "/Users/mark/Developer/purs-backend-go/go-support",
  timeouts: { build: 300_000, irisGo: 120_000, goBuild: 300_000, run: Number(process.env.FUZZ_RUN_TIMEOUT ?? 30_000) },
});

const OUTPUT_LIMIT = 4_000_000;

export const run = async (
  command: string[],
  options: { cwd: string; timeoutMs: number; env?: Record<string, string> },
): Promise<RunResult> => {
  const started = performance.now();
  const process_ = Bun.spawn(command, {
    cwd: options.cwd,
    env: { ...process.env, ...(options.env ?? {}) },
    stdout: "pipe",
    stderr: "pipe",
    stdin: "ignore",
  });
  let timedOut = false;
  const timer = setTimeout(() => {
    timedOut = true;
    process_.kill("SIGKILL");
  }, options.timeoutMs);
  const [stdout, stderr] = await Promise.all([
    new Response(process_.stdout).text(),
    new Response(process_.stderr).text(),
  ]);
  const status = await process_.exited;
  clearTimeout(timer);
  return {
    stdout: stdout.length > OUTPUT_LIMIT ? stdout.slice(0, OUTPUT_LIMIT) + "\n[truncated]\n" : stdout,
    stderr: stderr.length > OUTPUT_LIMIT ? stderr.slice(0, OUTPUT_LIMIT) + "\n[truncated]\n" : stderr,
    status: timedOut ? 137 : status,
    timedOut,
    millis: Math.round(performance.now() - started),
  };
};

const goModule = (goSupport: string) =>
  `module fuzz.example/program

go 1.27.0

require github.com/i-am-the-slime/purs-backend-go/go-support v0.0.0

replace github.com/i-am-the-slime/purs-backend-go/go-support => ${goSupport}
`;

const GO_ENVIRONMENT = { GOEXPERIMENT: process.env.GOEXPERIMENT ?? "simd", GOFLAGS: "-mod=mod" };

/** The project every worker copies: spago.yaml from this directory plus the lockfile Iris writes. */
export const ensureTemplate = async (workDirectory: string, toolchain: Toolchain): Promise<string> => {
  const template = join(workDirectory, "template");
  if (existsSync(join(template, "spago.lock")) && existsSync(join(template, "output"))) return template;
  rmSync(template, { recursive: true, force: true });
  mkdirSync(join(template, "src", "Fuzz"), { recursive: true });
  cpSync(join(FUZZ_DIRECTORY, "spago.yaml"), join(template, "spago.yaml"));
  writeFileSync(
    join(template, "src", "Fuzz", "Template.purs"),
    "module Fuzz.Template where\n\nimport Prelude\nimport Effect (Effect)\nimport Effect.Console (log)\n\nmain :: Effect Unit\nmain = log \"template\"\n",
  );
  const result = await run([toolchain.iris, "build", "--output", "output"], { cwd: template, timeoutMs: 600_000 });
  if (result.status !== 0) {
    throw new Error(`template project does not build:\n${result.stdout}\n${result.stderr}`);
  }
  return template;
};

const moduleFile = (moduleName: string) => `src/Fuzz/${moduleName.replace(/^Fuzz\./, "")}.purs`;

const DIAGNOSTIC_PATTERN = /^(Error|Warning)! · \[(\w+)\] · (\S+?):(\d+):(\d+)/gm;

/** The generated modules an `iris build` failure names, by their source path. */
const failingModules = (buildOutput: string): Set<string> => {
  const failing = new Set<string>();
  for (const match of buildOutput.matchAll(DIAGNOSTIC_PATTERN)) {
    const [, severity, , path] = match;
    const moduleMatch = /src\/Fuzz\/(\w+)\.purs$/.exec(path);
    if (severity === "Error" && moduleMatch) failing.add(`Fuzz.${moduleMatch[1]}`);
  }
  return failing;
};

const diagnosticsFor = (buildOutput: string, moduleName: string): string => {
  const short = moduleName.replace(/^Fuzz\./, "");
  const blocks = buildOutput.split(/\n(?=(?:Error|Warning)! · )/);
  return blocks.filter((block) => block.includes(`src/Fuzz/${short}.purs`)).join("\n");
};

const firstLine = (text: string, filter: (line: string) => boolean = () => true): string =>
  text.split("\n").find((line) => line.trim() !== "" && filter(line))?.slice(0, 300) ?? "";

export class Worker {
  readonly directory: string;
  private readonly toolchain: Toolchain;
  private prepared = false;

  constructor(directory: string, toolchain: Toolchain) {
    this.directory = directory;
    this.toolchain = toolchain;
  }

  async prepare(template: string): Promise<void> {
    if (this.prepared) return;
    if (!existsSync(join(this.directory, "spago.lock"))) {
      mkdirSync(this.directory, { recursive: true });
      cpSync(join(template, "spago.yaml"), join(this.directory, "spago.yaml"));
      cpSync(join(template, "spago.lock"), join(this.directory, "spago.lock"));
      cpSync(join(template, "output"), join(this.directory, "output"), { recursive: true });
      cpSync(join(template, ".spago"), join(this.directory, ".spago"), { recursive: true });
    }
    mkdirSync(join(this.directory, "src", "Fuzz"), { recursive: true });
    this.prepared = true;
  }

  private clearSources(): void {
    const sources = join(this.directory, "src", "Fuzz");
    for (const entry of readdirSync(sources)) rmSync(join(sources, entry), { force: true });
    const output = join(this.directory, "output");
    if (existsSync(output)) {
      for (const entry of readdirSync(output)) {
        if (entry.startsWith("Fuzz.")) rmSync(join(output, entry), { recursive: true, force: true });
      }
    }
    rmSync(join(this.directory, "go"), { recursive: true, force: true });
  }

  /** Builds the batch's JavaScript, dropping modules that do not typecheck until the rest builds. */
  private async buildJavaScript(
    programs: ProgramInput[],
  ): Promise<{ built: ProgramInput[]; failed: ProgramResult[]; buildMillis: number; log: string }> {
    let remaining = [...programs];
    const failed: ProgramResult[] = [];
    let buildMillis = 0;
    let log = "";
    for (let attempt = 0; attempt < programs.length + 1 && remaining.length > 0; attempt++) {
      const result = await run([this.toolchain.iris, "build", "--output", "output", "--quiet"], {
        cwd: this.directory,
        timeoutMs: this.toolchain.timeouts.build,
      });
      buildMillis += result.millis;
      log = result.stdout + result.stderr;
      if (result.status === 0) return { built: remaining, failed, buildMillis, log };
      const failing = failingModules(log);
      const named = remaining.filter((program) => failing.has(program.moduleName));
      if (named.length === 0) {
        const detail = result.timedOut ? "iris build timed out" : firstLine(log, (line) => /error|panic|Error/i.test(line));
        for (const program of remaining) {
          failed.push(this.emptyResult(program, "IRIS JS ERROR", detail, log));
        }
        return { built: [], failed, buildMillis, log };
      }
      for (const program of named) {
        const diagnostics = diagnosticsFor(log, program.moduleName);
        const codes = [...diagnostics.matchAll(/Error! · \[(\w+)\]/g)].map((match) => match[1]);
        failed.push(
          this.emptyResult(program, "GENERATOR ILL-TYPED", `${codes.slice(0, 3).join(",")}: ${firstLine(diagnostics.replace(/^.*\n/, ""), (line) => /•\s+\S/.test(line)).replace(/^\s*•\s*/, "")}`, diagnostics),
        );
        rmSync(join(this.directory, moduleFile(program.moduleName)), { force: true });
      }
      remaining = remaining.filter((program) => !failing.has(program.moduleName));
    }
    return { built: remaining, failed, buildMillis, log };
  }

  private emptyResult(program: ProgramInput, classification: Classification, detail: string, diagnostics: string): ProgramResult {
    return {
      seed: program.seed,
      moduleName: program.moduleName,
      classification,
      detail,
      js: null,
      go: null,
      irisLog: "",
      goBuildLog: "",
      diagnostics,
      goDirectory: null,
      millis: { build: 0, irisGo: 0, goBuild: 0 },
    };
  }

  async runBatch(programs: ProgramInput[]): Promise<ProgramResult[]> {
    this.clearSources();
    for (const program of programs) {
      writeFileSync(join(this.directory, moduleFile(program.moduleName)), program.source);
    }
    const { built, failed, buildMillis } = await this.buildJavaScript(programs);
    const results: ProgramResult[] = [...failed];
    for (const program of built) {
      results.push(await this.runProgram(program, Math.round(buildMillis / Math.max(1, built.length))));
    }
    return results;
  }

  private async runProgram(program: ProgramInput, buildMillis: number): Promise<ProgramResult> {
    const indexPath = join(this.directory, "output", program.moduleName, "index.js");
    const js = await run(["bun", "-e", `import(${JSON.stringify(indexPath)}).then((module) => module.main())`], {
      cwd: this.directory,
      timeoutMs: this.toolchain.timeouts.run,
    });
    const goDirectory = join(this.directory, "go", program.moduleName);
    mkdirSync(goDirectory, { recursive: true });
    writeFileSync(join(goDirectory, "go.mod"), goModule(this.toolchain.goSupport));
    const irisGo = await run([this.toolchain.iris, "go", "--entry", `${program.moduleName}.main`, goDirectory], {
      cwd: this.directory,
      timeoutMs: this.toolchain.timeouts.irisGo,
    });
    const base = {
      seed: program.seed,
      moduleName: program.moduleName,
      js,
      irisLog: irisGo.stdout + irisGo.stderr,
      diagnostics: "",
      goDirectory,
    };
    if (irisGo.status !== 0) {
      const detail = irisGo.timedOut
        ? "iris go timed out"
        : firstLine(base.irisLog, (line) => !line.startsWith("go:") && /error|panic|cannot|unsupported|not |failed/i.test(line)) || firstLine(base.irisLog, (line) => !line.startsWith("go:"));
      return { ...base, classification: "IRIS ERROR", detail, go: null, goBuildLog: "", millis: { build: buildMillis, irisGo: irisGo.millis, goBuild: 0 } };
    }
    const goBuild = await run(["go", "build", "-o", "program", "."], {
      cwd: goDirectory,
      timeoutMs: this.toolchain.timeouts.goBuild,
      env: GO_ENVIRONMENT,
    });
    const goBuildLog = goBuild.stdout + goBuild.stderr;
    if (goBuild.status !== 0) {
      const detail = goBuild.timedOut ? "go build timed out" : firstLine(goBuildLog, (line) => !line.startsWith("#") && !line.startsWith("go:"));
      return { ...base, classification: "GO BUILD ERROR", detail, go: null, goBuildLog, millis: { build: buildMillis, irisGo: irisGo.millis, goBuild: goBuild.millis } };
    }
    const go = await run([join(goDirectory, "program")], { cwd: goDirectory, timeoutMs: this.toolchain.timeouts.run });
    rmSync(join(goDirectory, "program"), { force: true });
    const { classification, detail } = classify(js, go);
    return { ...base, classification, detail, go, goBuildLog, millis: { build: buildMillis, irisGo: irisGo.millis, goBuild: goBuild.millis } };
  }
}

const JS_STACK_OVERFLOW = /Maximum call stack size exceeded|RangeError: Out of memory|stack overflow/i;

export const classify = (js: RunResult, go: RunResult): { classification: Classification; detail: string } => {
  if (js.timedOut && go.timedOut) return { classification: "TIMEOUT BOTH", detail: "both sides ran out of time" };
  if (js.timedOut) return { classification: "TIMEOUT JS", detail: `JS ran out of time; Go exit ${go.status} after ${lineCount(go.stdout)} lines` };
  if (go.timedOut) return { classification: "TIMEOUT GO", detail: `Go ran out of time after ${lineCount(go.stdout)} of ${lineCount(js.stdout)} lines` };
  const panic = go.stderr.split("\n").find((line) => /^panic: |^fatal error: /.test(line));
  if (panic && js.status === 0) {
    return {
      classification: "GO PANIC",
      detail: `${panic.slice(0, 200)} (after ${lineCount(go.stdout)} of ${lineCount(js.stdout)} lines)`,
    };
  }
  if (js.status !== 0 && JS_STACK_OVERFLOW.test(js.stderr) && go.status === 0) {
    return { classification: "JS STACK OVERFLOW", detail: `JS overflowed its stack after ${lineCount(js.stdout)} lines; Go finished ${lineCount(go.stdout)}` };
  }
  if (js.stdout !== go.stdout) {
    const jsLines = js.stdout.split("\n");
    const goLines = go.stdout.split("\n");
    let index = 0;
    while (index < jsLines.length && index < goLines.length && jsLines[index] === goLines[index]) index++;
    const detail = `line ${index + 1}: js ${JSON.stringify(jsLines[index] ?? "<end>").slice(0, 160)} go ${JSON.stringify(goLines[index] ?? "<end>").slice(0, 160)}`;
    return { classification: "OUTPUT MISMATCH", detail };
  }
  if (js.status !== go.status) {
    return {
      classification: "EXIT MISMATCH",
      detail: `js exit ${js.status} (${firstLine(js.stderr).slice(0, 100)}), go exit ${go.status} (${firstLine(go.stderr).slice(0, 100)})`,
    };
  }
  return { classification: "OK", detail: `${lineCount(js.stdout)} lines, exit ${js.status}` };
};

const lineCount = (text: string): number => (text === "" ? 0 : text.split("\n").length - (text.endsWith("\n") ? 1 : 0));

/** Keeps everything about a failing program under results/<class>/<module>/. */
export const saveResult = (resultsDirectory: string, program: ProgramInput, result: ProgramResult): string => {
  const slug = result.classification.toLowerCase().replace(/[^a-z]+/g, "-");
  const directory = join(resultsDirectory, slug, program.moduleName.replace(/^Fuzz\./, ""));
  rmSync(directory, { recursive: true, force: true });
  mkdirSync(directory, { recursive: true });
  writeFileSync(join(directory, `${program.moduleName.replace(/^Fuzz\./, "")}.purs`), program.source);
  if (result.js) {
    writeFileSync(join(directory, "js.out"), result.js.stdout);
    writeFileSync(join(directory, "js.err"), result.js.stderr);
    writeFileSync(join(directory, "js.status"), `${result.js.status}\n`);
  }
  if (result.go) {
    writeFileSync(join(directory, "go.out"), result.go.stdout);
    writeFileSync(join(directory, "go.err"), result.go.stderr);
    writeFileSync(join(directory, "go.status"), `${result.go.status}\n`);
  }
  if (result.irisLog) writeFileSync(join(directory, "iris.log"), result.irisLog);
  if (result.goBuildLog) writeFileSync(join(directory, "gobuild.log"), result.goBuildLog);
  if (result.diagnostics) writeFileSync(join(directory, "diagnostics.txt"), result.diagnostics);
  if (result.goDirectory && existsSync(result.goDirectory)) {
    cpSync(result.goDirectory, join(directory, "go"), { recursive: true, filter: (source) => !source.endsWith("/program") });
  }
  writeFileSync(
    join(directory, "result.json"),
    JSON.stringify({ seed: result.seed, moduleName: result.moduleName, classification: result.classification, detail: result.detail, millis: result.millis }, null, 2) + "\n",
  );
  return directory;
};

export const readSource = (path: string): string => readFileSync(path, "utf8");
