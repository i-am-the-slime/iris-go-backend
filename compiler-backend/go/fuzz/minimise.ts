// Shrinks a failing program while its classification persists: drops main statements and
// declarations, then replaces expressions by same-typed children or by the simplest value of
// their type, and shrinks literals. The program is reduced as a typed AST, so every candidate is
// well-typed by construction and the search spends its compiles on real reductions.

import { Alternative, Binding, Declaration, Equation, Expr, Pattern, Program, Statement, printProgram } from "./ast.ts";
import { Generator, GeneratorOptions, generateProgram } from "./generate.ts";
import { Classification, ProgramResult, RunResult, Worker } from "./pipeline.ts";
import * as T from "./types.ts";
import { Type, typeEquals } from "./types.ts";

export type MinimalResult = {
  source: string;
  classification: Classification;
  detail: string;
  signature: string;
  js: RunResult | null;
  go: RunResult | null;
};

type Site = { get: () => Expr; set: (expr: Expr) => void };

const emptyEnvironment = { variables: [], assumed: new Map(), typeVars: [], refs: [], inEffect: false };

/** A stable name for a failure: its class plus its detail with values and generated names erased. */
export const signatureOf = (classification: Classification, detail: string): string => {
  const erased = detail
    .replace(/Fuzz\.P\d+/g, "Fuzz.P")
    .replace(/\b(fn|D|N|Class|describeClass|let|v|m|l|r|acc|x|b|arg|self|n|rec|ref|cur|val|item|local|res|st|count|deep|walk|ping|pong|fold|nest|rankN|get|bump|other|c|q|p|i|y|f)\d+\b/g, "$1")
    .replace(/line \d+/g, "line")
    .replace(/-?\d+(\.\d+)?(e[+-]?\d+)?/g, "N");
  return `${classification}: ${erased}`;
};

export const minimise = async (
  seed: number,
  options: GeneratorOptions,
  classification: Classification,
  worker: Worker,
  log: (step: string) => void,
): Promise<MinimalResult> => {
  const moduleName = `Fuzz.P${seed}`;
  const program = generateProgram(seed, moduleName, options);
  const generator = new Generator(0, options);
  let last: ProgramResult | null = null;
  let checks = 0;

  const persists = async (): Promise<boolean> => {
    checks++;
    const source = printProgram(program);
    const [result] = await worker.runBatch([{ seed, moduleName, source }]);
    if (result.classification !== classification) return false;
    last = result;
    return true;
  };

  const initial = await persists();
  if (!initial) {
    const [result] = await worker.runBatch([{ seed, moduleName, source: printProgram(program) }]);
    return { source: printProgram(program), classification: result.classification, detail: `does not reproduce ${classification}; got ${result.classification}: ${result.detail}`, signature: signatureOf(result.classification, result.detail), js: result.js, go: result.go };
  }

  // 1. Main statements, by halves and then one at a time.
  const shrinkList = async <Item>(items: Item[], label: string): Promise<Item[]> => {
    let current = items;
    let chunk = Math.max(1, Math.floor(current.length / 2));
    while (chunk >= 1 && current.length > 1) {
      let start = 0;
      let removedAny = false;
      while (start < current.length && current.length > 1) {
        const candidate = [...current.slice(0, start), ...current.slice(start + chunk)];
        if (candidate.length === 0) break;
        apply(candidate);
        if (await persists()) {
          current = candidate;
          removedAny = true;
          log(`${label}: ${items.length} -> ${current.length}`);
        } else {
          apply(current);
          start += chunk;
        }
      }
      if (!removedAny) chunk = Math.floor(chunk / 2);
    }
    apply(current);
    return current;
    function apply(candidate: Item[]) {
      items.splice(0, items.length, ...candidate);
    }
  };

  await shrinkList(program.main, "main statements");

  // 2. Declarations, individually, largest first.
  for (let index = program.declarations.length - 1; index >= 0; index--) {
    const removed = program.declarations[index];
    program.declarations.splice(index, 1);
    if (!(await persists())) program.declarations.splice(index, 0, removed);
    else log(`declaration ${describeDeclaration(removed)} removed`);
  }

  // 3. Expressions: replace a node by a same-typed child or by the simplest value of its type.
  let progress = true;
  let passes = 0;
  while (progress && passes < 12) {
    progress = false;
    passes++;
    const sites = collectSites(program).sort((a, b) => size(b.get()) - size(a.get()));
    for (const site of sites) {
      const original = site.get();
      if (size(original) <= 1 && original.kind !== "literal") continue;
      for (const candidate of candidatesFor(original, generator)) {
        site.set(candidate);
        if (await persists()) {
          progress = true;
          log(`expression ${describeExpr(original)} -> ${describeExpr(candidate)}`);
          break;
        }
        site.set(original);
      }
    }
    // Case alternatives, guards and equations that are not the last one.
    for (const shrink of structuralShrinks(program)) {
      shrink.apply();
      if (await persists()) {
        progress = true;
        log(shrink.label);
      } else {
        shrink.undo();
      }
    }
  }

  // 4. A final pass over declarations that the expression shrinking may have orphaned.
  for (let index = program.declarations.length - 1; index >= 0; index--) {
    const removed = program.declarations[index];
    program.declarations.splice(index, 1);
    if (!(await persists())) program.declarations.splice(index, 0, removed);
    else log(`declaration ${describeDeclaration(removed)} removed`);
  }

  const final = last!;
  log(`${checks} checks`);
  return {
    source: printProgram(program),
    classification: final.classification,
    detail: final.detail,
    signature: signatureOf(final.classification, final.detail),
    js: final.js,
    go: final.go,
  };
};

const describeDeclaration = (declaration: Declaration): string => {
  switch (declaration.kind) {
    case "data":
      return declaration.name;
    case "function":
      return declaration.binding.name;
    case "class":
      return `class ${declaration.name}`;
    case "instance":
      return `instance ${declaration.className} ${T.printType(declaration.head)}`;
  }
};

const describeExpr = (expr: Expr): string => {
  switch (expr.kind) {
    case "literal":
      return expr.text.slice(0, 20);
    case "variable":
      return expr.name;
    case "apply":
      return `${describeExpr(expr.fn)}(...)`;
    case "binary":
      return `(${expr.op})`;
    default:
      return expr.kind;
  }
};

export const size = (expr: Expr): number => {
  let total = 0;
  forEachChild(expr, (child) => {
    total += size(child);
  });
  return total + 1;
};

const forEachChild = (expr: Expr, visit: (child: Expr, set: (replacement: Expr) => void) => void): void => {
  switch (expr.kind) {
    case "literal":
    case "variable":
      return;
    case "apply":
      visit(expr.fn, (e) => (expr.fn = e));
      expr.args.forEach((arg, i) => visit(arg, (e) => (expr.args[i] = e)));
      return;
    case "binary":
      visit(expr.left, (e) => (expr.left = e));
      visit(expr.right, (e) => (expr.right = e));
      return;
    case "section":
      visit(expr.operand, (e) => (expr.operand = e));
      return;
    case "lambda":
      visit(expr.body, (e) => (expr.body = e));
      return;
    case "ifThenElse":
      visit(expr.cond, (e) => (expr.cond = e));
      visit(expr.thenBranch, (e) => (expr.thenBranch = e));
      visit(expr.elseBranch, (e) => (expr.elseBranch = e));
      return;
    case "case":
      expr.scrutinees.forEach((s, i) => visit(s, (e) => (expr.scrutinees[i] = e)));
      for (const alternative of expr.alternatives) forEachAlternativeExpr(alternative, visit);
      return;
    case "letIn":
      for (const binding of expr.bindings) forEachBindingExpr(binding, visit);
      visit(expr.body, (e) => (expr.body = e));
      return;
    case "record":
      expr.fields.forEach((field) => visit(field.value, (e) => (field.value = e)));
      return;
    case "access":
      visit(expr.record, (e) => (expr.record = e));
      return;
    case "update":
      visit(expr.record, (e) => (expr.record = e));
      expr.fields.forEach((field) => visit(field.value, (e) => (field.value = e)));
      return;
    case "array":
      expr.elements.forEach((element, i) => visit(element, (e) => (expr.elements[i] = e)));
      return;
    case "annotate":
      visit(expr.expr, (e) => (expr.expr = e));
      return;
    case "doBlock":
      for (const statement of expr.statements) forEachStatementExpr(statement, visit);
      visit(expr.result, (e) => (expr.result = e));
      return;
  }
};

const forEachAlternativeExpr = (alternative: Alternative, visit: (child: Expr, set: (replacement: Expr) => void) => void) => {
  for (const guard of alternative.guards) {
    visit(guard.cond, (e) => (guard.cond = e));
    visit(guard.body, (e) => (guard.body = e));
  }
  visit(alternative.body, (e) => (alternative.body = e));
};

const forEachEquationExpr = (equation: Equation, visit: (child: Expr, set: (replacement: Expr) => void) => void) => {
  for (const guard of equation.guards) {
    visit(guard.cond, (e) => (guard.cond = e));
    visit(guard.body, (e) => (guard.body = e));
  }
  visit(equation.body, (e) => (equation.body = e));
  for (const binding of equation.where) forEachBindingExpr(binding, visit);
};

const forEachBindingExpr = (binding: Binding, visit: (child: Expr, set: (replacement: Expr) => void) => void) => {
  for (const equation of binding.equations) forEachEquationExpr(equation, visit);
};

const forEachStatementExpr = (statement: Statement, visit: (child: Expr, set: (replacement: Expr) => void) => void) => {
  switch (statement.kind) {
    case "bind":
      visit(statement.expr, (e) => (statement.expr = e));
      return;
    case "discard":
      visit(statement.expr, (e) => (statement.expr = e));
      return;
    case "let":
      for (const binding of statement.bindings) forEachBindingExpr(binding, visit);
      return;
  }
};

/** Every expression position in the program, with a setter, outermost first. */
const collectSites = (program: Program): Site[] => {
  const sites: Site[] = [];
  const visit = (expr: Expr, set: (replacement: Expr) => void) => {
    let current = expr;
    sites.push({ get: () => current, set: (replacement) => { current = replacement; set(replacement); } });
    forEachChild(expr, visit);
  };
  for (const statement of program.main) forEachStatementExpr(statement, visit);
  for (const declaration of program.declarations) {
    if (declaration.kind === "function") forEachBindingExpr(declaration.binding, visit);
    if (declaration.kind === "instance") for (const method of declaration.methods) forEachBindingExpr(method, visit);
    if (declaration.kind === "data" && declaration.manualShow) for (const equation of declaration.manualShow) forEachEquationExpr(equation, visit);
  }
  return sites;
};

/** Smaller expressions of the same type to try in place of a node. */
const candidatesFor = (expr: Expr, generator: Generator): Expr[] => {
  const candidates: Expr[] = [];
  const type = expr.type;
  const children: Expr[] = [];
  forEachChild(expr, (child) => {
    children.push(child);
  });
  for (const child of children) {
    if (typeEquals(child.type, type) && !isDummyType(child.type)) candidates.push(child);
  }
  if (expr.kind === "literal") {
    for (const text of smallerLiterals(expr)) candidates.push({ kind: "literal", type, text });
  } else if (expr.kind === "array" && expr.elements.length > 0) {
    candidates.push({ ...expr, elements: expr.elements.slice(0, Math.floor(expr.elements.length / 2)) });
    candidates.push({ ...expr, elements: expr.elements.slice(1) });
  } else if (expr.kind === "ifThenElse") {
    // Branches were pushed as children above; the condition is a Boolean and rarely matches.
  } else if (expr.kind === "letIn") {
    candidates.push(expr.body);
  } else if (expr.kind === "annotate") {
    // Keep annotations: they pin otherwise ambiguous types.
  }
  if (!isDummyType(type) && type.tag !== "Var" && type.tag !== "Effect" && type.tag !== "Ref" && !(expr.kind === "literal" || (expr.kind === "variable" && !expr.name.includes(".")))) {
    const simplest = generator.defaultValue(type, emptyEnvironment);
    if (!containsUndefined(simplest)) candidates.push(simplest);
  }
  return candidates.filter((candidate) => size(candidate) < size(expr) || (expr.kind === "literal" && candidate.kind === "literal"));
};

const isDummyType = (type: Type): boolean => type.tag === "Unit";

const containsUndefined = (expr: Expr): boolean => {
  if (expr.kind === "literal" && expr.text === "undefined") return true;
  let found = false;
  forEachChild(expr, (child) => {
    if (containsUndefined(child)) found = true;
  });
  return found;
};

const smallerLiterals = (expr: Expr & { kind: "literal" }): string[] => {
  const text = expr.text;
  switch (expr.type.tag) {
    case "Int": {
      const value = Number(text);
      if (Number.isNaN(value)) return [];
      const smaller = new Set<string>();
      if (value !== 0) smaller.add("0");
      if (value !== 1 && value !== 0) smaller.add("1");
      if (Math.abs(value) > 10) smaller.add(String(Math.trunc(value / 10)));
      if (value < 0) smaller.add(String(-value));
      smaller.delete(text);
      return [...smaller];
    }
    case "Number": {
      const smaller = new Set(["0.0", "1.0"]);
      smaller.delete(text);
      return [...smaller];
    }
    case "String": {
      const smaller = new Set<string>(['""', '"a"']);
      if (text.length > 4) smaller.add(`"${text.slice(1, Math.ceil(text.length / 2))}"`.replace(/\\$/, "").replace(/\\x[0-9A-Fa-f]*"$/, '"'));
      smaller.delete(text);
      return [...smaller].filter((candidate) => /^"([^"\\]|\\.)*"$/.test(candidate));
    }
    case "Char":
      return text === "'a'" ? [] : ["'a'"];
    case "Boolean":
      return text === "true" ? ["false"] : ["true"];
    default:
      return [];
  }
};

type StructuralShrink = { label: string; apply: () => void; undo: () => void };

/** Removals of case alternatives, guards and equations that keep the program exhaustive. */
const structuralShrinks = (program: Program): StructuralShrink[] => {
  const shrinks: StructuralShrink[] = [];
  const visitExpr = (expr: Expr) => {
    if (expr.kind === "case") {
      const alternatives = expr.alternatives;
      for (let i = 0; i < alternatives.length - 1; i++) {
        shrinks.push({
          label: `drop case alternative ${i}`,
          apply: () => void alternatives.splice(i, 1),
          undo: () => void alternatives.splice(i, 0, alternatives_[i]),
        });
      }
      const alternatives_ = [...alternatives];
      for (const alternative of alternatives) {
        if (alternative.guards.length > 0) {
          const guards = alternative.guards;
          const saved = [...guards];
          shrinks.push({ label: "drop guards", apply: () => void guards.splice(0, guards.length), undo: () => void guards.splice(0, 0, ...saved) });
        }
      }
    }
    forEachChild(expr, visitExpr);
  };
  for (const statement of program.main) forEachStatementExpr(statement, (e) => visitExpr(e));
  for (const declaration of program.declarations) {
    if (declaration.kind === "function") {
      const equations = declaration.binding.equations;
      const saved = [...equations];
      for (let i = 0; i < equations.length - 1; i++) {
        shrinks.push({ label: `drop equation ${i} of ${declaration.binding.name}`, apply: () => void equations.splice(i, 1), undo: () => void equations.splice(i, 0, saved[i]) });
      }
      for (const equation of equations) {
        if (equation.guards.length > 0) {
          const guards = equation.guards;
          const savedGuards = [...guards];
          shrinks.push({ label: `drop guards of ${declaration.binding.name}`, apply: () => void guards.splice(0, guards.length), undo: () => void guards.splice(0, 0, ...savedGuards) });
        }
        if (equation.where.length > 0) {
          const where = equation.where;
          const savedWhere = [...where];
          shrinks.push({ label: `drop where of ${declaration.binding.name}`, apply: () => void where.splice(0, where.length), undo: () => void where.splice(0, 0, ...savedWhere) });
        }
      }
      forEachBindingExpr(declaration.binding, (e) => visitExpr(e));
    }
  }
  return shrinks;
};

export type { Pattern };
