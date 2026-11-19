// The abstract syntax of a generated program and its PureScript rendering. Every expression
// carries its type, so that the minimiser can replace any node by another of the same type.

import { PolyType, Type, printPolyType, printType } from "./types.ts";

export type Expr =
  | { kind: "literal"; type: Type; text: string }
  | { kind: "variable"; type: Type; name: string }
  | { kind: "apply"; type: Type; fn: Expr; args: Expr[] }
  | { kind: "binary"; type: Type; op: string; left: Expr; right: Expr }
  | { kind: "section"; type: Type; op: string; operand: Expr; side: "left" | "right" }
  | { kind: "lambda"; type: Type; params: Pattern[]; body: Expr }
  | { kind: "ifThenElse"; type: Type; cond: Expr; thenBranch: Expr; elseBranch: Expr }
  | { kind: "case"; type: Type; scrutinees: Expr[]; alternatives: Alternative[] }
  | { kind: "letIn"; type: Type; bindings: Binding[]; body: Expr }
  | { kind: "record"; type: Type; fields: { name: string; value: Expr }[] }
  | { kind: "access"; type: Type; record: Expr; field: string }
  | { kind: "update"; type: Type; record: Expr; fields: { name: string; value: Expr }[] }
  | { kind: "array"; type: Type; elements: Expr[] }
  | { kind: "annotate"; type: Type; expr: Expr }
  | { kind: "doBlock"; type: Type; statements: Statement[]; result: Expr };

export type Pattern =
  | { kind: "wildcard" }
  | { kind: "variable"; name: string; type: Type }
  | { kind: "literal"; text: string }
  | { kind: "constructor"; name: string; args: Pattern[] }
  | { kind: "array"; elements: Pattern[] }
  | { kind: "record"; fields: { name: string; pattern: Pattern }[] }
  | { kind: "named"; name: string; type: Type; pattern: Pattern };

export type Guarded = { cond: Expr; body: Expr };

export type Alternative = {
  patterns: Pattern[];
  guards: Guarded[];
  body: Expr;
};

export type Binding = {
  name: string;
  signature: PolyType | null;
  equations: Equation[];
};

export type Equation = {
  patterns: Pattern[];
  guards: Guarded[];
  body: Expr;
  where: Binding[];
};

export type Statement =
  | { kind: "bind"; pattern: Pattern; expr: Expr }
  | { kind: "discard"; expr: Expr }
  | { kind: "let"; bindings: Binding[] };

export type DataDeclaration = {
  kind: "data";
  name: string;
  params: string[];
  constructors: { name: string; fields: Type[] }[];
  derived: string[];
  showInstance: "generic" | "newtype" | "manual" | null;
  manualShow: Equation[] | null;
  isNewtype: boolean;
};

export type FunctionDeclaration = {
  kind: "function";
  binding: Binding;
};

export type ClassDeclaration = {
  kind: "class";
  name: string;
  param: string;
  superclasses: string[];
  methods: { name: string; type: Type }[];
};

export type InstanceDeclaration = {
  kind: "instance";
  className: string;
  head: Type;
  constraints: { className: string; type: Type }[];
  methods: Binding[];
  chained: boolean;
};

export type Declaration = DataDeclaration | FunctionDeclaration | ClassDeclaration | InstanceDeclaration;

export type Program = {
  moduleName: string;
  declarations: Declaration[];
  main: Statement[];
  imports: string[];
};

export const STANDARD_IMPORTS: string[] = [
  "import Prelude",
  "",
  "import Control.Lazy as CLazy",
  "import Control.Monad.Rec.Class (Step(..), tailRec, tailRecM)",
  "import Control.Monad.ST as ST",
  "import Control.Monad.ST.Ref as STRef",
  "import Control.Parallel (parTraverse, parSequence_)",
  "import Data.Array as Array",
  "import Data.Array.ST as STArray",
  "import Data.Char as Char",
  "import Data.Either (Either(..), either, note, hush, isLeft, isRight)",
  "import Data.Enum (fromEnum, toEnum, succ, pred)",
  "import Data.Exists (Exists, mkExists, runExists)",
  "import Data.Foldable (foldl, foldr, foldMap, sum, product, all, any, elem, intercalate, maximum, minimum, for_, traverse_)",
  "import Data.Function (on, applyN)",
  "import Data.Generic.Rep (class Generic)",
  "import Data.Int as Int",
  "import Data.Int.Bits as Bits",
  "import Data.Lazy as Lazy",
  "import Data.List as List",
  "import Data.Map as Map",
  "import Data.Maybe (Maybe(..), maybe, fromMaybe, isJust, isNothing)",
  "import Data.Newtype (class Newtype, unwrap, wrap, over)",
  "import Data.Number as Number",
  "import Data.Ord (abs, signum)",
  "import Data.Set as Set",
  "import Data.Show.Generic (genericShow)",
  "import Data.String as String",
  "import Data.String.CodePoints as CP",
  "import Data.String.CodeUnits as CU",
  "import Data.String.Pattern (Pattern(..), Replacement(..))",
  "import Data.Traversable (traverse, sequence, for)",
  "import Data.Tuple (Tuple(..), fst, snd, swap, uncurry, curry)",
  "import Data.Tuple.Nested ((/\\))",
  "import Data.Variant as Variant",
  "import Effect (Effect, foreachE, forE, whileE)",
  "import Effect.Aff as Aff",
  "import Effect.Class (liftEffect)",
  "import Effect.Console (log)",
  "import Effect.Exception as Exception",
  "import Effect.Ref as Ref",
  "import Effect.Unsafe (unsafePerformEffect)",
  "import Partial.Unsafe (unsafePartial, unsafeCrashWith)",
  "import Type.Proxy (Proxy(..))",
];

// ---------------------------------------------------------------- rendering

const INDENT = "  ";

const atomicExpr = (expr: Expr): boolean => {
  switch (expr.kind) {
    case "literal":
    case "variable":
    case "record":
    case "array":
      return true;
    case "access":
      return atomicExpr(expr.record);
    default:
      return false;
  }
};

/** Whether an expression extends as far to the right as it can, so that any following token is absorbed. */
const openEnded = (expr: Expr): boolean =>
  ["lambda", "ifThenElse", "case", "letIn", "doBlock"].includes(expr.kind);

const multiline = (text: string): boolean => text.includes("\n");

/** Renders an expression in argument position: atomic, or wrapped in parentheses. */
export const printAtom = (expr: Expr, indent: string): string => {
  const text = printExpr(expr, indent);
  return atomicExpr(expr) ? text : `(${text})`;
};

/** Renders an expression that other tokens follow on its line: open-ended forms get parentheses. */
const printOperand = (expr: Expr, indent: string): string => {
  const text = printExpr(expr, indent);
  return openEnded(expr) ? `(${text})` : text;
};

/** Renders an expression; nested layout blocks are indented past `indent`. */
export const printExpr = (expr: Expr, indent: string): string => {
  const deeper = indent + INDENT;
  switch (expr.kind) {
    case "literal":
      return expr.text.startsWith("-") ? `(${expr.text})` : expr.text;
    case "variable":
      return expr.name;
    case "apply": {
      const fn = printAtom(expr.fn, indent);
      const args = expr.args.map((arg) => printAtom(arg, deeper));
      return [fn, ...args].join(" ");
    }
    case "binary":
      return `${printAtom(expr.left, deeper)} ${expr.op} ${printAtom(expr.right, deeper)}`;
    case "section":
      return expr.side === "right"
        ? `(_ ${expr.op} ${printAtom(expr.operand, deeper)})`
        : `(${printAtom(expr.operand, deeper)} ${expr.op} _)`;
    case "lambda":
      return `\\${expr.params.map((p) => printPatternAtom(p)).join(" ")} -> ${printExpr(expr.body, deeper)}`;
    case "ifThenElse": {
      const cond = printOperand(expr.cond, deeper);
      const thenBranch = printOperand(expr.thenBranch, deeper);
      const elseBranch = printExpr(expr.elseBranch, deeper);
      if (!multiline(cond) && !multiline(thenBranch) && !multiline(elseBranch) && cond.length + thenBranch.length + elseBranch.length < 80) {
        return `if ${cond} then ${thenBranch} else ${elseBranch}`;
      }
      return `if ${cond}\n${deeper}then ${thenBranch}\n${deeper}else ${elseBranch}`;
    }
    case "case": {
      const scrutinees = expr.scrutinees.map((s) => printOperand(s, deeper)).join(", ");
      const alternatives = expr.alternatives.map((alt) => printAlternative(alt, deeper));
      return `case ${scrutinees} of\n${alternatives.join("\n")}`;
    }
    case "letIn": {
      const bindings = expr.bindings.map((binding) => printBinding(binding, deeper + INDENT)).join("\n");
      return `do\n${deeper}let\n${bindings}\n${deeper}${printExpr(expr.body, deeper)}`;
    }
    case "record":
      if (expr.fields.length === 0) return "{}";
      return `{ ${expr.fields.map((field) => `${field.name}: ${printOperand(field.value, deeper)}`).join(", ")} }`;
    case "access": {
      // purs rejects a field access directly on a record literal (Iris accepts it).
      const record = expr.record.kind === "record" ? `(${printExpr(expr.record, indent)})` : printAtom(expr.record, indent);
      return `${record}.${expr.field}`;
    }
    case "update": {
      const record = expr.record.kind === "variable" ? expr.record.name : `(${printExpr(expr.record, indent)})`;
      return `${record} { ${expr.fields.map((field) => `${field.name} = ${printOperand(field.value, deeper)}`).join(", ")} }`;
    }
    case "array":
      return `[${expr.elements.map((element) => printOperand(element, deeper)).join(", ")}]`;
    case "annotate":
      return `${printAtom(expr.expr, indent)} :: ${printType(expr.type)}`;
    case "doBlock": {
      const statements = expr.statements.map((statement) => printStatement(statement, deeper));
      return `do\n${[...statements, deeper + printExpr(expr.result, deeper)].join("\n")}`;
    }
  }
};

const printAlternative = (alternative: Alternative, indent: string): string => {
  const patterns = alternative.patterns.map((p) => printPattern(p)).join(", ");
  if (alternative.guards.length === 0) {
    return `${indent}${patterns} -> ${printExpr(alternative.body, indent + INDENT)}`;
  }
  const guards = alternative.guards.map(
    (guard) => `${indent}${INDENT}| ${printOperand(guard.cond, indent + INDENT + INDENT)} -> ${printExpr(guard.body, indent + INDENT + INDENT)}`,
  );
  return [`${indent}${patterns}`, ...guards, `${indent}${INDENT}| otherwise -> ${printExpr(alternative.body, indent + INDENT + INDENT)}`].join("\n");
};

export const printStatement = (statement: Statement, indent: string): string => {
  switch (statement.kind) {
    case "bind":
      return `${indent}${printPattern(statement.pattern)} <- ${printExpr(statement.expr, indent + INDENT)}`;
    case "discard":
      return `${indent}${printExpr(statement.expr, indent + INDENT)}`;
    case "let":
      return `${indent}let\n${statement.bindings.map((binding) => printBinding(binding, indent + INDENT)).join("\n")}`;
  }
};

export const printBinding = (binding: Binding, indent: string): string => {
  const lines: string[] = [];
  if (binding.signature) lines.push(`${indent}${binding.name} :: ${printPolyType(binding.signature)}`);
  for (const equation of binding.equations) lines.push(printEquation(binding.name, equation, indent));
  return lines.join("\n");
};

const printEquation = (name: string, equation: Equation, indent: string): string => {
  const head = [name, ...equation.patterns.map((p) => printPatternAtom(p))].join(" ");
  const deeper = indent + INDENT;
  const lines: string[] = [];
  if (equation.guards.length === 0) {
    lines.push(`${indent}${head} = ${printExpr(equation.body, deeper)}`);
  } else {
    lines.push(`${indent}${head}`);
    for (const guard of equation.guards) {
      lines.push(`${deeper}| ${printOperand(guard.cond, deeper + INDENT)} = ${printExpr(guard.body, deeper + INDENT)}`);
    }
    lines.push(`${deeper}| otherwise = ${printExpr(equation.body, deeper + INDENT)}`);
  }
  if (equation.where.length > 0) {
    lines.push(`${deeper}where`);
    for (const binding of equation.where) lines.push(printBinding(binding, deeper));
  }
  return lines.join("\n");
};

export const printPattern = (pattern: Pattern): string => {
  switch (pattern.kind) {
    case "wildcard":
      return "_";
    case "variable":
      return pattern.name;
    case "literal":
      return pattern.text.startsWith("-") ? `(${pattern.text})` : pattern.text;
    case "constructor":
      return pattern.args.length === 0
        ? pattern.name
        : `${pattern.name} ${pattern.args.map((arg) => printPatternAtom(arg)).join(" ")}`;
    case "array":
      return `[${pattern.elements.map((element) => printPattern(element)).join(", ")}]`;
    case "record":
      return `{ ${pattern.fields.map((field) => field.pattern.kind === "variable" && field.pattern.name === field.name ? field.name : `${field.name}: ${printPattern(field.pattern)}`).join(", ")} }`;
    case "named":
      return `${pattern.name}@${printPatternAtom(pattern.pattern)}`;
  }
};

const printPatternAtom = (pattern: Pattern): string => {
  const text = printPattern(pattern);
  const atomic =
    pattern.kind === "wildcard" ||
    pattern.kind === "variable" ||
    pattern.kind === "array" ||
    pattern.kind === "record" ||
    (pattern.kind === "literal" && !text.startsWith("-")) ||
    (pattern.kind === "constructor" && pattern.args.length === 0);
  return atomic ? text : `(${text})`;
};

const printDeclaration = (declaration: Declaration): string => {
  switch (declaration.kind) {
    case "data":
      return printData(declaration);
    case "function":
      return printBinding(declaration.binding, "");
    case "class": {
      const superclasses = declaration.superclasses.length > 0
        ? `(${declaration.superclasses.map((s) => `${s} ${declaration.param}`).join(", ")}) <= `
        : "";
      const methods = declaration.methods.map((method) => `${INDENT}${method.name} :: ${printType(method.type)}`);
      return [`class ${superclasses}${declaration.name} ${declaration.param} where`, ...methods].join("\n");
    }
    case "instance": {
      const constraints = declaration.constraints.length > 0
        ? `(${declaration.constraints.map((c) => `${c.className} ${printTypeArgument(c.type)}`).join(", ")}) => `
        : "";
      const keyword = declaration.chained ? "else instance" : "instance";
      const methods = declaration.methods.map((method) => printBinding(method, INDENT));
      return [`${keyword} ${constraints}${declaration.className} ${printTypeArgument(declaration.head)} where`, ...methods].join("\n");
    }
  }
};

const printTypeArgument = (type: Type): string => {
  const text = printType(type);
  const atomic = ["Int", "Number", "Boolean", "Char", "String", "Unit", "Ordering", "Record", "Var"].includes(type.tag) ||
    (type.tag === "Data" && type.args.length === 0);
  return atomic ? text : `(${text})`;
};

const printData = (declaration: DataDeclaration): string => {
  const head = [declaration.name, ...declaration.params].join(" ");
  const lines: string[] = [];
  const constructors = declaration.constructors.map(
    (constructor) => [constructor.name, ...constructor.fields.map(printTypeArgument)].join(" "),
  );
  if (declaration.isNewtype) {
    lines.push(`newtype ${head} = ${constructors[0]}`);
  } else if (constructors.length === 0) {
    lines.push(`data ${head}`);
  } else {
    lines.push(`data ${head}`);
    constructors.forEach((constructor, index) => lines.push(`${INDENT}${index === 0 ? "=" : "|"} ${constructor}`));
  }
  const applied = printTypeArgument({ tag: "Data", name: declaration.name, args: declaration.params.map((p) => ({ tag: "Var", name: p })) });
  const constrained = (className: string) =>
    declaration.params.length > 0
      ? `(${declaration.params.map((p) => `${className} ${p}`).join(", ")}) => ${className} ${applied}`
      : `${className} ${applied}`;
  for (const className of declaration.derived) {
    if (className === "Generic") lines.push(`derive instance Generic ${applied} _`);
    else if (className === "Newtype") lines.push(`derive instance Newtype ${applied} _`);
    else if (className === "Functor") lines.push(`derive instance Functor ${declaration.name}`);
    else if (declaration.isNewtype && declaration.showInstance === "newtype") lines.push(`derive newtype instance ${constrained(className)}`);
    else lines.push(`derive instance ${constrained(className)}`);
  }
  if (declaration.showInstance === "generic") {
    lines.push(`instance ${constrained("Show")} where`);
    lines.push(`${INDENT}show value = genericShow value`);
  } else if (declaration.showInstance === "newtype") {
    lines.push(`derive newtype instance ${constrained("Show")}`);
  } else if (declaration.showInstance === "manual" && declaration.manualShow) {
    lines.push(`instance ${constrained("Show")} where`);
    lines.push(printBinding({ name: "show", signature: null, equations: declaration.manualShow }, INDENT));
  }
  return lines.join("\n");
};

export const printProgram = (program: Program): string => {
  const parts: string[] = [`module ${program.moduleName} where`, "", ...program.imports, ""];
  for (const declaration of program.declarations) {
    parts.push(printDeclaration(declaration));
    parts.push("");
  }
  parts.push("main :: Effect Unit");
  parts.push("main = do");
  for (const statement of program.main) parts.push(printStatement(statement, INDENT));
  if (program.main.length === 0) parts.push(`${INDENT}pure unit`);
  parts.push("");
  return parts.join("\n");
};
