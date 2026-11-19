// Type-directed generation of random, well-typed PureScript programs. Every production builds an
// expression of a requested type from smaller expressions of the types it needs, so a generated
// program typechecks by construction; one that does not is a generator bug.

import { Random } from "./random.ts";
import * as T from "./types.ts";
import { DataEnvironment, DataInfo, PolyType, Type, hasClass, printType, substitute, typeEquals } from "./types.ts";
import {
  Alternative,
  Binding,
  ClassDeclaration,
  DataDeclaration,
  Declaration,
  Equation,
  Expr,
  InstanceDeclaration,
  Pattern,
  Program,
  STANDARD_IMPORTS,
  Statement,
} from "./ast.ts";

export const FEATURES = [
  "prims",
  "strings",
  "surrogates",
  "transcendental",
  "adts",
  "records",
  "patterns",
  "classes",
  "hof",
  "containers",
  "lists",
  "poly",
  "lazy",
  "recursion",
  "effects",
  "exceptions",
  "st",
  "aff",
] as const;

export type Feature = (typeof FEATURES)[number];

export type GeneratorOptions = {
  weights: Record<Feature, number>;
  statements: number;
  depth: number;
};

export const defaultWeights = (): Record<Feature, number> => ({
  prims: 1,
  strings: 1,
  surrogates: 0,
  transcendental: 0,
  adts: 1,
  records: 1,
  patterns: 1,
  classes: 1,
  hof: 1,
  containers: 1,
  lists: 1,
  poly: 1,
  lazy: 1,
  recursion: 1,
  effects: 1,
  exceptions: 1,
  st: 1,
  aff: 1,
});

type Variable = { name: string; type: Type };

type Environment = {
  variables: Variable[];
  assumed: Map<string, Set<string>>;
  typeVars: string[];
  refs: Variable[];
  inEffect: boolean;
};

type UserFunction = { name: string; signature: PolyType; userClassConstraints: string[]; boundedFirstArgument: number | null };

type UserClass = {
  declaration: ClassDeclaration;
  instances: InstanceDeclaration[];
  catchAll: boolean;
};

type Production = { feature: Feature; weight: number; build: () => Expr | null };

const literal = (type: Type, text: string): Expr => ({ kind: "literal", type, text });
const variable = (type: Type, name: string): Expr => ({ kind: "variable", type, name });
const apply = (type: Type, fn: Expr, ...args: Expr[]): Expr => ({ kind: "apply", type, fn, args });
const call = (type: Type, name: string, ...args: Expr[]): Expr => apply(type, variable(T.Unit, name), ...args);
const binary = (type: Type, op: string, left: Expr, right: Expr): Expr => ({ kind: "binary", type, op, left, right });
const lambda = (type: Type, params: Pattern[], body: Expr): Expr => ({ kind: "lambda", type, params, body });
const annotate = (type: Type, expr: Expr): Expr => ({ kind: "annotate", type, expr });
const varPattern = (name: string, type: Type): Pattern => ({ kind: "variable", name, type });
const wildcard: Pattern = { kind: "wildcard" };

const INT_EDGES = [0, 1, -1, 2, 3, 7, 10, 42, 100, 255, 256, 1000, 65535, 65536, 46340, 46341, 2147483647, -2147483647, 1073741824, -1073741824, 123456789, 1000000];
const NUMBER_EDGES = ["0.0", "1.0", "-1.0", "0.5", "1.5", "-2.5", "0.1", "0.2", "3.0", "10.0", "100.0", "1.0e21", "1.0e-7", "123456789.123", "1.7976931348623157e308", "5.0e-324", "4294967296.0", "2147483648.0", "2147483647.0", "-2147483648.0", "-0.0", "1.0e15", "9007199254740993.0", "0.3", "1.0e-10", "123.456e5"];
const CHAR_EDGES = ["'a'", "'Z'", "'0'", "' '", "'\\n'", "'\\t'", "'\\\\'", "'\\''", "'\\x00'", "'\\x7F'", "'\\xE9'", "'\\xFF'", "'\\x2028'", "'\\xFFFF'", "'\\xFEFF'", "'\\x4E2D'", "'~'", "'\\x80'"];
const SURROGATE_CHARS = ["'\\xD800'", "'\\xDC00'", "'\\xD83D'", "'\\xDFFF'"];
// Hex escapes are padded to six digits, so that a hex-digit character after them is not swallowed.
const STRING_EDGES = ['""', '"a"', '"abc"', '"Hello, World!"', '"\\""', '"\\\\"', '"\\n"', '"\\t"', '"  padded  "', '"\\x0000E9"', '"stra\\x0000DFe"', '"\\x000130stanbul"', '"\\x0003A3\\x000391\\x0003A3"', '"\\x0065E5\\x00672C\\x008A9E"', '"\\x01F600"', '"a\\x01F600b"', '"\\x10FFFF"', '"\\x000000"', '"\\x00FEFF"', '"\\x002028"', '"e\\x000301"', '"\\x01F1E9\\x01F1EA"', '"\\x01D4B3"', '"1.5"', '"42"', '"-7"', '"0x1F"', '"NaN"', '"Infinity"', '"1e3"', '"a,b,,c"', '","', '"  "', '"ABC def"', '"x=1;y=2"', '"\\x01F600\\x01F600\\x01F600"', '"\\x0000C5"', '"A\\x00030A"', '"\\r\\n"', '"tab\\there"'];
const SURROGATE_STRINGS = ['"\\x00D800"', '"a\\x00DC00b"', '"\\x00D83D"', '"\\x00DFFF\\x00D800"', '"x\\x00DE00"'];
const FIELD_NAMES = ["a", "b", "c", "x", "y", "z", "n", "s", "k", "v", "name", "count", "items"];

const QUALIFIED_CONSTRUCTORS: Record<string, string> = { Cons: "List.Cons", Nil: "List.Nil" };

export class Generator {
  private readonly rng: Random;
  private readonly options: GeneratorOptions;
  private readonly dataEnvironment: DataEnvironment = new Map();
  private readonly declarations: Declaration[] = [];
  private readonly functions: UserFunction[] = [];
  private readonly classes: UserClass[] = [];
  private readonly rowFunctions: { name: string; field: string; type: Type; mode: "get" | "bump" }[] = [];
  private counter = 0;
  private hasRecursiveShowBox = false;
  private nestFunctions: { name: string; wrapper: "Array" | "Maybe" | "Tuple" }[] = [];
  private rankN: { name: string; kind: "identity" | "show" }[] = [];

  constructor(seed: number, options: GeneratorOptions) {
    this.rng = new Random(seed);
    this.options = options;
  }

  private on(feature: Feature): boolean {
    return this.options.weights[feature] > 0;
  }

  private weight(feature: Feature, base: number): number {
    return base * this.options.weights[feature];
  }

  private fresh(prefix: string): string {
    this.counter++;
    return `${prefix}${this.counter}`;
  }

  // ---------------------------------------------------------------- programs

  generate(moduleName: string): Program {
    if (this.on("adts")) this.declareDataTypes();
    if (this.on("classes")) this.declareClasses();
    if (this.on("records")) this.declareRowFunctions();
    if (this.on("poly")) this.declarePolymorphicIdioms();
    if (this.on("recursion")) this.declareRecursiveFunctions();
    const functionCount = this.rng.int(2, 6);
    for (let i = 0; i < functionCount; i++) this.declareFunction();
    const main = this.generateMain();
    const imports = [...STANDARD_IMPORTS, "import Control.Alt ((<|>))", "import Data.Bifunctor (lmap, rmap, bimap)", "import Data.Maybe (fromJust)", "import Data.Monoid (power, guard)"];
    return { moduleName, declarations: this.declarations, main, imports };
  }

  private generateMain(): Statement[] {
    const statements: Statement[] = [];
    const env: Environment = { variables: [], assumed: new Map(), typeVars: [], refs: [], inEffect: true };
    const count = this.rng.int(Math.max(2, this.options.statements - 3), this.options.statements + 3);
    // An Aff statement goes last: JavaScript runs a launched fiber synchronously up to its first
    // asynchronous step, so anything logged after it would interleave differently by design.
    let aff: Statement | null = null;
    const weights = this.options.weights;
    for (let i = 0; i < count; i++) {
      const choice = this.rng.weighted<string>([
        [weights.effects * 0.9, "effects"],
        [weights.aff * 0.3, "aff"],
        [weights.exceptions * 0.5, "exceptions"],
        [weights.st * 1.4, "st"],
        [weights.effects * 0.9, "imperativeEffect"],
        [3, "log"],
      ]);
      if (choice === "effects") statements.push(...this.effectStatements(env));
      else if (choice === "aff" && aff === null) aff = this.affStatement(env);
      else if (choice === "exceptions") statements.push(this.exceptionStatement(env));
      else if (choice === "st") statements.push({ kind: "discard", expr: call(T.effect(T.Unit), "log", binary(T.String, "<>", literal(T.String, `"${i}: "`), call(T.String, "show", this.stProgram(env)))) });
      else if (choice === "imperativeEffect") statements.push(...this.imperativeEffectStatements(env, i));
      else statements.push(this.logStatement(env, i));
    }
    if (aff) statements.push(aff);
    return statements;
  }

  // ---------------------------------------------------------------- imperative programs

  /** An element type for mutable cells and arrays, kept small so that loops stay cheap. */
  private cellType(env: Environment): Type {
    return this.rng.weighted<Type>([
      [4, T.Int],
      [2, T.Number],
      [2, T.String],
      [1, T.Boolean],
      [1, T.maybe(T.Int)],
      [1, T.tuple(T.Int, T.String)],
      [1, T.record([{ name: "n", type: T.Int }, { name: "s", type: T.String }])],
      [1, this.showableType({ ...env, typeVars: [] }, 1)],
    ]);
  }

  /** An index expression, out of bounds about a third of the time. */
  private index(loopVariable: string | null): Expr {
    const literalIndex = () => literal(T.Int, String(this.rng.pick([0, 1, 2, 3, -1, -2, 5, 7, 100, 2147483647])));
    if (loopVariable === null) return literalIndex();
    return this.rng.weighted<() => Expr>([
      [3, () => variable(T.Int, loopVariable)],
      [1, () => binary(T.Int, "*", variable(T.Int, loopVariable), literal(T.Int, "2"))],
      [1, () => binary(T.Int, "-", variable(T.Int, loopVariable), literal(T.Int, "1"))],
      [1, () => binary(T.Int, "+", variable(T.Int, loopVariable), literal(T.Int, "100"))],
      [1, () => call(T.Int, "negate", variable(T.Int, loopVariable))],
      [1, literalIndex],
    ])();
  }

  private discard(expr: Expr): Statement {
    return { kind: "discard", expr };
  }

  private bind(name: string, type: Type, expr: Expr): Statement {
    return { kind: "bind", pattern: varPattern(name, type), expr };
  }

  private block(statements: Statement[], result: Expr): Expr {
    return { kind: "doBlock", type: T.Unit, statements, result };
  }

  /**
   * `ST.run` over an accumulator STRef, a value STRef and an STArray, driven by for/foreach/while
   * loops, tailRecM, out-of-bounds peeks and pokes, freezes and nested runs. The result is a
   * snapshot of all the state, so every step shows in the output.
   */
  private stProgram(env: Environment): Expr {
    const element = this.cellType(env);
    const acc = this.fresh("acc");
    const cell = this.fresh("cell");
    const arr = this.fresh("arr");
    const snapshots: { name: string; type: Type }[] = [];
    const pureEnv: Environment = { ...env, inEffect: false, refs: [] };
    const elementExpr = (loopVariable: string | null) => {
      const scope = loopVariable ? this.extend(pureEnv, { name: loopVariable, type: T.Int }) : pureEnv;
      return this.expr(element, scope, 2);
    };
    const bumpAcc = (delta: Expr) => this.discard(call(T.Unit, "void", call(T.Unit, "STRef.modify", lambda(T.Unit, [varPattern("a", T.Int)], binary(T.Int, "+", variable(T.Int, "a"), delta)), variable(T.Unit, acc))));
    const statements: Statement[] = [
      this.bind(acc, T.Unit, call(T.Unit, "STRef.new", literal(T.Int, "0"))),
      this.bind(cell, T.Unit, call(T.Unit, "STRef.new", elementExpr(null))),
      this.rng.chance(0.7)
        ? this.bind(arr, T.Unit, call(T.Unit, "STArray.thaw", this.expr(T.array(element), pureEnv, 2)))
        : this.bind(arr, T.Unit, variable(T.Unit, "STArray.new")),
    ];
    const stepCount = this.rng.int(3, 8);
    for (let step = 0; step < stepCount; step++) {
      const i = this.fresh("i");
      const m = this.fresh("m");
      const ok = this.fresh("ok");
      const n = this.fresh("n");
      const choice = this.rng.int(0, 15);
      switch (choice) {
        case 0:
        case 1: {
          const body = this.block(
            [this.bind(ok, T.Boolean, call(T.Unit, "STArray.poke", this.index(i), elementExpr(i), variable(T.Unit, arr)))],
            call(T.Unit, "void", call(T.Unit, "STRef.modify", lambda(T.Unit, [varPattern("a", T.Int)], binary(T.Int, "+", variable(T.Int, "a"), { kind: "ifThenElse", type: T.Int, cond: variable(T.Boolean, ok), thenBranch: literal(T.Int, "1"), elseBranch: literal(T.Int, "-1000") })), variable(T.Unit, acc))),
          );
          statements.push(this.discard(call(T.Unit, "ST.for", literal(T.Int, String(this.rng.pick([0, -2, 1]))), literal(T.Int, String(this.rng.pick([0, 3, 5, 8]))), lambda(T.Unit, [varPattern(i, T.Int)], body))));
          break;
        }
        case 2:
        case 3: {
          const indices: Expr = { kind: "array", type: T.array(T.Int), elements: Array.from({ length: this.rng.int(1, 4) }, () => this.index(null)) };
          const peeked = this.bind(m, T.maybe(element), call(T.Unit, "STArray.peek", variable(T.Int, i), variable(T.Unit, arr)));
          const onHit = call(T.Unit, "void", call(T.Unit, "STRef.write", variable(element, "v"), variable(T.Unit, cell)));
          const branch: Expr = {
            kind: "case",
            type: T.Unit,
            scrutinees: [variable(T.maybe(element), m)],
            alternatives: [
              { patterns: [{ kind: "constructor", name: "Just", args: [varPattern("v", element)] }], guards: [], body: onHit },
              { patterns: [{ kind: "constructor", name: "Nothing", args: [] }], guards: [], body: call(T.Unit, "void", call(T.Unit, "STRef.modify", lambda(T.Unit, [varPattern("a", T.Int)], binary(T.Int, "-", variable(T.Int, "a"), literal(T.Int, "7"))), variable(T.Unit, acc))) },
            ],
          };
          statements.push(this.discard(call(T.Unit, "ST.foreach", indices, lambda(T.Unit, [varPattern(i, T.Int)], this.block([peeked], branch)))));
          break;
        }
        case 4:
          statements.push(this.bind(n, T.Int, call(T.Unit, "STArray.push", elementExpr(null), variable(T.Unit, arr))));
          statements.push(bumpAcc(variable(T.Int, n)));
          break;
        case 5:
          statements.push(this.bind(n, T.Int, call(T.Unit, this.rng.pick(["STArray.pushAll", "STArray.unshiftAll"]), this.expr(T.array(element), pureEnv, 2), variable(T.Unit, arr))));
          statements.push(bumpAcc(variable(T.Int, n)));
          break;
        case 6: {
          const f = this.expr(T.fn(element, element), pureEnv, 2);
          statements.push(this.bind(ok, T.Boolean, call(T.Unit, "STArray.modify", this.index(null), f, variable(T.Unit, arr))));
          statements.push(bumpAcc({ kind: "ifThenElse", type: T.Int, cond: variable(T.Boolean, ok), thenBranch: literal(T.Int, "10"), elseBranch: literal(T.Int, "-10") }));
          break;
        }
        case 7:
          statements.push(this.bind(m, T.maybe(element), call(T.Unit, this.rng.pick(["STArray.pop", "STArray.shift"]), variable(T.Unit, arr))));
          statements.push(bumpAcc(call(T.Int, "maybe", literal(T.Int, "-3"), lambda(T.Unit, [wildcard], literal(T.Int, "3")), variable(T.maybe(element), m))));
          if (this.rng.chance(0.5)) statements.push(this.discard(call(T.Unit, "void", call(T.Unit, "STRef.modify", lambda(T.Unit, [varPattern("old", element)], call(element, "fromMaybe", variable(element, "old"), variable(T.maybe(element), m))), variable(T.Unit, cell)))));
          break;
        case 8: {
          const removed = this.fresh("removed");
          statements.push(this.bind(removed, T.array(element), call(T.Unit, "STArray.splice", this.index(null), literal(T.Int, String(this.rng.pick([0, 1, 2, 100, -1]))), this.expr(T.array(element), pureEnv, 1), variable(T.Unit, arr))));
          statements.push(bumpAcc(call(T.Int, "Array.length", variable(T.array(element), removed))));
          break;
        }
        case 9:
          statements.push(this.bind(n, T.Int, call(T.Unit, "STArray.length", variable(T.Unit, arr))));
          statements.push(bumpAcc(binary(T.Int, "*", variable(T.Int, n), literal(T.Int, "100"))));
          break;
        case 10: {
          const counter = this.fresh("cnt");
          statements.push(this.bind(counter, T.Unit, call(T.Unit, "STRef.new", literal(T.Int, "0"))));
          const cond = call(T.Unit, "map", { kind: "section", type: T.Unit, op: "<", operand: literal(T.Int, String(this.rng.int(1, 6))), side: "right" }, call(T.Unit, "STRef.read", variable(T.Unit, counter)));
          const body = this.block(
            [this.bind(n, T.Int, call(T.Unit, "STRef.modify", { kind: "section", type: T.Unit, op: "+", operand: literal(T.Int, "1"), side: "right" }, variable(T.Unit, counter)))],
            call(T.Unit, "void", call(T.Unit, "STArray.poke", this.index(n), elementExpr(n), variable(T.Unit, arr))),
          );
          statements.push(this.discard(call(T.Unit, "ST.while", cond, body)));
          break;
        }
        case 11: {
          const stepBody = this.block(
            [this.bind(ok, T.Boolean, call(T.Unit, "STArray.poke", this.index(i), elementExpr(i), variable(T.Unit, arr)))],
            call(T.Unit, "pure", call(T.Unit, "Loop", binary(T.Int, "+", variable(T.Int, i), literal(T.Int, String(this.rng.pick([1, 2])))))),
          );
          const loop: Expr = { kind: "ifThenElse", type: T.Unit, cond: binary(T.Boolean, ">=", variable(T.Int, i), literal(T.Int, String(this.rng.pick([3, 5, 7])))), thenBranch: call(T.Unit, "pure", call(T.Unit, "Done", variable(T.Unit, "unit"))), elseBranch: stepBody };
          statements.push(this.discard(call(T.Unit, "tailRecM", lambda(T.Unit, [varPattern(i, T.Int)], loop), literal(T.Int, "0"))));
          break;
        }
        case 12: {
          const innerRef = this.fresh("inner");
          const innerRun = call(T.Int, "ST.run", this.block(
            [this.bind(innerRef, T.Unit, call(T.Unit, "STRef.new", this.expr(T.Int, pureEnv, 2))), this.discard(call(T.Unit, "void", call(T.Unit, "STRef.modify", this.expr(T.fn(T.Int, T.Int), pureEnv, 2), variable(T.Unit, innerRef))))],
            call(T.Unit, "STRef.read", variable(T.Unit, innerRef)),
          ));
          statements.push(bumpAcc(innerRun));
          break;
        }
        case 13: {
          const snapshot = this.fresh("snap");
          statements.push(this.bind(snapshot, T.array(element), call(T.Unit, "STArray.freeze", variable(T.Unit, arr))));
          snapshots.push({ name: snapshot, type: T.array(element) });
          break;
        }
        case 14: {
          const copy = this.fresh("copy");
          const inner = this.fresh("st");
          const action = lambda(T.Unit, [varPattern(inner, T.Unit)], call(T.Unit, "void", call(T.Unit, "STArray.poke", this.index(null), elementExpr(null), variable(T.Unit, inner))));
          statements.push(this.bind(copy, T.array(element), call(T.Unit, "STArray.withArray", action, this.expr(T.array(element), pureEnv, 2))));
          snapshots.push({ name: copy, type: T.array(element) });
          break;
        }
        default: {
          if (hasClass("Ord", element, this.dataEnvironment)) {
            statements.push(this.discard(call(T.Unit, "void", call(T.Unit, "STArray.sort", variable(T.Unit, arr)))));
          } else {
            const assoc = this.fresh("assoc");
            statements.push(this.bind(assoc, T.Unit, call(T.Unit, "STArray.toAssocArray", variable(T.Unit, arr))));
            statements.push(bumpAcc(call(T.Int, "Array.length", variable(T.Unit, assoc))));
          }
          break;
        }
      }
    }
    const finalAcc = this.fresh("total");
    const finalCell = this.fresh("value");
    const finalArray = this.fresh("frozen");
    statements.push(this.bind(finalAcc, T.Int, call(T.Unit, "STRef.read", variable(T.Unit, acc))));
    statements.push(this.bind(finalCell, element, call(T.Unit, "STRef.read", variable(T.Unit, cell))));
    statements.push(this.bind(finalArray, T.array(element), call(T.Unit, this.rng.chance(0.8) ? "STArray.freeze" : "STArray.unsafeFreeze", variable(T.Unit, arr))));
    const snapshotRecord: Expr = { kind: "record", type: T.Unit, fields: snapshots.map((s) => ({ name: s.name, value: variable(s.type, s.name) })) };
    const result = call(T.Unit, "Tuple", variable(T.Int, finalAcc), call(T.Unit, "Tuple", variable(element, finalCell), snapshots.length > 0 ? call(T.Unit, "Tuple", variable(T.array(element), finalArray), snapshotRecord) : variable(T.array(element), finalArray)));
    const resultType = T.tuple(T.Int, T.tuple(element, snapshots.length > 0 ? T.tuple(T.array(element), T.record(snapshots)) : T.array(element)));
    return annotate(resultType, call(resultType, "ST.run", this.block(statements, call(T.Unit, "pure", result))));
  }

  /** Effect.Ref cells and loops (forE, foreachE, whileE, tailRecM, for_) logging as they go. */
  private imperativeEffectStatements(env: Environment, index: number): Statement[] {
    const element = this.cellType(env);
    const counter = this.fresh("counter");
    const cell = this.fresh("cellRef");
    const items = this.fresh("items");
    const statements: Statement[] = [
      this.bind(counter, T.ref(T.Int), call(T.Unit, "Ref.new", literal(T.Int, "0"))),
      this.bind(cell, T.ref(element), call(T.Unit, "Ref.new", this.expr(element, env, 2))),
      this.bind(items, T.ref(T.array(element)), call(T.Unit, "Ref.new", this.expr(T.array(element), env, 2))),
    ];
    const log = (expr: Expr) => this.discard(call(T.effect(T.Unit), "log", binary(T.String, "<>", literal(T.String, `"${index}: "`), expr)));
    const bump = (delta: Expr) => this.discard(call(T.Unit, "Ref.modify_", lambda(T.Unit, [varPattern("c", T.Int)], binary(T.Int, "+", variable(T.Int, "c"), delta)), variable(T.Unit, counter)));
    const stepCount = this.rng.int(2, 5);
    for (let step = 0; step < stepCount; step++) {
      const i = this.fresh("i");
      const scope = this.extend(env, { name: i, type: T.Int });
      switch (this.rng.int(0, 6)) {
        case 0: {
          const body = this.block(
            [this.discard(call(T.Unit, "Ref.modify_", lambda(T.Unit, [varPattern("xs", T.array(element))], call(T.Unit, "Array.snoc", variable(T.Unit, "xs"), this.expr(element, scope, 2))), variable(T.Unit, items)))],
            call(T.Unit, "Ref.modify_", { kind: "section", type: T.Unit, op: "+", operand: variable(T.Int, i), side: "right" }, variable(T.Unit, counter)),
          );
          statements.push(this.discard(call(T.Unit, "forE", literal(T.Int, String(this.rng.pick([0, -1, 2]))), literal(T.Int, String(this.rng.pick([0, 1, 4, 6]))), lambda(T.Unit, [varPattern(i, T.Int)], body))));
          break;
        }
        case 1: {
          const x = this.fresh("x");
          const body = call(T.Unit, "Ref.modify_", lambda(T.Unit, [varPattern("old", element)], this.expr(element, this.extend(env, { name: "old", type: element }, { name: x, type: element }), 2)), variable(T.Unit, cell));
          statements.push(this.discard(call(T.Unit, "foreachE", this.expr(T.array(element), env, 2), lambda(T.Unit, [varPattern(x, element)], body))));
          break;
        }
        case 2: {
          const cond = call(T.Unit, "map", { kind: "section", type: T.Unit, op: "<", operand: literal(T.Int, String(this.rng.int(1, 5))), side: "right" }, call(T.Unit, "Ref.read", variable(T.Unit, counter)));
          const body = this.block(
            [bump(literal(T.Int, "1"))],
            call(T.Unit, "Ref.modify_", lambda(T.Unit, [varPattern("xs", T.array(element))], call(T.Unit, "Array.drop", literal(T.Int, "1"), variable(T.Unit, "xs"))), variable(T.Unit, items)),
          );
          statements.push(this.discard(call(T.Unit, "whileE", cond, body)));
          break;
        }
        case 3: {
          const stepBody = this.block([bump(variable(T.Int, i))], call(T.Unit, "pure", call(T.Unit, "Loop", binary(T.Int, "+", variable(T.Int, i), literal(T.Int, "1")))));
          const loop: Expr = { kind: "ifThenElse", type: T.Unit, cond: binary(T.Boolean, ">", variable(T.Int, i), literal(T.Int, String(this.rng.pick([2, 4, 1000])))), thenBranch: call(T.Unit, "pure", call(T.Unit, "Done", variable(T.Unit, "unit"))), elseBranch: stepBody };
          statements.push(this.discard(call(T.Unit, "tailRecM", lambda(T.Unit, [varPattern(i, T.Int)], loop), literal(T.Int, "0"))));
          break;
        }
        case 4: {
          const result = this.fresh("r");
          const modifier = lambda(T.Unit, [varPattern("c", T.Int)], { kind: "record", type: T.Unit, fields: [{ name: "state", value: binary(T.Int, "+", variable(T.Int, "c"), literal(T.Int, "1")) }, { name: "value", value: binary(T.Int, "*", variable(T.Int, "c"), literal(T.Int, "2")) }] });
          statements.push(this.bind(result, T.Int, call(T.Unit, "Ref.modify'", modifier, variable(T.Unit, counter))));
          statements.push(log(call(T.String, "show", variable(T.Int, result))));
          break;
        }
        case 5: {
          const x = this.fresh("x");
          const body = log(call(T.String, "show", this.expr(this.showableType(env, 1), this.extend(env, { name: x, type: element }), 2)));
          statements.push(this.discard(call(T.Unit, "for_", this.expr(T.array(element), env, 2), lambda(T.Unit, [varPattern(x, element)], body.expr))));
          break;
        }
        default: {
          const previous = this.fresh("prev");
          statements.push(this.bind(previous, element, call(T.Unit, "Ref.modify", this.expr(T.fn(element, element), env, 2), variable(T.Unit, cell))));
          statements.push(log(call(T.String, "show", variable(element, previous))));
          break;
        }
      }
    }
    const count = this.fresh("count");
    const value = this.fresh("value");
    const list = this.fresh("list");
    statements.push(this.bind(count, T.Int, call(T.Unit, "Ref.read", variable(T.Unit, counter))));
    statements.push(this.bind(value, element, call(T.Unit, "Ref.read", variable(T.Unit, cell))));
    statements.push(this.bind(list, T.array(element), call(T.Unit, "Ref.read", variable(T.Unit, items))));
    statements.push(log(call(T.String, "show", call(T.Unit, "Tuple", variable(T.Int, count), call(T.Unit, "Tuple", variable(element, value), variable(T.array(element), list))))));
    return statements;
  }

  private logStatement(env: Environment, index: number): Statement {
    const type = this.showableType(env, this.rng.int(1, 4));
    const expr = this.expr(type, env, this.options.depth);
    const shown = typeEquals(type, T.String) && this.rng.chance(0.5) ? expr : call(T.String, "show", expr);
    const labelled = binary(T.String, "<>", literal(T.String, `"${index}: "`), shown);
    return { kind: "discard", expr: call(T.effect(T.Unit), "log", labelled) };
  }

  // ---------------------------------------------------------------- data types

  private declareDataTypes(): void {
    const count = this.rng.int(1, 3);
    for (let i = 0; i < count; i++) {
      if (this.rng.chance(0.3)) this.declareNewtype();
      else this.declareData();
    }
  }

  private declareData(): void {
    const name = this.fresh("D");
    const params = this.rng.chance(0.35) ? ["a"] : [];
    const env: Environment = { variables: [], assumed: new Map(params.map((p) => [p, new Set(["Show", "Eq", "Ord"])])), typeVars: params, refs: [], inEffect: false };
    const self = T.data(name, params.map(T.tvar));
    const constructorCount = this.rng.int(1, 4);
    const constructors: { name: string; fields: Type[] }[] = [];
    let recursive = false;
    let hasFunctionField = false;
    for (let i = 0; i < constructorCount; i++) {
      const fieldCount = this.rng.weighted<number>([[2, 0], [3, 1], [2, 2], [1, 3]]);
      const fields: Type[] = [];
      for (let f = 0; f < fieldCount; f++) {
        if (i > 0 && this.rng.chance(0.25)) {
          fields.push(self);
          recursive = true;
        } else if (this.on("hof") && this.rng.chance(0.05)) {
          fields.push(T.fn(T.Int, T.Int));
          hasFunctionField = true;
        } else {
          fields.push(this.type(env, 2, { showable: true, allowData: true }));
        }
      }
      constructors.push({ name: `${name}${String.fromCharCode(65 + i)}`, fields });
    }
    // A parameter no constructor mentions would be a phantom whose instantiation no value fixes.
    if (params.length > 0 && !constructors.some((c) => c.fields.some((f) => T.freeVars(f).has(params[0])))) {
      constructors[0].fields.push(T.tvar(params[0]));
    }
    const classes = new Set<string>();
    const derived: string[] = [];
    let showInstance: DataDeclaration["showInstance"] = null;
    let manualShow: Equation[] | null = null;
    if (!hasFunctionField) {
      derived.push("Eq");
      classes.add("Eq");
      if (this.rng.chance(0.85)) {
        derived.push("Ord");
        classes.add("Ord");
      }
      if (this.rng.chance(0.75)) {
        derived.push("Generic");
        showInstance = "generic";
      } else {
        showInstance = "manual";
        manualShow = constructors.map((constructor) => {
          const vars = constructor.fields.map((field, index) => varPattern(`f${index}`, field));
          const pieces: Expr[] = [literal(T.String, `"<${constructor.name}"`)];
          vars.forEach((v, index) => {
            pieces.push(literal(T.String, '" "'));
            const fieldType = constructor.fields[index];
            pieces.push(hasClass("Show", fieldType, this.dataEnvironment, env.assumed) ? call(T.String, "show", variable(fieldType, `f${index}`)) : literal(T.String, '"?"'));
          });
          pieces.push(literal(T.String, '">"'));
          const body = pieces.reduce((acc, piece) => binary(T.String, "<>", acc, piece));
          return { patterns: [{ kind: "constructor", name: constructor.name, args: vars }], guards: [], body, where: [] };
        });
      }
      classes.add("Show");
    }
    if (params.length > 0 && this.rng.chance(0.5) && constructors.every((c) => c.fields.every((f) => functorSafe(f, params[0], name)))) derived.push("Functor");
    const declaration: DataDeclaration = { kind: "data", name, params, constructors, derived, showInstance, manualShow, isNewtype: false };
    this.declarations.push(declaration);
    this.dataEnvironment.set(name, { name, params, constructors, classes, isNewtype: false });
    if (recursive && this.on("recursion")) this.declareDataFold(name, params, constructors);
  }

  /** A structurally recursive function over a recursive data type: one equation per constructor. */
  private declareDataFold(dataName: string, params: string[], constructors: { name: string; fields: Type[] }[]): void {
    const name = this.fresh("fold");
    const resultType = this.rng.pick([T.Int, T.String]);
    const typeArgs = params.map(() => T.Int);
    const bindings = new Map(params.map((p, i) => [p, typeArgs[i]]));
    const self = T.data(dataName, typeArgs);
    const signature: PolyType = { vars: [], constraints: [], type: T.fn(self, resultType) };
    const env: Environment = { variables: [], assumed: new Map(), typeVars: [], refs: [], inEffect: false };
    const equations: Equation[] = constructors.map((constructor) => {
      const variables: Variable[] = [];
      const patterns: Pattern[] = [];
      const parts: Expr[] = [literal(resultType, resultType.tag === "Int" ? "1" : `"${constructor.name}"`)];
      const args = constructor.fields.map((field, index) => {
        const fieldType = substitute(field, bindings);
        const fieldName = `f${index}`;
        if (fieldType.tag === "Data" && fieldType.name === dataName) {
          parts.push(call(resultType, name, variable(fieldType, fieldName)));
        } else {
          variables.push({ name: fieldName, type: fieldType });
        }
        return varPattern(fieldName, fieldType);
      });
      patterns.push({ kind: "constructor", name: constructor.name, args });
      const combined = parts.reduce((acc, part) => binary(resultType, resultType.tag === "Int" ? "+" : "<>", acc, part));
      const extra = variables.length > 0 && this.rng.chance(0.6) ? this.expr(resultType, { ...env, variables }, 2) : null;
      const body = extra ? binary(resultType, resultType.tag === "Int" ? "+" : "<>", combined, extra) : combined;
      return { patterns, guards: [], body, where: [] };
    });
    this.declarations.push({ kind: "function", binding: { name, signature, equations } });
    this.functions.push({ name, signature, userClassConstraints: [], boundedFirstArgument: null });
  }

  /** Recursive functions whose first argument bounds the recursion, so that call sites stay finite. */
  private declareRecursiveFunctions(): void {
    const count = this.rng.int(1, 3);
    for (let i = 0; i < count; i++) {
      const shape = this.rng.pick(["countdown", "nonTail", "structural", "mutual"] as const);
      const env: Environment = { variables: [], assumed: new Map(), typeVars: [], refs: [], inEffect: false };
      const valueType = this.type(env, 1, { showable: true, allowData: true });
      if (shape === "countdown") {
        const name = this.fresh("count");
        const signature: PolyType = { vars: [], constraints: [], type: T.fnN([T.Int, valueType], valueType) };
        const bodyEnv = this.extend(env, { name: "n", type: T.Int }, { name: "acc", type: valueType });
        const step = this.expr(valueType, bodyEnv, 2);
        const equations: Equation[] = [{
          patterns: [varPattern("n", T.Int), varPattern("acc", valueType)],
          guards: [{ cond: binary(T.Boolean, "<=", variable(T.Int, "n"), literal(T.Int, "0")), body: variable(valueType, "acc") }],
          body: call(valueType, name, binary(T.Int, "-", variable(T.Int, "n"), literal(T.Int, "1")), step),
          where: [],
        }];
        this.declarations.push({ kind: "function", binding: { name, signature, equations } });
        this.functions.push({ name, signature, userClassConstraints: [], boundedFirstArgument: growable(valueType) ? 12 : 20000 });
      } else if (shape === "nonTail") {
        const name = this.fresh("deep");
        const signature: PolyType = { vars: [], constraints: [], type: T.fnN([T.Int, valueType], valueType) };
        const bodyEnv = this.extend(env, { name: "n", type: T.Int }, { name: "seed", type: valueType }, { name: "below", type: valueType });
        const combine = this.expr(valueType, bodyEnv, 2);
        const recursive: Expr = {
          kind: "letIn",
          type: valueType,
          bindings: [{ name: "below", signature: null, equations: [{ patterns: [], guards: [], body: call(valueType, name, binary(T.Int, "-", variable(T.Int, "n"), literal(T.Int, "1")), variable(valueType, "seed")), where: [] }] }],
          body: combine,
        };
        const equations: Equation[] = [{
          patterns: [varPattern("n", T.Int), varPattern("seed", valueType)],
          guards: [{ cond: binary(T.Boolean, "<=", variable(T.Int, "n"), literal(T.Int, "0")), body: variable(valueType, "seed") }],
          body: recursive,
          where: [],
        }];
        this.declarations.push({ kind: "function", binding: { name, signature, equations } });
        this.functions.push({ name, signature, userClassConstraints: [], boundedFirstArgument: growable(valueType) ? 8 : 1500 });
      } else if (shape === "structural") {
        const name = this.fresh("walk");
        const element = this.type(env, 1, { showable: true, allowData: true });
        const signature: PolyType = { vars: [], constraints: [], type: T.fnN([T.array(element), valueType], valueType) };
        const bodyEnv = this.extend(env, { name: "head", type: element }, { name: "acc", type: valueType });
        const step = this.expr(valueType, bodyEnv, 2);
        const unconsType = T.maybe(T.record([{ name: "head", type: element }, { name: "tail", type: T.array(element) }]));
        const body: Expr = {
          kind: "case",
          type: valueType,
          scrutinees: [call(unconsType, "Array.uncons", variable(T.array(element), "xs"))],
          alternatives: [
            { patterns: [{ kind: "constructor", name: "Nothing", args: [] }], guards: [], body: variable(valueType, "acc") },
            { patterns: [{ kind: "constructor", name: "Just", args: [{ kind: "record", fields: [{ name: "head", pattern: varPattern("head", element) }, { name: "tail", pattern: varPattern("tail", T.array(element)) }] }] }], guards: [], body: call(valueType, name, variable(T.array(element), "tail"), step) },
          ],
        };
        const equations: Equation[] = [{ patterns: [varPattern("xs", T.array(element)), varPattern("acc", valueType)], guards: [], body, where: [] }];
        this.declarations.push({ kind: "function", binding: { name, signature, equations } });
        this.functions.push({ name, signature, userClassConstraints: [], boundedFirstArgument: null });
      } else {
        const first = this.fresh("ping");
        const second = this.fresh("pong");
        const signature: PolyType = { vars: [], constraints: [], type: T.fnN([T.Int, valueType], valueType) };
        const bodyEnv = this.extend(env, { name: "n", type: T.Int }, { name: "acc", type: valueType });
        const makeEquations = (self: string, other: string): Equation[] => [{
          patterns: [varPattern("n", T.Int), varPattern("acc", valueType)],
          guards: [{ cond: binary(T.Boolean, "<=", variable(T.Int, "n"), literal(T.Int, "0")), body: this.expr(valueType, bodyEnv, 2) }],
          body: call(valueType, other, binary(T.Int, "-", variable(T.Int, "n"), literal(T.Int, "1")), this.expr(valueType, bodyEnv, 2)),
          where: [],
        }];
        this.declarations.push({ kind: "function", binding: { name: first, signature, equations: makeEquations(first, second) } });
        this.declarations.push({ kind: "function", binding: { name: second, signature, equations: makeEquations(second, first) } });
        const limit = growable(valueType) ? 10 : 5000;
        this.functions.push({ name: first, signature, userClassConstraints: [], boundedFirstArgument: limit });
        this.functions.push({ name: second, signature, userClassConstraints: [], boundedFirstArgument: limit });
      }
    }
  }

  private declareNewtype(): void {
    const name = this.fresh("N");
    const env: Environment = { variables: [], assumed: new Map(), typeVars: [], refs: [], inEffect: false };
    const inner = this.type(env, 2, { showable: true, allowData: true });
    const constructors = [{ name, fields: [inner] }];
    const classes = new Set(["Show", "Eq"]);
    const derived = ["Newtype", "Eq"];
    if (hasClass("Ord", inner, this.dataEnvironment)) {
      derived.push("Ord");
      classes.add("Ord");
    }
    const useNewtypeDeriving = this.rng.chance(0.5);
    let showInstance: DataDeclaration["showInstance"] = useNewtypeDeriving ? "newtype" : "generic";
    if (!useNewtypeDeriving) derived.push("Generic");
    const declaration: DataDeclaration = { kind: "data", name, params: [], constructors, derived, showInstance, manualShow: null, isNewtype: true };
    this.declarations.push(declaration);
    this.dataEnvironment.set(name, { name, params: [], constructors, classes, isNewtype: true });
  }

  // ---------------------------------------------------------------- classes

  private declareClasses(): void {
    const count = this.rng.int(1, 2);
    for (let i = 0; i < count; i++) {
      const name = this.fresh("Class");
      const methodType = T.fn(T.tvar("a"), T.String);
      const methodName = `describe${name}`;
      const superclasses = this.classes.length > 0 && this.rng.chance(0.4) ? [this.classes[this.classes.length - 1].declaration.name] : [];
      const declaration: ClassDeclaration = { kind: "class", name, param: "a", superclasses, methods: [{ name: methodName, type: methodType }] };
      this.declarations.push(declaration);
      const user: UserClass = { declaration, instances: [], catchAll: false };
      this.classes.push(user);
      const heads: { head: Type; constraints: { className: string; type: Type }[]; assumed: Map<string, Set<string>> }[] = [];
      const superclassInstances = superclasses.length > 0 ? this.classes.find((c) => c.declaration.name === superclasses[0])! : null;
      const assumedA = new Map([["a", new Set([name])]]);
      const instanceTypeFor = (type: Type): boolean => superclassInstances === null || this.userClassHas(superclassInstances, type, assumedA);
      for (const base of this.rng.shuffle([T.Int, T.String, T.Boolean, T.Number, T.Char])) {
        if (heads.length >= 3) break;
        if (instanceTypeFor(base)) heads.push({ head: base, constraints: [], assumed: new Map() });
      }
      if (this.rng.chance(0.7) && instanceTypeFor(T.array(T.tvar("a")))) {
        heads.push({ head: T.array(T.tvar("a")), constraints: [{ className: name, type: T.tvar("a") }], assumed: assumedA });
      }
      if (this.rng.chance(0.5) && instanceTypeFor(T.maybe(T.tvar("a")))) {
        heads.push({ head: T.maybe(T.tvar("a")), constraints: [{ className: name, type: T.tvar("a") }], assumed: assumedA });
      }
      for (const [dataName, info] of this.dataEnvironment) {
        if (info.params.length === 0 && this.rng.chance(0.6) && instanceTypeFor(T.data(dataName))) heads.push({ head: T.data(dataName), constraints: [], assumed: new Map() });
      }
      const catchAll = this.rng.chance(0.35) && superclasses.length === 0;
      heads.forEach((entry, index) => {
        const param = varPattern("value", entry.head);
        const env: Environment = { variables: [{ name: "value", type: entry.head }], assumed: entry.assumed, typeVars: [...entry.assumed.keys()], refs: [], inEffect: false };
        const chained = index > 0 && (catchAll || this.rng.chance(0.3));
        const body = this.describeBody(user, entry.head, env);
        const method: Binding = { name: methodName, signature: null, equations: [{ patterns: [param], guards: [], body, where: [] }] };
        const instance: InstanceDeclaration = { kind: "instance", className: name, head: entry.head, constraints: entry.constraints, methods: [method], chained };
        this.declarations.push(instance);
        user.instances.push(instance);
      });
      if (catchAll) {
        const env: Environment = { variables: [{ name: "value", type: T.tvar("a") }], assumed: new Map([["a", new Set(["Show"])]]), typeVars: ["a"], refs: [], inEffect: false };
        const body = binary(T.String, "<>", literal(T.String, '"other:"'), call(T.String, "show", variable(T.tvar("a"), "value")));
        const method: Binding = { name: methodName, signature: null, equations: [{ patterns: [varPattern("value", T.tvar("a"))], guards: [], body, where: [] }] };
        const instance: InstanceDeclaration = { kind: "instance", className: name, head: T.tvar("a"), constraints: [{ className: "Show", type: T.tvar("a") }], methods: [method], chained: true };
        this.declarations.push(instance);
        user.instances.push(instance);
        user.catchAll = true;
        void env;
      }
    }
  }

  private describeBody(user: UserClass, head: Type, env: Environment): Expr {
    const name = user.declaration.name;
    const value = variable(head, "value");
    const tag = literal(T.String, `"${name}/${printType(head).replace(/[^A-Za-z]/g, "")}:"`);
    if (head.tag === "Array") {
      const inner = head.arg;
      const described = call(T.array(T.String), "map", variable(T.Unit, `describe${name}`), value);
      return binary(T.String, "<>", tag, call(T.String, "intercalate", literal(T.String, '"|"'), described));
      void inner;
    }
    if (head.tag === "Maybe") {
      return binary(T.String, "<>", tag, call(T.String, "maybe", literal(T.String, '"none"'), variable(T.Unit, `describe${name}`), value));
    }
    const superclassMethod = user.declaration.superclasses.length > 0 ? `describe${user.declaration.superclasses[0]}` : null;
    const shown = hasClass("Show", head, this.dataEnvironment, env.assumed) ? call(T.String, "show", value) : literal(T.String, '"?"');
    const base = binary(T.String, "<>", tag, shown);
    if (superclassMethod) return binary(T.String, "<>", base, binary(T.String, "<>", literal(T.String, '"/"'), call(T.String, superclassMethod, value)));
    if (this.rng.chance(0.5)) {
      const extra = this.expr(T.String, { ...env, variables: [...env.variables] }, 2);
      return binary(T.String, "<>", base, extra);
    }
    return base;
  }

  /** Whether a set of assumed classes entails a class, through superclasses. */
  private entails(assumedClasses: Set<string>, className: string): boolean {
    if (assumedClasses.has(className)) return true;
    for (const assumedClass of assumedClasses) {
      const user = this.classes.find((c) => c.declaration.name === assumedClass);
      if (user && this.entails(new Set(user.declaration.superclasses), className)) return true;
    }
    return false;
  }

  private userClassHas(user: UserClass, type: Type, assumed: Map<string, Set<string>> = new Map()): boolean {
    if (type.tag === "Var") return this.entails(assumed.get(type.name) ?? new Set(), user.declaration.name);
    for (const instance of user.instances) {
      const head = instance.head;
      if (head.tag === "Var") {
        if (user.catchAll && hasClass("Show", type, this.dataEnvironment, assumed)) return true;
        continue;
      }
      if (head.tag === "Array" && type.tag === "Array") return this.userClassHas(user, type.arg, assumed);
      if (head.tag === "Maybe" && type.tag === "Maybe") return this.userClassHas(user, type.arg, assumed);
      if (typeEquals(head, type)) return true;
    }
    return false;
  }

  // ---------------------------------------------------------------- row polymorphism and idioms

  private declareRowFunctions(): void {
    if (!this.rng.chance(0.7)) return;
    const field = this.rng.pick(["x", "n", "count"]);
    const getName = this.fresh("get");
    const bumpName = this.fresh("bump");
    const getBinding: Binding = {
      name: getName,
      signature: { vars: [], constraints: [], type: T.tvar(`forall r. { ${field} :: Int | r } -> Int`) },
      equations: [{ patterns: [varPattern("r", T.Int)], guards: [], body: { kind: "access", type: T.Int, record: variable(T.Int, "r"), field }, where: [] }],
    };
    const bumpBinding: Binding = {
      name: bumpName,
      signature: { vars: [], constraints: [], type: T.tvar(`forall r. { ${field} :: Int | r } -> { ${field} :: Int | r }`) },
      equations: [{
        patterns: [varPattern("r", T.Int)],
        guards: [],
        body: { kind: "update", type: T.Int, record: variable(T.Int, "r"), fields: [{ name: field, value: binary(T.Int, "+", { kind: "access", type: T.Int, record: variable(T.Int, "r"), field }, literal(T.Int, "1")) }] },
        where: [],
      }],
    };
    this.declarations.push({ kind: "function", binding: getBinding }, { kind: "function", binding: bumpBinding });
    this.rowFunctions.push({ name: getName, field, type: T.Int, mode: "get" }, { name: bumpName, field, type: T.Int, mode: "bump" });
  }

  private declarePolymorphicIdioms(): void {
    if (this.rng.chance(0.6)) {
      const wrapper = this.rng.pick(["Array", "Maybe", "Tuple"] as const);
      const name = this.fresh("nest");
      const wrap = (x: Expr): Expr =>
        wrapper === "Array" ? { kind: "array", type: T.array(x.type), elements: [x] }
          : wrapper === "Maybe" ? call(T.maybe(x.type), "Just", x)
          : call(T.tuple(x.type, x.type), "Tuple", x, x);
      const a = T.tvar("a");
      const binding: Binding = {
        name,
        signature: { vars: ["a"], constraints: [{ className: "Show", type: a }], type: T.fnN([T.Int, a], T.String) },
        equations: [
          { patterns: [{ kind: "literal", text: "0" }, varPattern("x", a)], guards: [], body: call(T.String, "show", variable(a, "x")), where: [] },
          { patterns: [varPattern("n", T.Int), varPattern("x", a)], guards: [], body: call(T.String, name, binary(T.Int, "-", variable(T.Int, "n"), literal(T.Int, "1")), wrap(variable(a, "x"))), where: [] },
        ],
      };
      this.declarations.push({ kind: "function", binding });
      this.nestFunctions.push({ name, wrapper });
    }
    if (this.rng.chance(0.6)) {
      const name = this.fresh("rankN");
      const kind = this.rng.pick(["identity", "show"] as const);
      this.rankN.push({ name, kind });
      const signatureText = kind === "identity"
        ? "(forall a. a -> a) -> Int -> String -> String"
        : "(forall a. Show a => a -> String) -> Int -> Boolean -> String";
      const body = kind === "identity"
        ? "show (f n) <> f s"
        : "f n <> \"/\" <> f b <> \"/\" <> f [n]";
      const params = kind === "identity" ? ["f", "n", "s"] : ["f", "n", "b"];
      const binding: Binding = {
        name,
        signature: { vars: [], constraints: [], type: T.tvar(signatureText) },
        equations: [{ patterns: params.map((p) => varPattern(p, T.Unit)), guards: [], body: literal(T.String, body), where: [] }],
      };
      this.declarations.push({ kind: "function", binding });
    }
    if (this.rng.chance(0.5)) {
      this.declarations.push({
        kind: "data",
        name: "ShowBox",
        params: ["a"],
        constructors: [{ name: "ShowBox", fields: [T.fn(T.tvar("a"), T.String), T.tvar("a")] }],
        derived: [],
        showInstance: null,
        manualShow: null,
        isNewtype: false,
      });
      this.hasRecursiveShowBox = true;
    }
  }

  // ---------------------------------------------------------------- functions

  private declareFunction(): void {
    const name = this.fresh("fn");
    const polymorphic = this.on("poly") && this.rng.chance(0.3);
    const typeVars = polymorphic ? ["a"] : [];
    const assumed = new Map<string, Set<string>>();
    const constraints: PolyType["constraints"] = [];
    const userClassConstraints: string[] = [];
    if (polymorphic) {
      const classesForA = new Set<string>(["Show"]);
      if (this.rng.chance(0.6)) classesForA.add("Eq");
      if (classesForA.has("Eq") && this.rng.chance(0.6)) classesForA.add("Ord");
      if (this.classes.length > 0 && this.rng.chance(0.4)) {
        const user = this.rng.pick(this.classes);
        classesForA.add(user.declaration.name);
        userClassConstraints.push(user.declaration.name);
      }
      assumed.set("a", classesForA);
      for (const className of classesForA) constraints.push({ className, type: T.tvar("a") });
    }
    const env: Environment = { variables: [], assumed, typeVars, refs: [], inEffect: false };
    const paramCount = this.rng.int(1, 3);
    const paramTypes: Type[] = [];
    if (polymorphic) paramTypes.push(T.tvar("a"));
    while (paramTypes.length < paramCount) paramTypes.push(this.type(env, 2, { showable: false, allowData: true, allowFunctions: this.on("hof") }));
    const resultType = this.type(env, 2, { showable: true, allowData: true });
    const signature: PolyType = { vars: typeVars, constraints, type: T.fnN(paramTypes, resultType) };
    const equations: Equation[] = [];
    const equationCount = this.on("patterns") ? this.rng.int(1, 3) : 1;
    for (let i = 0; i < equationCount; i++) {
      const last = i === equationCount - 1;
      const patterns: Pattern[] = [];
      const bound: Variable[] = [];
      paramTypes.forEach((paramType, index) => {
        if (last || !this.on("patterns") || paramType.tag === "Var") {
          patterns.push(varPattern(`p${index}`, paramType));
          bound.push({ name: `p${index}`, type: paramType });
        } else {
          const generated = this.pattern(paramType, 2, env, `p${index}`);
          patterns.push(generated.pattern);
          bound.push(...generated.bindings);
        }
      });
      const guardEnv: Environment = { ...env, variables: [...bound] };
      const guards: Alternative["guards"] = [];
      if (this.on("patterns") && this.rng.chance(0.4)) {
        const guardCount = this.rng.int(1, 2);
        for (let g = 0; g < guardCount; g++) {
          guards.push({ cond: this.expr(T.Boolean, guardEnv, 2), body: this.expr(resultType, guardEnv, this.options.depth - 1) });
        }
      }
      // A `where` clause scopes over the equation's bodies but not over its guards.
      const bodyEnv: Environment = { ...env, variables: [...bound] };
      const where: Binding[] = [];
      if (this.rng.chance(0.3)) {
        const helperName = `helper${i}`;
        const helperType = this.type(bodyEnv, 1, { showable: true, allowData: true });
        const helper: Binding = { name: helperName, signature: null, equations: [{ patterns: [], guards: [], body: this.expr(helperType, bodyEnv, 2), where: [] }] };
        where.push(helper);
        bodyEnv.variables.push({ name: helperName, type: helperType });
      }
      const body = this.expr(resultType, bodyEnv, this.options.depth - 1);
      equations.push({ patterns, guards, body, where });
    }
    this.declarations.push({ kind: "function", binding: { name, signature, equations } });
    this.functions.push({ name, signature, userClassConstraints, boundedFirstArgument: null });
  }

  // ---------------------------------------------------------------- types

  private type(
    env: Environment,
    size: number,
    options: { showable: boolean; allowData?: boolean; allowFunctions?: boolean },
  ): Type {
    for (let attempt = 0; attempt < 30; attempt++) {
      const candidate = this.typeOnce(env, size, options);
      if (!options.showable || hasClass("Show", candidate, this.dataEnvironment, env.assumed)) return candidate;
    }
    return T.Int;
  }

  private typeOnce(env: Environment, size: number, options: { allowData?: boolean; allowFunctions?: boolean }): Type {
    const choices: [number, () => Type][] = [
      [5, () => T.Int],
      [this.weight("prims", 3), () => T.Number],
      [2, () => T.Boolean],
      [this.weight("strings", 2), () => T.Char],
      [this.weight("strings", 4), () => T.String],
      [0.3, () => T.Unit],
      [0.5, () => T.Ordering],
    ];
    if (env.typeVars.length > 0) choices.push([3, () => T.tvar(this.rng.pick(env.typeVars))]);
    if (size > 0) {
      const smaller = size - 1;
      choices.push(
        [this.weight("containers", 3), () => T.maybe(this.typeOnce(env, smaller, options))],
        [this.weight("containers", 1.5), () => T.either(this.typeOnce(env, smaller, options), this.typeOnce(env, smaller, options))],
        [this.weight("containers", 2), () => T.tuple(this.typeOnce(env, smaller, options), this.typeOnce(env, smaller, options))],
        [this.weight("containers", 3), () => T.array(this.typeOnce(env, smaller, options))],
        [this.weight("lists", 1), () => T.list(this.typeOnce(env, smaller, options))],
        [this.weight("containers", 1), () => T.map(this.keyType(env, smaller), this.typeOnce(env, smaller, options))],
        [this.weight("containers", 1), () => T.set(this.keyType(env, smaller))],
        [this.weight("records", 2), () => this.recordType(env, smaller, options)],
        [this.weight("lazy", 0.7), () => T.lazy(this.typeOnce(env, smaller, options))],
      );
      if (options.allowFunctions) choices.push([this.weight("hof", 1.5), () => T.fn(this.typeOnce(env, smaller, options), this.typeOnce(env, smaller, options))]);
      if (options.allowData && this.dataEnvironment.size > 0) {
        choices.push([this.weight("adts", 3), () => {
          const info = this.rng.pick([...this.dataEnvironment.values()]);
          return T.data(info.name, info.params.map(() => this.typeOnce(env, smaller, options)));
        }]);
      }
    }
    return this.rng.weighted(choices)();
  }

  private keyType(env: Environment, size: number): Type {
    for (let attempt = 0; attempt < 20; attempt++) {
      const candidate = this.typeOnce({ ...env, typeVars: [] }, Math.min(size, 1), { allowData: true });
      if (hasClass("Ord", candidate, this.dataEnvironment, env.assumed) && hasClass("Show", candidate, this.dataEnvironment, env.assumed)) return candidate;
    }
    return T.Int;
  }

  private recordType(env: Environment, size: number, options: { allowData?: boolean; allowFunctions?: boolean }): Type {
    const count = this.rng.int(1, 3);
    const names = this.rng.shuffle(FIELD_NAMES).slice(0, count);
    return T.record(names.map((name) => ({ name, type: this.typeOnce(env, size, options) })));
  }

  private showableType(env: Environment, size: number): Type {
    return this.type(env, size, { showable: true, allowData: true });
  }

  // ---------------------------------------------------------------- expressions

  private expr(type: Type, env: Environment, depth: number): Expr {
    if (depth <= 0) return this.leaf(type, env);
    const productions = this.productions(type, env, depth).filter((p) => p.weight > 0);
    const candidates = [...productions];
    for (let attempt = 0; attempt < 6 && candidates.length > 0; attempt++) {
      const chosen = this.rng.weighted(candidates.map((p) => [p.weight, p] as [number, Production]));
      const built = chosen.build();
      if (built) return built;
      candidates.splice(candidates.indexOf(chosen), 1);
    }
    return this.leaf(type, env);
  }

  private variablesOf(type: Type, env: Environment): Variable[] {
    return env.variables.filter((v) => typeEquals(v.type, type));
  }

  /** The simplest expression of a type: a variable in scope or a literal. */
  private leaf(type: Type, env: Environment): Expr {
    const variables = this.variablesOf(type, env);
    if (variables.length > 0 && (type.tag === "Var" || this.rng.chance(0.5))) return variable(type, this.rng.pick(variables).name);
    return this.defaultValue(type, env);
  }

  defaultValue(type: Type, env: Environment): Expr {
    switch (type.tag) {
      case "Int":
        return this.intLiteral();
      case "Number":
        return this.numberLiteral();
      case "Boolean":
        return literal(type, this.rng.pick(["true", "false"]));
      case "Char":
        return this.charLiteral();
      case "String":
        return this.stringLiteral();
      case "Unit":
        return variable(type, "unit");
      case "Ordering":
        return variable(type, this.rng.pick(["LT", "EQ", "GT"]));
      case "Maybe":
        return this.rng.chance(0.3) ? annotate(type, variable(type, "Nothing")) : call(type, "Just", this.leaf(type.arg, env));
      case "Either":
        return annotate(type, this.rng.chance(0.5) ? call(type, "Left", this.leaf(type.left, env)) : call(type, "Right", this.leaf(type.right, env)));
      case "Tuple":
        return call(type, "Tuple", this.leaf(type.first, env), this.leaf(type.second, env));
      case "Array": {
        const count = this.rng.weighted<number>([[2, 0], [3, 1], [3, 2], [2, 3]]);
        const elements: Expr[] = [];
        for (let i = 0; i < count; i++) elements.push(this.leaf(type.arg, env));
        return count === 0 ? annotate(type, { kind: "array", type, elements }) : { kind: "array", type, elements };
      }
      case "List":
        return call(type, "List.fromFoldable", this.defaultValue(T.array(type.arg), env));
      case "Map":
        return call(type, "Map.fromFoldable", this.defaultValue(T.array(T.tuple(type.key, type.value)), env));
      case "Set":
        return call(type, "Set.fromFoldable", this.defaultValue(T.array(type.arg), env));
      case "Record":
        return { kind: "record", type, fields: type.fields.map((field) => ({ name: field.name, value: this.leaf(field.type, env) })) };
      case "Function": {
        const name = this.fresh("arg");
        const body = this.leaf(type.to, { ...env, variables: [...env.variables, { name, type: type.from }] });
        return lambda(type, [varPattern(name, type.from)], body);
      }
      case "Data": {
        const info = this.dataEnvironment.get(type.name);
        if (!info) return literal(type, "undefined");
        const bindings = new Map(info.params.map((p, i) => [p, type.args[i]]));
        const nonRecursive = info.constructors.filter((c) => !c.fields.some((f) => f.tag === "Data" && f.name === type.name));
        const constructor = this.rng.pick(nonRecursive.length > 0 ? nonRecursive : info.constructors);
        const args = constructor.fields.map((field) => this.leaf(substitute(field, bindings), env));
        const applied = args.length === 0 ? variable(type, constructor.name) : call(type, constructor.name, ...args);
        return args.length === 0 || info.params.length > 0 ? annotate(type, applied) : applied;
      }
      case "Lazy":
        return call(type, "Lazy.defer", lambda(T.fn(T.Unit, type.arg), [wildcard], this.leaf(type.arg, env)));
      case "Effect":
        return annotate(type, call(type, "pure", this.leaf(type.arg, env)));
      case "Ref":
        return literal(type, "undefined");
      case "Var": {
        const variables = this.variablesOf(type, env);
        if (variables.length > 0) return variable(type, this.rng.pick(variables).name);
        return literal(type, "undefined");
      }
    }
  }

  private intLiteral(): Expr {
    if (this.rng.chance(0.15)) return annotate(T.Int, variable(T.Int, this.rng.pick(["bottom", "top"])));
    const value = this.rng.chance(0.5) ? this.rng.pick(INT_EDGES) : this.rng.int(-20, 20);
    return literal(T.Int, String(value));
  }

  private numberLiteral(): Expr {
    if (this.rng.chance(0.15)) return variable(T.Number, this.rng.pick(["Number.nan", "Number.infinity", "Number.pi", "Number.e"]));
    if (this.rng.chance(0.3)) {
      const value = (this.rng.next() - 0.5) * 1000;
      const text = value.toFixed(this.rng.int(0, 6));
      return literal(T.Number, text.includes(".") ? text : `${text}.0`);
    }
    return literal(T.Number, this.rng.pick(NUMBER_EDGES));
  }

  private charLiteral(): Expr {
    const pool = this.on("surrogates") && this.rng.chance(0.15) ? SURROGATE_CHARS : CHAR_EDGES;
    return literal(T.Char, this.rng.pick(pool));
  }

  private stringLiteral(): Expr {
    const pool = this.on("surrogates") && this.rng.chance(0.15) ? SURROGATE_STRINGS : STRING_EDGES;
    return literal(T.String, this.rng.pick(pool));
  }

  private boundVariable(prefix: string, type: Type): { name: string; pattern: Pattern; variable: Variable } {
    const name = this.fresh(prefix);
    return { name, pattern: varPattern(name, type), variable: { name, type } };
  }

  private extend(env: Environment, ...variables: Variable[]): Environment {
    return { ...env, variables: [...env.variables, ...variables] };
  }

  /** A type with some structure to match on, for case expressions and eliminators. */
  private scrutineeType(env: Environment, depth: number): Type {
    const choices: [number, () => Type][] = [
      [3, () => T.maybe(this.showableType(env, 1))],
      [2, () => T.either(this.showableType(env, 1), this.showableType(env, 1))],
      [2, () => T.tuple(this.showableType(env, 1), this.showableType(env, 1))],
      [2, () => T.Boolean],
      [2, () => T.Int],
      [this.weight("strings", 1), () => T.String],
      [this.weight("containers", 2), () => T.array(this.showableType(env, 1))],
      [this.weight("lists", 1), () => T.list(this.showableType(env, 1))],
      [this.weight("records", 2), () => this.recordType(env, 1, { allowData: true })],
    ];
    if (this.dataEnvironment.size > 0) {
      choices.push([this.weight("adts", 4), () => {
        const info = this.rng.pick([...this.dataEnvironment.values()]);
        return T.data(info.name, info.params.map(() => this.showableType(env, 1)));
      }]);
    }
    void depth;
    return this.rng.weighted(choices)();
  }

  private productions(type: Type, env: Environment, depth: number): Production[] {
    const productions: Production[] = [...this.genericProductions(type, env, depth)];
    switch (type.tag) {
      case "Int":
        productions.push(...this.intProductions(env, depth));
        break;
      case "Number":
        productions.push(...this.numberProductions(env, depth));
        break;
      case "Boolean":
        productions.push(...this.booleanProductions(env, depth));
        break;
      case "Char":
        productions.push(...this.charProductions(env, depth));
        break;
      case "String":
        productions.push(...this.stringProductions(env, depth));
        break;
      case "Ordering":
        productions.push({ feature: "prims", weight: 4, build: () => {
          const operand = this.showableType(env, 1);
          if (!hasClass("Ord", operand, this.dataEnvironment, env.assumed)) return null;
          return call(type, "compare", this.expr(operand, env, depth - 1), this.expr(operand, env, depth - 1));
        } });
        productions.push({ feature: "prims", weight: 1, build: () => binary(type, "<>", this.expr(type, env, depth - 1), this.expr(type, env, depth - 1)) });
        break;
      case "Unit":
        productions.push({ feature: "prims", weight: 1, build: () => variable(type, "unit") });
        break;
      case "Maybe":
        productions.push(...this.maybeProductions(type, type.arg, env, depth));
        break;
      case "Either":
        productions.push(...this.eitherProductions(type, type.left, type.right, env, depth));
        break;
      case "Tuple":
        productions.push(...this.tupleProductions(type, type.first, type.second, env, depth));
        break;
      case "Array":
        productions.push(...this.arrayProductions(type, type.arg, env, depth));
        break;
      case "List":
        productions.push(...this.listProductions(type, type.arg, env, depth));
        break;
      case "Map":
        productions.push(...this.mapProductions(type, type.key, type.value, env, depth));
        break;
      case "Set":
        productions.push(...this.setProductions(type, type.arg, env, depth));
        break;
      case "Record":
        productions.push(...this.recordProductions(type, env, depth));
        break;
      case "Function":
        productions.push(...this.functionProductions(type, type.from, type.to, env, depth));
        break;
      case "Data":
        productions.push(...this.dataProductions(type, env, depth));
        break;
      case "Lazy":
        productions.push(...this.lazyProductions(type, type.arg, env, depth));
        break;
      case "Effect":
        productions.push(...this.effectProductions(type, type.arg, env, depth));
        break;
      default:
        break;
    }
    return productions;
  }

  private genericProductions(type: Type, env: Environment, depth: number): Production[] {
    const productions: Production[] = [
      { feature: "prims", weight: 3, build: () => {
        const variables = this.variablesOf(type, env);
        return variables.length > 0 ? variable(type, this.rng.pick(variables).name) : null;
      } },
      { feature: "prims", weight: 1.5, build: () => ({
        kind: "ifThenElse",
        type,
        cond: this.expr(T.Boolean, env, depth - 1),
        thenBranch: this.expr(type, env, depth - 1),
        elseBranch: this.expr(type, env, depth - 1),
      }) },
      { feature: "patterns", weight: 3, build: () => this.caseExpression(type, env, depth) },
      { feature: "prims", weight: 1.5, build: () => this.letExpression(type, env, depth) },
      { feature: "hof", weight: 3, build: () => this.callUserFunction(type, env, depth) },
      { feature: "hof", weight: 1, build: () => {
        const argType = this.showableType(env, 1);
        const bound = this.boundVariable("v", argType);
        const body = this.expr(type, this.extend(env, bound.variable), depth - 1);
        return apply(type, lambda(T.fn(argType, type), [bound.pattern], body), this.expr(argType, env, depth - 1));
      } },
      { feature: "containers", weight: 2, build: () => {
        const inner = this.showableType(env, 1);
        const bound = this.boundVariable("m", inner);
        const body = this.expr(type, this.extend(env, bound.variable), depth - 1);
        return call(type, "maybe", this.expr(type, env, depth - 1), lambda(T.fn(inner, type), [bound.pattern], body), this.expr(T.maybe(inner), env, depth - 1));
      } },
      { feature: "containers", weight: 1.5, build: () => call(type, "fromMaybe", this.expr(type, env, depth - 1), this.expr(T.maybe(type), env, depth - 1)) },
      { feature: "containers", weight: 1.5, build: () => {
        const left = this.showableType(env, 1);
        const right = this.showableType(env, 1);
        const l = this.boundVariable("l", left);
        const r = this.boundVariable("r", right);
        return call(type, "either",
          lambda(T.fn(left, type), [l.pattern], this.expr(type, this.extend(env, l.variable), depth - 1)),
          lambda(T.fn(right, type), [r.pattern], this.expr(type, this.extend(env, r.variable), depth - 1)),
          this.expr(T.either(left, right), env, depth - 1));
      } },
      { feature: "containers", weight: 1, build: () => {
        const other = this.showableType(env, 1);
        const first = this.rng.chance(0.5);
        const tupleType = first ? T.tuple(type, other) : T.tuple(other, type);
        return call(type, first ? "fst" : "snd", this.expr(tupleType, env, depth - 1));
      } },
      { feature: "hof", weight: 2, build: () => {
        const element = this.showableType(env, 1);
        const acc = this.boundVariable("acc", type);
        const x = this.boundVariable("x", element);
        const body = this.expr(type, this.extend(env, acc.variable, x.variable), depth - 1);
        const container = this.on("lists") && this.rng.chance(0.3) ? T.list(element) : T.array(element);
        return call(type, "foldl", lambda(T.fnN([type, element], type), [acc.pattern, x.pattern], body), this.expr(type, env, depth - 1), this.expr(container, env, depth - 1));
      } },
      { feature: "hof", weight: 1, build: () => {
        const element = this.showableType(env, 1);
        const acc = this.boundVariable("acc", type);
        const x = this.boundVariable("x", element);
        const body = this.expr(type, this.extend(env, acc.variable, x.variable), depth - 1);
        return call(type, "foldr", lambda(T.fnN([element, type], type), [x.pattern, acc.pattern], body), this.expr(type, env, depth - 1), this.expr(T.array(element), env, depth - 1));
      } },
      { feature: "lazy", weight: 1.5, build: () => call(type, "Lazy.force", this.expr(T.lazy(type), env, depth - 1)) },
      { feature: "containers", weight: 1, build: () => call(type, "fromMaybe", this.expr(type, env, depth - 1), call(T.maybe(type), "Array.index", this.expr(T.array(type), env, depth - 1), this.expr(T.Int, env, depth - 1))) },
      { feature: "containers", weight: 1, build: () => {
        const key = this.keyType(env, 1);
        return call(type, "fromMaybe", this.expr(type, env, depth - 1), call(T.maybe(type), "Map.lookup", this.expr(key, env, depth - 1), this.expr(T.map(key, type), env, depth - 1)));
      } },
      { feature: "records", weight: 1.5, build: () => {
        const name = this.rng.pick(FIELD_NAMES);
        const others = this.rng.shuffle(FIELD_NAMES.filter((f) => f !== name)).slice(0, this.rng.int(0, 2));
        const recordType = T.record([{ name, type }, ...others.map((o) => ({ name: o, type: this.showableType(env, 1) }))]);
        return { kind: "access", type, record: this.expr(recordType, env, depth - 1), field: name };
      } },
      { feature: "hof", weight: 1, build: () => {
        const f = this.expr(T.fn(type, type), env, depth - 1);
        return call(type, "applyN", f, literal(T.Int, String(this.rng.int(0, 5))), this.expr(type, env, depth - 1));
      } },
      { feature: "recursion", weight: 1, build: () => this.tailRecLoop(type, env, depth) },
      { feature: "recursion", weight: 1, build: () => this.fixLoop(type, env, depth) },
      { feature: "effects", weight: 0.5, build: () => env.inEffect ? null : call(type, "unsafePerformEffect", this.expr(T.effect(type), { ...env, inEffect: true }, depth - 1)) },
      { feature: "st", weight: 1, build: () => this.stRun(type, env, depth) },
      { feature: "hof", weight: 1, build: () => {
        const argType = this.showableType(env, 1);
        return apply(type, this.expr(T.fn(argType, type), env, depth - 1), this.expr(argType, env, depth - 1));
      } },
    ];
    return productions.map((p) => ({ ...p, weight: this.weight(p.feature, p.weight) }));
  }

  private caseExpression(type: Type, env: Environment, depth: number): Expr | null {
    const scrutineeType = this.scrutineeType(env, depth);
    const scrutinee = this.expr(scrutineeType, env, depth - 1);
    const alternatives: Alternative[] = [];
    const count = this.rng.int(1, 3);
    for (let i = 0; i < count; i++) {
      const generated = this.pattern(scrutineeType, 2, env, "c");
      if (generated.irrefutable && i < count - 1) continue;
      const bodyEnv = this.extend(env, ...generated.bindings);
      const guards: Alternative["guards"] = [];
      if (this.on("patterns") && this.rng.chance(0.3)) {
        guards.push({ cond: this.expr(T.Boolean, bodyEnv, depth - 2), body: this.expr(type, bodyEnv, depth - 1) });
      }
      alternatives.push({ patterns: [generated.pattern], guards, body: this.expr(type, bodyEnv, depth - 1) });
      if (generated.irrefutable && guards.length === 0) return { kind: "case", type, scrutinees: [scrutinee], alternatives };
    }
    const fallback = this.boundVariable("other", scrutineeType);
    const useWildcard = this.rng.chance(0.5);
    alternatives.push({ patterns: [useWildcard ? wildcard : fallback.pattern], guards: [], body: this.expr(type, useWildcard ? env : this.extend(env, fallback.variable), depth - 1) });
    return { kind: "case", type, scrutinees: [scrutinee], alternatives };
  }

  private letExpression(type: Type, env: Environment, depth: number): Expr {
    const bindings: Binding[] = [];
    let bodyEnv = env;
    const count = this.rng.int(1, 2);
    for (let i = 0; i < count; i++) {
      const name = this.fresh("let");
      if (this.on("hof") && this.rng.chance(0.3)) {
        const argType = this.showableType(env, 1);
        const resultType = this.showableType(env, 1);
        const param = this.boundVariable("y", argType);
        const body = this.expr(resultType, this.extend(bodyEnv, param.variable), depth - 1);
        bindings.push({ name, signature: null, equations: [{ patterns: [param.pattern], guards: [], body, where: [] }] });
        bodyEnv = this.extend(bodyEnv, { name, type: T.fn(argType, resultType) });
      } else {
        const valueType = this.showableType(env, 2);
        const value = this.expr(valueType, bodyEnv, depth - 1);
        bindings.push({ name, signature: this.rng.chance(0.3) ? { vars: [], constraints: [], type: valueType } : null, equations: [{ patterns: [], guards: [], body: value, where: [] }] });
        bodyEnv = this.extend(bodyEnv, { name, type: valueType });
      }
    }
    return { kind: "letIn", type, bindings, body: this.expr(type, bodyEnv, depth - 1) };
  }

  /** Calls a top-level function whose result type matches, instantiating its type variables. */
  private callUserFunction(type: Type, env: Environment, depth: number): Expr | null {
    const candidates = this.functions.filter((f) => this.matchResult(f.signature, type, env) !== null);
    if (candidates.length === 0) return null;
    const chosen = this.rng.pick(candidates);
    const bindings = this.matchResult(chosen.signature, type, env)!;
    const params: Type[] = [];
    let cursor = chosen.signature.type;
    while (cursor.tag === "Function") {
      params.push(substitute(cursor.from, bindings));
      cursor = cursor.to;
    }
    const args = params.map((param, index) =>
      index === 0 && chosen.boundedFirstArgument !== null
        ? literal(T.Int, String(this.rng.pick([0, 1, 2, 3, 5, chosen.boundedFirstArgument])))
        : this.expr(param, env, depth - 1),
    );
    return call(type, chosen.name, ...args);
  }

  private matchResult(signature: PolyType, type: Type, env: Environment): Map<string, Type> | null {
    let cursor = signature.type;
    while (cursor.tag === "Function") cursor = cursor.to;
    const bindings = new Map<string, Type>();
    if (!this.unify(cursor, type, bindings, signature.vars)) return null;
    for (const name of signature.vars) {
      if (!bindings.has(name)) {
        const constraints = signature.constraints.filter((c) => c.type.tag === "Var" && c.type.name === name).map((c) => c.className);
        const chosen = this.typeSatisfying(constraints, env);
        if (!chosen) return null;
        bindings.set(name, chosen);
      }
    }
    for (const constraint of signature.constraints) {
      const instantiated = substitute(constraint.type, bindings);
      if (!this.satisfies(constraint.className, instantiated, env)) return null;
    }
    return bindings;
  }

  private satisfies(className: string, type: Type, env: Environment): boolean {
    if (className === "Show" || className === "Eq" || className === "Ord") return hasClass(className, type, this.dataEnvironment, env.assumed);
    const user = this.classes.find((c) => c.declaration.name === className);
    return user ? this.userClassHas(user, type, env.assumed) : false;
  }

  private typeSatisfying(classNames: string[], env: Environment): Type | null {
    for (let attempt = 0; attempt < 20; attempt++) {
      const candidate = this.type(env, 1, { showable: true, allowData: true });
      if (classNames.every((className) => this.satisfies(className, candidate, env))) return candidate;
    }
    return null;
  }

  private unify(pattern: Type, type: Type, bindings: Map<string, Type>, vars: string[]): boolean {
    if (pattern.tag === "Var" && vars.includes(pattern.name)) {
      const bound = bindings.get(pattern.name);
      if (bound) return typeEquals(bound, type);
      bindings.set(pattern.name, type);
      return true;
    }
    if (pattern.tag !== type.tag) return false;
    switch (pattern.tag) {
      case "Maybe":
      case "Array":
      case "List":
      case "Set":
      case "Lazy":
      case "Effect":
      case "Ref":
        return this.unify(pattern.arg, (type as typeof pattern).arg, bindings, vars);
      case "Either":
        return this.unify(pattern.left, (type as typeof pattern).left, bindings, vars) && this.unify(pattern.right, (type as typeof pattern).right, bindings, vars);
      case "Tuple":
        return this.unify(pattern.first, (type as typeof pattern).first, bindings, vars) && this.unify(pattern.second, (type as typeof pattern).second, bindings, vars);
      case "Map":
        return this.unify(pattern.key, (type as typeof pattern).key, bindings, vars) && this.unify(pattern.value, (type as typeof pattern).value, bindings, vars);
      case "Function":
        return this.unify(pattern.from, (type as typeof pattern).from, bindings, vars) && this.unify(pattern.to, (type as typeof pattern).to, bindings, vars);
      case "Record": {
        const other = type as typeof pattern;
        if (pattern.fields.length !== other.fields.length) return false;
        return pattern.fields.every((field, index) => field.name === other.fields[index].name && this.unify(field.type, other.fields[index].type, bindings, vars));
      }
      case "Data": {
        const other = type as typeof pattern;
        if (pattern.name !== other.name) return false;
        return pattern.args.every((arg, index) => this.unify(arg, other.args[index], bindings, vars));
      }
      case "Var":
        return typeEquals(pattern, type);
      default:
        return true;
    }
  }

  private tailRecLoop(type: Type, env: Environment, depth: number): Expr | null {
    if (type.tag === "Var" || type.tag === "Function") return null;
    const stateType = T.record([{ name: "acc", type }, { name: "i", type: T.Int }]);
    const stepType = T.data("Step", [stateType, type]);
    const state = this.boundVariable("st", stateType);
    const limit = this.rng.pick([0, 1, 5, 100, 10000, 100000]);
    const accValue = variable(type, `${state.name}.acc`);
    const stepEnv = this.extend(env, state.variable, { name: `${state.name}.acc`, type }, { name: `${state.name}.i`, type: T.Int });
    const next = this.expr(type, stepEnv, depth - 1);
    const body: Expr = {
      kind: "ifThenElse",
      type: stepType,
      cond: binary(T.Boolean, ">=", variable(T.Int, `${state.name}.i`), literal(T.Int, String(limit))),
      thenBranch: call(stepType, "Done", accValue),
      elseBranch: call(stepType, "Loop", { kind: "record", type: stateType, fields: [{ name: "acc", value: next }, { name: "i", value: binary(T.Int, "+", variable(T.Int, `${state.name}.i`), literal(T.Int, "1")) }] }),
    };
    const initial: Expr = { kind: "record", type: stateType, fields: [{ name: "acc", value: this.expr(type, env, depth - 1) }, { name: "i", value: literal(T.Int, "0") }] };
    return call(type, "tailRec", lambda(T.fn(stateType, stepType), [state.pattern], body), initial);
  }

  private fixLoop(type: Type, env: Environment, depth: number): Expr | null {
    if (type.tag === "Var" || type.tag === "Function") return null;
    const self = this.fresh("self");
    const n = this.fresh("n");
    const rec = this.fresh("rec");
    const selfType = T.fn(T.Int, type);
    const loopEnv = this.extend(env, { name: n, type: T.Int }, { name: rec, type });
    const recursiveCall = apply(type, variable(selfType, self), binary(T.Int, "-", variable(T.Int, n), literal(T.Int, "1")));
    const recursive: Expr = {
      kind: "letIn",
      type,
      bindings: [{ name: rec, signature: null, equations: [{ patterns: [], guards: [], body: recursiveCall, where: [] }] }],
      body: this.expr(type, loopEnv, depth - 1),
    };
    const base = this.expr(type, this.extend(env, { name: n, type: T.Int }), depth - 1);
    const body: Expr = {
      kind: "ifThenElse",
      type,
      cond: binary(T.Boolean, "<=", variable(T.Int, n), literal(T.Int, "0")),
      thenBranch: base,
      elseBranch: recursive,
    };
    const start = this.rng.pick([0, 1, 3, 10, 500]);
    return apply(type, call(selfType, "CLazy.fix", lambda(T.fn(selfType, selfType), [varPattern(self, selfType), varPattern(n, T.Int)], body)), literal(T.Int, String(start)));
  }

  private stRun(type: Type, env: Environment, depth: number): Expr | null {
    if (type.tag === "Var" || type.tag === "Function" || env.inEffect) return null;
    const refName = this.fresh("ref");
    const stateType = T.ref(type);
    const statements: Statement[] = [
      { kind: "bind", pattern: varPattern(refName, stateType), expr: call(T.effect(stateType), "STRef.new", this.expr(type, env, depth - 1)) },
    ];
    const count = this.rng.int(1, 3);
    for (let i = 0; i < count; i++) {
      const current = this.boundVariable("cur", type);
      const next = this.expr(type, this.extend(env, current.variable), depth - 1);
      statements.push({ kind: "discard", expr: call(T.effect(type), "void", call(T.effect(type), "STRef.modify", lambda(T.fn(type, type), [current.pattern], next), variable(stateType, refName))) });
    }
    const block: Expr = { kind: "doBlock", type: T.effect(type), statements, result: call(T.effect(type), "STRef.read", variable(stateType, refName)) };
    return call(type, "ST.run", block);
  }

  // ---------------------------------------------------------------- primitives

  private intProductions(env: Environment, depth: number): Production[] {
    const int = T.Int;
    const sub = () => this.expr(int, env, depth - 1);
    const productions: Production[] = [
      { feature: "prims", weight: 3, build: () => this.intLiteral() },
      { feature: "prims", weight: 4, build: () => binary(int, this.rng.pick(["+", "-", "*"]), sub(), sub()) },
      { feature: "prims", weight: 3, build: () => call(int, this.rng.pick(["div", "mod"]), sub(), sub()) },
      { feature: "prims", weight: 1.5, build: () => call(int, this.rng.pick(["negate", "abs", "signum"]), sub()) },
      { feature: "prims", weight: 1, build: () => call(int, this.rng.pick(["min", "max"]), sub(), sub()) },
      { feature: "prims", weight: 0.7, build: () => call(int, "clamp", sub(), sub(), sub()) },
      { feature: "prims", weight: 2, build: () => call(int, this.rng.pick(["Int.floor", "Int.round", "Int.ceil", "Int.trunc"]), this.expr(T.Number, env, depth - 1)) },
      { feature: "prims", weight: 1, build: () => call(int, "Int.pow", sub(), sub()) },
      { feature: "prims", weight: 1, build: () => call(int, this.rng.pick(["Int.quot", "Int.rem"]), sub(), sub()) },
      { feature: "prims", weight: 2, build: () => call(int, this.rng.pick(["Bits.and", "Bits.or", "Bits.xor", "Bits.shl", "Bits.shr", "Bits.zshr"]), sub(), sub()) },
      { feature: "prims", weight: 0.7, build: () => call(int, "Bits.complement", sub()) },
      { feature: "prims", weight: 1, build: () => call(int, "fromMaybe", sub(), call(T.maybe(int), "Int.fromString", this.expr(T.String, env, depth - 1))) },
      { feature: "prims", weight: 1, build: () => call(int, "fromMaybe", sub(), call(T.maybe(int), "Int.fromNumber", this.expr(T.Number, env, depth - 1))) },
      { feature: "strings", weight: 2, build: () => call(int, this.rng.pick(["CU.length", "CP.length", "String.length"]), this.expr(T.String, env, depth - 1)) },
      { feature: "strings", weight: 1.5, build: () => call(int, "fromEnum", this.expr(T.Char, env, depth - 1)) },
      { feature: "strings", weight: 1, build: () => call(int, "Char.toCharCode", this.expr(T.Char, env, depth - 1)) },
      { feature: "containers", weight: 2, build: () => call(int, "Array.length", this.expr(T.array(this.showableType(env, 1)), env, depth - 1)) },
      { feature: "lists", weight: 1, build: () => call(int, "List.length", this.expr(T.list(this.showableType(env, 1)), env, depth - 1)) },
      { feature: "containers", weight: 1, build: () => {
        const key = this.keyType(env, 1);
        return call(int, "Map.size", this.expr(T.map(key, this.showableType(env, 1)), env, depth - 1));
      } },
      { feature: "containers", weight: 1, build: () => call(int, "Set.size", this.expr(T.set(this.keyType(env, 1)), env, depth - 1)) },
      { feature: "containers", weight: 2, build: () => call(int, this.rng.pick(["sum", "product"]), this.expr(T.array(int), env, depth - 1)) },
      { feature: "containers", weight: 1, build: () => call(int, "fromMaybe", sub(), call(T.maybe(int), this.rng.pick(["maximum", "minimum"]), this.expr(T.array(int), env, depth - 1))) },
      { feature: "containers", weight: 1, build: () => {
        const element = this.showableType(env, 1);
        if (!hasClass("Eq", element, this.dataEnvironment, env.assumed)) return null;
        return call(int, "fromMaybe", sub(), call(T.maybe(int), "Array.elemIndex", this.expr(element, env, depth - 1), this.expr(T.array(element), env, depth - 1)));
      } },
      { feature: "records", weight: 1.5, build: () => {
        const getter = this.rowFunctions.find((f) => f.mode === "get");
        if (!getter) return null;
        const extra = this.rng.shuffle(FIELD_NAMES.filter((f) => f !== getter.field)).slice(0, this.rng.int(0, 2));
        const recordType = T.record([{ name: getter.field, type: T.Int }, ...extra.map((name) => ({ name, type: this.showableType(env, 1) }))]);
        const bumper = this.rowFunctions.find((f) => f.mode === "bump")!;
        const record = this.rng.chance(0.5) ? call(recordType, bumper.name, this.expr(recordType, env, depth - 1)) : this.expr(recordType, env, depth - 1);
        return call(int, getter.name, record);
      } },
      { feature: "strings", weight: 1, build: () => call(int, "fromMaybe", sub(), call(T.maybe(int), this.rng.pick(["String.indexOf", "String.lastIndexOf", "CU.indexOf"]), call(T.Unit, "Pattern", this.expr(T.String, env, depth - 1)), this.expr(T.String, env, depth - 1))) },
      { feature: "classes", weight: 1, build: () => {
        const ord = this.showableType(env, 1);
        if (!hasClass("Ord", ord, this.dataEnvironment, env.assumed)) return null;
        return call(int, "fromEnum", call(T.Ordering, "compare", this.expr(ord, env, depth - 1), this.expr(ord, env, depth - 1)));
      } },
    ];
    return productions.map((p) => ({ ...p, weight: this.weight(p.feature, p.weight) }));
  }

  private numberProductions(env: Environment, depth: number): Production[] {
    const number = T.Number;
    const sub = () => this.expr(number, env, depth - 1);
    const productions: Production[] = [
      { feature: "prims", weight: 3, build: () => this.numberLiteral() },
      { feature: "prims", weight: 4, build: () => binary(number, this.rng.pick(["+", "-", "*", "/"]), sub(), sub()) },
      { feature: "prims", weight: 2, build: () => call(number, "Int.toNumber", this.expr(T.Int, env, depth - 1)) },
      { feature: "prims", weight: 2, build: () => call(number, this.rng.pick(["Number.abs", "Number.floor", "Number.ceil", "Number.round", "Number.trunc", "Number.sign", "negate"]), sub()) },
      { feature: "prims", weight: 1.5, build: () => call(number, this.rng.pick(["Number.pow", "Number.remainder", "Number.min", "Number.max", "min", "max"]), sub(), sub()) },
      { feature: "prims", weight: 1, build: () => call(number, "Number.sqrt", sub()) },
      { feature: "transcendental", weight: 1.5, build: () => call(number, this.rng.pick(["Number.exp", "Number.log", "Number.sin", "Number.cos", "Number.tan", "Number.atan", "Number.asin", "Number.acos"]), sub()) },
      { feature: "transcendental", weight: 1, build: () => call(number, "Number.atan2", sub(), sub()) },
      { feature: "prims", weight: 1, build: () => call(number, "fromMaybe", sub(), call(T.maybe(number), "Number.fromString", this.expr(T.String, env, depth - 1))) },
      { feature: "containers", weight: 1.5, build: () => call(number, this.rng.pick(["sum", "product"]), this.expr(T.array(number), env, depth - 1)) },
    ];
    return productions.map((p) => ({ ...p, weight: this.weight(p.feature, p.weight) }));
  }

  private booleanProductions(env: Environment, depth: number): Production[] {
    const boolean = T.Boolean;
    const sub = () => this.expr(boolean, env, depth - 1);
    const productions: Production[] = [
      { feature: "prims", weight: 2, build: () => literal(boolean, this.rng.pick(["true", "false"])) },
      { feature: "prims", weight: 5, build: () => {
        const operand = this.showableType(env, 2);
        const ordered = hasClass("Ord", operand, this.dataEnvironment, env.assumed);
        const equal = hasClass("Eq", operand, this.dataEnvironment, env.assumed);
        if (!equal) return null;
        const op = ordered ? this.rng.pick(["==", "/=", "<", "<=", ">", ">="]) : this.rng.pick(["==", "/="]);
        return binary(boolean, op, this.expr(operand, env, depth - 1), this.expr(operand, env, depth - 1));
      } },
      { feature: "prims", weight: 2, build: () => binary(boolean, this.rng.pick(["&&", "||"]), sub(), sub()) },
      { feature: "prims", weight: 1, build: () => call(boolean, "not", sub()) },
      { feature: "containers", weight: 1.5, build: () => call(boolean, this.rng.pick(["isJust", "isNothing"]), this.expr(T.maybe(this.showableType(env, 1)), env, depth - 1)) },
      { feature: "containers", weight: 1, build: () => call(boolean, this.rng.pick(["isLeft", "isRight"]), this.expr(T.either(this.showableType(env, 1), this.showableType(env, 1)), env, depth - 1)) },
      { feature: "containers", weight: 1.5, build: () => call(boolean, "Array.null", this.expr(T.array(this.showableType(env, 1)), env, depth - 1)) },
      { feature: "containers", weight: 1.5, build: () => {
        const element = this.showableType(env, 1);
        if (!hasClass("Eq", element, this.dataEnvironment, env.assumed)) return null;
        return call(boolean, this.rng.pick(["elem", "Array.elem", "Array.notElem"]), this.expr(element, env, depth - 1), this.expr(T.array(element), env, depth - 1));
      } },
      { feature: "hof", weight: 1.5, build: () => {
        const element = this.showableType(env, 1);
        return call(boolean, this.rng.pick(["Array.any", "Array.all", "any", "all"]), this.expr(T.fn(element, boolean), env, depth - 1), this.expr(T.array(element), env, depth - 1));
      } },
      { feature: "containers", weight: 1, build: () => {
        const key = this.keyType(env, 1);
        return call(boolean, "Map.member", this.expr(key, env, depth - 1), this.expr(T.map(key, this.showableType(env, 1)), env, depth - 1));
      } },
      { feature: "containers", weight: 1, build: () => {
        const key = this.keyType(env, 1);
        return call(boolean, "Set.member", this.expr(key, env, depth - 1), this.expr(T.set(key), env, depth - 1));
      } },
      { feature: "strings", weight: 1.5, build: () => call(boolean, "String.contains", call(T.Unit, "Pattern", this.expr(T.String, env, depth - 1)), this.expr(T.String, env, depth - 1)) },
      { feature: "strings", weight: 1, build: () => call(boolean, "String.null", this.expr(T.String, env, depth - 1)) },
      { feature: "prims", weight: 1, build: () => call(boolean, this.rng.pick(["Number.isNaN", "Number.isFinite"]), this.expr(T.Number, env, depth - 1)) },
      { feature: "prims", weight: 1, build: () => {
        const ordered = this.showableType(env, 1);
        if (!hasClass("Ord", ordered, this.dataEnvironment, env.assumed)) return null;
        return call(boolean, "between", this.expr(ordered, env, depth - 1), this.expr(ordered, env, depth - 1), this.expr(ordered, env, depth - 1));
      } },
      { feature: "prims", weight: 1, build: () => binary(boolean, this.rng.pick(["==", "/="]), this.expr(T.Ordering, env, depth - 1), this.expr(T.Ordering, env, depth - 1)) },
    ];
    return productions.map((p) => ({ ...p, weight: this.weight(p.feature, p.weight) }));
  }

  private charProductions(env: Environment, depth: number): Production[] {
    const char = T.Char;
    const sub = () => this.expr(char, env, depth - 1);
    const productions: Production[] = [
      { feature: "strings", weight: 3, build: () => this.charLiteral() },
      { feature: "strings", weight: 2, build: () => call(char, "fromMaybe", sub(), call(T.maybe(char), "toEnum", this.expr(T.Int, env, depth - 1))) },
      { feature: "strings", weight: 2, build: () => call(char, "fromMaybe", sub(), call(T.maybe(char), "CU.charAt", this.expr(T.Int, env, depth - 1), this.expr(T.String, env, depth - 1))) },
      { feature: "strings", weight: 1, build: () => call(char, "fromMaybe", sub(), call(T.maybe(char), "Char.fromCharCode", this.expr(T.Int, env, depth - 1))) },
      { feature: "strings", weight: 1, build: () => call(char, "fromMaybe", sub(), call(T.maybe(char), this.rng.pick(["succ", "pred"]), sub())) },
      { feature: "strings", weight: 1, build: () => call(char, "fromMaybe", sub(), call(T.maybe(char), "Array.head", call(T.array(char), "CU.toCharArray", this.expr(T.String, env, depth - 1)))) },
      { feature: "prims", weight: 1, build: () => call(char, this.rng.pick(["min", "max"]), sub(), sub()) },
    ];
    return productions.map((p) => ({ ...p, weight: this.weight(p.feature, p.weight) }));
  }

  private stringProductions(env: Environment, depth: number): Production[] {
    const string = T.String;
    const sub = () => this.expr(string, env, depth - 1);
    const int = () => this.expr(T.Int, env, depth - 1);
    const pattern = () => call(T.Unit, "Pattern", sub());
    const productions: Production[] = [
      { feature: "strings", weight: 3, build: () => this.stringLiteral() },
      { feature: "strings", weight: 4, build: () => binary(string, "<>", sub(), sub()) },
      { feature: "prims", weight: 5, build: () => call(string, "show", this.expr(this.showableType(env, 2), env, depth - 1)) },
      { feature: "strings", weight: 2, build: () => call(string, this.rng.pick(["CU.take", "CU.drop", "CP.take", "CP.drop", "String.take", "String.drop", "CU.takeRight", "CU.dropRight"]), int(), sub()) },
      { feature: "strings", weight: 1.5, build: () => call(string, "CU.singleton", this.expr(T.Char, env, depth - 1)) },
      { feature: "strings", weight: 1.5, build: () => call(string, "CU.fromCharArray", this.expr(T.array(T.Char), env, depth - 1)) },
      { feature: "strings", weight: 1, build: () => call(string, "CP.singleton", call(T.Unit, "CP.codePointFromChar", this.expr(T.Char, env, depth - 1))) },
      { feature: "strings", weight: 2, build: () => call(string, this.rng.pick(["String.toUpper", "String.toLower", "String.trim"]), sub()) },
      { feature: "strings", weight: 2, build: () => call(string, "String.joinWith", sub(), this.expr(T.array(string), env, depth - 1)) },
      { feature: "strings", weight: 2, build: () => call(string, this.rng.pick(["String.replace", "String.replaceAll"]), pattern(), call(T.Unit, "Replacement", sub()), sub()) },
      { feature: "strings", weight: 1.5, build: () => call(string, "Int.toStringAs", variable(T.Unit, this.rng.pick(["Int.hexadecimal", "Int.binary", "Int.decimal", "Int.octal", "Int.base36"])), int()) },
      { feature: "strings", weight: 1.5, build: () => call(string, "intercalate", sub(), this.expr(T.array(string), env, depth - 1)) },
      { feature: "strings", weight: 1, build: () => call(string, "CU.slice", int(), int(), sub()) },
      { feature: "strings", weight: 1, build: () => call(string, "power", sub(), literal(T.Int, String(this.rng.int(0, 5)))) },
      { feature: "strings", weight: 1, build: () => call(string, "CU.fromCharArray", call(T.array(T.Char), "Array.reverse", call(T.array(T.Char), "CU.toCharArray", sub()))) },
      { feature: "strings", weight: 1, build: () => call(string, "fromMaybe", sub(), call(T.maybe(string), "String.stripPrefix", pattern(), sub())) },
      { feature: "strings", weight: 1, build: () => call(string, "fromMaybe", sub(), call(T.maybe(string), "String.stripSuffix", pattern(), sub())) },
      { feature: "hof", weight: 2, build: () => {
        const element = this.showableType(env, 1);
        return call(string, "foldMap", this.expr(T.fn(element, string), env, depth - 1), this.expr(T.array(element), env, depth - 1));
      } },
      { feature: "classes", weight: 3, build: () => this.callUserClassMethod(env, depth) },
      { feature: "poly", weight: 2, build: () => this.callNest(env, depth) },
      { feature: "poly", weight: 2, build: () => this.callRankN(env, depth) },
      { feature: "poly", weight: 2, build: () => this.existsShow(env, depth) },
      { feature: "poly", weight: 2, build: () => this.variantMatch(env, depth) },
      { feature: "strings", weight: 1, build: () => call(string, "String.fromCodePointArray", call(T.array(T.Unit), "CP.toCodePointArray", sub())) },
    ];
    return productions.map((p) => ({ ...p, weight: this.weight(p.feature, p.weight) }));
  }

  private callUserClassMethod(env: Environment, depth: number): Expr | null {
    if (this.classes.length === 0) return null;
    const user = this.rng.pick(this.classes);
    for (let attempt = 0; attempt < 10; attempt++) {
      const candidate = this.type(env, 2, { showable: true, allowData: true });
      if (this.userClassHas(user, candidate, env.assumed)) {
        return call(T.String, `describe${user.declaration.name}`, this.expr(candidate, env, depth - 1));
      }
    }
    return null;
  }

  private callNest(env: Environment, depth: number): Expr | null {
    if (this.nestFunctions.length === 0) return null;
    const nest = this.rng.pick(this.nestFunctions);
    const inner = this.showableType(env, 1);
    return call(T.String, nest.name, literal(T.Int, String(this.rng.int(0, 4))), this.expr(inner, env, depth - 1));
  }

  private callRankN(env: Environment, depth: number): Expr | null {
    if (this.rankN.length === 0) return null;
    const entry = this.rng.pick(this.rankN);
    if (entry.kind === "identity") {
      const argument = this.rng.pick(["identity", "(\\x -> x)", "(\\x -> identity x)"]);
      return call(T.String, entry.name, variable(T.Unit, argument), this.expr(T.Int, env, depth - 1), this.expr(T.String, env, depth - 1));
    }
    const argument = this.rng.pick(["show", "(\\x -> show x <> \"!\")", "(\\x -> \"<\" <> show x <> \">\")"]);
    return call(T.String, entry.name, variable(T.Unit, argument), this.expr(T.Int, env, depth - 1), this.expr(T.Boolean, env, depth - 1));
  }

  private existsShow(env: Environment, depth: number): Expr | null {
    if (!this.hasRecursiveShowBox) return null;
    const inner = this.showableType(env, 2);
    const boxed = call(T.Unit, "ShowBox", variable(T.Unit, "show"), this.expr(inner, env, depth - 1));
    const existential = annotate(T.tvar("Exists ShowBox"), call(T.Unit, "mkExists", boxed));
    const unpack = lambda(T.Unit, [{ kind: "constructor", name: "ShowBox", args: [varPattern("f", T.Unit), varPattern("x", T.Unit)] }], apply(T.String, variable(T.Unit, "f"), variable(T.Unit, "x")));
    return call(T.String, "runExists", unpack, existential);
  }

  private variantMatch(env: Environment, depth: number): Expr | null {
    const labels = this.rng.shuffle(["alpha", "beta", "gamma"]).slice(0, this.rng.int(2, 3));
    const fieldTypes = labels.map(() => this.showableType(env, 1));
    const chosen = this.rng.int(0, labels.length - 1);
    const variantType = T.tvar(`Variant.Variant (${labels.map((label, i) => `${label} :: ${printType(fieldTypes[i])}`).join(", ")})`);
    const injected = annotate(variantType, call(T.Unit, "Variant.inj", variable(T.Unit, `(Proxy :: Proxy "${labels[chosen]}")`), this.expr(fieldTypes[chosen], env, depth - 1)));
    if (this.rng.chance(0.5)) {
      const handlers: Expr = {
        kind: "record",
        type: T.Unit,
        fields: labels.map((label, i) => ({
          name: label,
          value: lambda(T.Unit, [varPattern("v", fieldTypes[i])], binary(T.String, "<>", literal(T.String, `"${label}="`), call(T.String, "show", variable(fieldTypes[i], "v")))),
        })),
      };
      return call(T.String, "Variant.match", handlers, injected);
    }
    const handler = lambda(T.Unit, [varPattern("v", fieldTypes[chosen])], call(T.String, "show", variable(fieldTypes[chosen], "v")));
    const onCase = call(T.Unit, "Variant.on", variable(T.Unit, `(Proxy :: Proxy "${labels[chosen]}")`), handler);
    const matcher = binary(T.Unit, "#", call(T.Unit, "Variant.default", literal(T.String, '"default"')), onCase);
    return apply(T.String, matcher, injected);
  }

  // ---------------------------------------------------------------- containers

  private maybeProductions(type: Type, inner: Type, env: Environment, depth: number): Production[] {
    const sub = () => this.expr(type, env, depth - 1);
    const productions: Production[] = [
      { feature: "containers", weight: 2, build: () => annotate(type, variable(type, "Nothing")) },
      { feature: "containers", weight: 3, build: () => call(type, "Just", this.expr(inner, env, depth - 1)) },
      { feature: "containers", weight: 2, build: () => call(type, this.rng.pick(["Array.head", "Array.last"]), this.expr(T.array(inner), env, depth - 1)) },
      { feature: "containers", weight: 2, build: () => call(type, "Array.index", this.expr(T.array(inner), env, depth - 1), this.expr(T.Int, env, depth - 1)) },
      { feature: "containers", weight: 1.5, build: () => {
        const key = this.keyType(env, 1);
        return call(type, "Map.lookup", this.expr(key, env, depth - 1), this.expr(T.map(key, inner), env, depth - 1));
      } },
      { feature: "hof", weight: 2, build: () => {
        const source = this.showableType(env, 1);
        return call(type, "map", this.expr(T.fn(source, inner), env, depth - 1), this.expr(T.maybe(source), env, depth - 1));
      } },
      { feature: "hof", weight: 1.5, build: () => {
        const source = this.showableType(env, 1);
        const bound = this.boundVariable("b", source);
        return binary(type, ">>=", this.expr(T.maybe(source), env, depth - 1), lambda(T.fn(source, type), [bound.pattern], this.expr(type, this.extend(env, bound.variable), depth - 1)));
      } },
      { feature: "hof", weight: 1, build: () => call(type, "Array.find", this.expr(T.fn(inner, T.Boolean), env, depth - 1), this.expr(T.array(inner), env, depth - 1)) },
      { feature: "containers", weight: 1, build: () => call(type, "hush", this.expr(T.either(this.showableType(env, 1), inner), env, depth - 1)) },
      { feature: "containers", weight: 1, build: () => binary(type, "<|>", sub(), sub()) },
      { feature: "containers", weight: 1, build: () => {
        if (!hasClass("Semigroup", inner, this.dataEnvironment, env.assumed)) return null;
        return binary(type, "<>", sub(), sub());
      } },
    ];
    if (inner.tag === "Int") {
      productions.push({ feature: "prims", weight: 2, build: () => call(type, "Int.fromString", this.expr(T.String, env, depth - 1)) });
      productions.push({ feature: "strings", weight: 1, build: () => call(type, "String.indexOf", call(T.Unit, "Pattern", this.expr(T.String, env, depth - 1)), this.expr(T.String, env, depth - 1)) });
      productions.push({ feature: "containers", weight: 1, build: () => call(type, this.rng.pick(["maximum", "minimum"]), this.expr(T.array(T.Int), env, depth - 1)) });
      productions.push({ feature: "prims", weight: 1, build: () => call(type, "Int.fromNumber", this.expr(T.Number, env, depth - 1)) });
    }
    if (inner.tag === "Char") {
      productions.push({ feature: "strings", weight: 2, build: () => call(type, "CU.charAt", this.expr(T.Int, env, depth - 1), this.expr(T.String, env, depth - 1)) });
      productions.push({ feature: "strings", weight: 1, build: () => call(type, "toEnum", this.expr(T.Int, env, depth - 1)) });
    }
    if (inner.tag === "Number") {
      productions.push({ feature: "prims", weight: 2, build: () => call(type, "Number.fromString", this.expr(T.String, env, depth - 1)) });
    }
    if (inner.tag === "String") {
      productions.push({ feature: "strings", weight: 1, build: () => call(type, "String.stripPrefix", call(T.Unit, "Pattern", this.expr(T.String, env, depth - 1)), this.expr(T.String, env, depth - 1)) });
    }
    if (inner.tag === "Array") {
      productions.push({ feature: "hof", weight: 1.5, build: () => {
        const source = this.showableType(env, 1);
        return call(type, "traverse", this.expr(T.fn(source, T.maybe(inner.arg)), env, depth - 1), this.expr(T.array(source), env, depth - 1));
      } });
    }
    return productions.map((p) => ({ ...p, weight: this.weight(p.feature, p.weight) }));
  }

  private eitherProductions(type: Type, left: Type, right: Type, env: Environment, depth: number): Production[] {
    const productions: Production[] = [
      { feature: "containers", weight: 3, build: () => annotate(type, call(type, "Left", this.expr(left, env, depth - 1))) },
      { feature: "containers", weight: 3, build: () => annotate(type, call(type, "Right", this.expr(right, env, depth - 1))) },
      { feature: "containers", weight: 2, build: () => call(type, "note", this.expr(left, env, depth - 1), this.expr(T.maybe(right), env, depth - 1)) },
      { feature: "hof", weight: 1.5, build: () => {
        const source = this.showableType(env, 1);
        return call(type, "map", this.expr(T.fn(source, right), env, depth - 1), this.expr(T.either(left, source), env, depth - 1));
      } },
      { feature: "hof", weight: 1, build: () => {
        const source = this.showableType(env, 1);
        return call(type, "lmap", this.expr(T.fn(source, left), env, depth - 1), this.expr(T.either(source, right), env, depth - 1));
      } },
      { feature: "hof", weight: 1.5, build: () => {
        const source = this.showableType(env, 1);
        const bound = this.boundVariable("b", source);
        return binary(type, ">>=", this.expr(T.either(left, source), env, depth - 1), lambda(T.fn(source, type), [bound.pattern], this.expr(type, this.extend(env, bound.variable), depth - 1)));
      } },
    ];
    if (left.tag === "String" && this.on("exceptions") && !env.inEffect) {
      productions.push({ feature: "exceptions", weight: 2, build: () => {
        const action = this.expr(T.effect(right), { ...env, inEffect: true }, depth - 1);
        const tried = call(T.Unit, "Exception.try", action);
        return call(type, "unsafePerformEffect", call(T.Unit, "map", call(T.Unit, "lmap", variable(T.Unit, "Exception.message")), tried));
      } });
    }
    return productions.map((p) => ({ ...p, weight: this.weight(p.feature, p.weight) }));
  }

  private tupleProductions(type: Type, first: Type, second: Type, env: Environment, depth: number): Production[] {
    const productions: Production[] = [
      { feature: "containers", weight: 4, build: () => call(type, "Tuple", this.expr(first, env, depth - 1), this.expr(second, env, depth - 1)) },
      { feature: "containers", weight: 2, build: () => binary(type, "/\\", this.expr(first, env, depth - 1), this.expr(second, env, depth - 1)) },
      { feature: "containers", weight: 1.5, build: () => call(type, "swap", this.expr(T.tuple(second, first), env, depth - 1)) },
      { feature: "hof", weight: 1, build: () => {
        const source = this.showableType(env, 1);
        return call(type, "map", this.expr(T.fn(source, second), env, depth - 1), this.expr(T.tuple(first, source), env, depth - 1));
      } },
    ];
    if (first.tag === "Array" && second.tag === "Array") {
      productions.push({ feature: "containers", weight: 2, build: () => call(type, "Array.unzip", this.expr(T.array(T.tuple(first.arg, second.arg)), env, depth - 1)) });
    }
    return productions.map((p) => ({ ...p, weight: this.weight(p.feature, p.weight) }));
  }

  private arrayProductions(type: Type, element: Type, env: Environment, depth: number): Production[] {
    const sub = () => this.expr(type, env, depth - 1);
    const int = () => this.expr(T.Int, env, depth - 1);
    const predicate = () => this.expr(T.fn(element, T.Boolean), env, depth - 1);
    const ordered = hasClass("Ord", element, this.dataEnvironment, env.assumed);
    const equal = hasClass("Eq", element, this.dataEnvironment, env.assumed);
    const productions: Production[] = [
      { feature: "containers", weight: 3, build: () => {
        const count = this.rng.int(0, 4);
        const elements: Expr[] = [];
        for (let i = 0; i < count; i++) elements.push(this.expr(element, env, depth - 1));
        const literalArray: Expr = { kind: "array", type, elements };
        return count === 0 ? annotate(type, literalArray) : literalArray;
      } },
      { feature: "hof", weight: 3, build: () => {
        const source = this.showableType(env, 1);
        return call(type, "map", this.expr(T.fn(source, element), env, depth - 1), this.expr(T.array(source), env, depth - 1));
      } },
      { feature: "hof", weight: 2, build: () => call(type, "Array.filter", predicate(), sub()) },
      { feature: "containers", weight: 2, build: () => call(type, "Array.replicate", literal(T.Int, String(this.rng.int(0, 4))), this.expr(element, env, depth - 1)) },
      { feature: "containers", weight: 1.5, build: () => call(type, this.rng.pick(["Array.cons", "flip Array.snoc"]), this.expr(element, env, depth - 1), sub()) },
      { feature: "containers", weight: 2, build: () => binary(type, "<>", sub(), sub()) },
      { feature: "containers", weight: 1.5, build: () => call(type, this.rng.pick(["Array.take", "Array.drop", "Array.takeEnd", "Array.dropEnd"]), int(), sub()) },
      { feature: "containers", weight: 1.5, build: () => call(type, "Array.reverse", sub()) },
      { feature: "containers", weight: 1, build: () => call(type, "Array.slice", int(), int(), sub()) },
      { feature: "hof", weight: 1.5, build: () => {
        const left = this.showableType(env, 1);
        const right = this.showableType(env, 1);
        return call(type, "Array.zipWith", this.expr(T.fnN([left, right], element), env, depth - 1), this.expr(T.array(left), env, depth - 1), this.expr(T.array(right), env, depth - 1));
      } },
      { feature: "hof", weight: 1.5, build: () => {
        const source = this.showableType(env, 1);
        return call(type, "Array.concatMap", this.expr(T.fn(source, type), env, depth - 1), this.expr(T.array(source), env, depth - 1));
      } },
      { feature: "hof", weight: 1, build: () => {
        const source = this.showableType(env, 1);
        const bound = this.boundVariable("b", source);
        return binary(type, ">>=", this.expr(T.array(source), env, depth - 1), lambda(T.fn(source, type), [bound.pattern], this.expr(type, this.extend(env, bound.variable), depth - 1)));
      } },
      { feature: "containers", weight: 1.5, build: () => call(type, "Array.catMaybes", this.expr(T.array(T.maybe(element)), env, depth - 1)) },
      { feature: "hof", weight: 1, build: () => {
        const source = this.showableType(env, 1);
        return call(type, "Array.mapMaybe", this.expr(T.fn(source, T.maybe(element)), env, depth - 1), this.expr(T.array(source), env, depth - 1));
      } },
      { feature: "lists", weight: 1.5, build: () => call(type, "Array.fromFoldable", this.expr(T.list(element), env, depth - 1)) },
      { feature: "containers", weight: 1, build: () => call(type, "Array.singleton", this.expr(element, env, depth - 1)) },
      { feature: "hof", weight: 1, build: () => {
        const index = this.boundVariable("i", T.Int);
        const source = this.showableType(env, 1);
        const value = this.boundVariable("x", source);
        const body = this.expr(element, this.extend(env, index.variable, value.variable), depth - 1);
        return call(type, "Array.mapWithIndex", lambda(T.fnN([T.Int, source], element), [index.pattern, value.pattern], body), this.expr(T.array(source), env, depth - 1));
      } },
      { feature: "containers", weight: 1, build: () => call(type, "fromMaybe", sub(), call(T.maybe(type), this.rng.pick(["Array.updateAt", "Array.insertAt"]), int(), this.expr(element, env, depth - 1), sub())) },
      { feature: "containers", weight: 1, build: () => call(type, "fromMaybe", sub(), call(T.maybe(type), "Array.deleteAt", int(), sub())) },
      { feature: "hof", weight: 1, build: () => call(type, this.rng.pick(["Array.takeWhile", "Array.dropWhile"]), predicate(), sub()) },
      { feature: "hof", weight: 1, build: () => call(type, "Array.sortBy", this.expr(T.fnN([element, element], T.Ordering), env, depth - 1), sub()) },
      { feature: "hof", weight: 1, build: () => {
        const acc = this.boundVariable("acc", element);
        const x = this.boundVariable("x", element);
        return call(type, "Array.scanl", lambda(T.fnN([element, element], element), [acc.pattern, x.pattern], this.expr(element, this.extend(env, acc.variable, x.variable), depth - 1)), this.expr(element, env, depth - 1), sub());
      } },
      { feature: "st", weight: 1.5, build: () => this.stArrayRun(type, element, env, depth) },
    ];
    if (ordered) {
      productions.push({ feature: "containers", weight: 2, build: () => call(type, "Array.sort", sub()) });
      productions.push({ feature: "containers", weight: 1, build: () => call(type, "Array.fromFoldable", this.expr(T.set(element), env, depth - 1)) });
      productions.push({ feature: "containers", weight: 1, build: () => call(type, "Array.fromFoldable", call(T.Unit, "Map.keys", this.expr(T.map(element, this.showableType(env, 1)), env, depth - 1))) });
    }
    if (equal) {
      productions.push({ feature: "containers", weight: 1.5, build: () => call(type, ordered ? "Array.nub" : "Array.nubEq", sub()) });
      productions.push({ feature: "containers", weight: 1, build: () => call(type, this.rng.pick(["Array.union", "Array.intersect", "Array.difference"]), sub(), sub()) });
      productions.push({ feature: "containers", weight: 1, build: () => call(type, "Array.delete", this.expr(element, env, depth - 1), sub()) });
    }
    if (element.tag === "Int") {
      productions.push({ feature: "containers", weight: 3, build: () => call(type, "Array.range", call(T.Int, "clamp", literal(T.Int, "-5"), literal(T.Int, "20"), int()), call(T.Int, "clamp", literal(T.Int, "-5"), literal(T.Int, "20"), int())) });
      productions.push({ feature: "containers", weight: 1, build: () => call(type, "Array.range", literal(T.Int, String(this.rng.int(-3, 3))), literal(T.Int, String(this.rng.int(-3, 12)))) });
    }
    if (element.tag === "Char") {
      productions.push({ feature: "strings", weight: 3, build: () => call(type, "CU.toCharArray", this.expr(T.String, env, depth - 1)) });
    }
    if (element.tag === "String") {
      productions.push({ feature: "strings", weight: 3, build: () => call(type, "String.split", call(T.Unit, "Pattern", this.expr(T.String, env, depth - 1)), this.expr(T.String, env, depth - 1)) });
      productions.push({ feature: "hof", weight: 1.5, build: () => call(type, "map", variable(T.Unit, "show"), this.expr(T.array(this.showableType(env, 1)), env, depth - 1)) });
    }
    if (element.tag === "Tuple") {
      productions.push({ feature: "containers", weight: 2, build: () => call(type, "Array.zip", this.expr(T.array(element.first), env, depth - 1), this.expr(T.array(element.second), env, depth - 1)) });
      if (hasClass("Ord", element.first, this.dataEnvironment, env.assumed)) {
        productions.push({ feature: "containers", weight: 2, build: () => annotate(type, call(type, "Map.toUnfoldable", this.expr(T.map(element.first, element.second), env, depth - 1))) });
      }
    }
    if (element.tag === "Maybe") {
      productions.push({ feature: "hof", weight: 1, build: () => call(type, "map", variable(T.Unit, "Just"), this.expr(T.array(element.arg), env, depth - 1)) });
    }
    return productions.map((p) => ({ ...p, weight: this.weight(p.feature, p.weight) }));
  }

  private stArrayRun(type: Type, element: Type, env: Environment, depth: number): Expr | null {
    if (env.inEffect || element.tag === "Var") return null;
    const arrayName = this.fresh("arr");
    const statements: Statement[] = [
      { kind: "bind", pattern: varPattern(arrayName, T.Unit), expr: call(T.Unit, "STArray.thaw", this.expr(type, env, depth - 1)) },
    ];
    const count = this.rng.int(1, 3);
    for (let i = 0; i < count; i++) {
      const choice = this.rng.int(0, 2);
      if (choice === 0) statements.push({ kind: "discard", expr: call(T.Unit, "void", call(T.Unit, "STArray.push", this.expr(element, env, depth - 1), variable(T.Unit, arrayName))) });
      else if (choice === 1) statements.push({ kind: "discard", expr: call(T.Unit, "void", call(T.Unit, "STArray.poke", this.expr(T.Int, env, depth - 1), this.expr(element, env, depth - 1), variable(T.Unit, arrayName))) });
      else statements.push({ kind: "discard", expr: call(T.Unit, "void", call(T.Unit, "STArray.modify", this.expr(T.Int, env, depth - 1), this.expr(T.fn(element, element), env, depth - 1), variable(T.Unit, arrayName))) });
    }
    const block: Expr = { kind: "doBlock", type: T.Unit, statements, result: call(T.Unit, "pure", variable(T.Unit, arrayName)) };
    return call(type, "STArray.run", block);
  }

  private listProductions(type: Type, element: Type, env: Environment, depth: number): Production[] {
    const sub = () => this.expr(type, env, depth - 1);
    const productions: Production[] = [
      { feature: "containers", weight: 4, build: () => call(type, "List.fromFoldable", this.expr(T.array(element), env, depth - 1)) },
      { feature: "containers", weight: 2, build: () => annotate(type, variable(type, "List.Nil")) },
      { feature: "containers", weight: 3, build: () => call(type, "List.Cons", this.expr(element, env, depth - 1), sub()) },
      { feature: "hof", weight: 2, build: () => {
        const source = this.showableType(env, 1);
        return call(type, "map", this.expr(T.fn(source, element), env, depth - 1), this.expr(T.list(source), env, depth - 1));
      } },
      { feature: "hof", weight: 1.5, build: () => call(type, "List.filter", this.expr(T.fn(element, T.Boolean), env, depth - 1), sub()) },
      { feature: "containers", weight: 1.5, build: () => call(type, "List.reverse", sub()) },
      { feature: "containers", weight: 1.5, build: () => call(type, this.rng.pick(["List.take", "List.drop"]), this.expr(T.Int, env, depth - 1), sub()) },
      { feature: "containers", weight: 1.5, build: () => binary(type, "<>", sub(), sub()) },
      { feature: "containers", weight: 1, build: () => call(type, "List.concat", this.expr(T.list(type), env, depth - 1)) },
    ];
    if (hasClass("Ord", element, this.dataEnvironment, env.assumed)) {
      productions.push({ feature: "containers", weight: 1.5, build: () => call(type, "List.sort", sub()) });
    }
    if (element.tag === "Int") {
      productions.push({ feature: "containers", weight: 2, build: () => call(type, "List.range", call(T.Int, "clamp", literal(T.Int, "-5"), literal(T.Int, "20"), this.expr(T.Int, env, depth - 1)), call(T.Int, "clamp", literal(T.Int, "-5"), literal(T.Int, "20"), this.expr(T.Int, env, depth - 1))) });
    }
    return productions.map((p) => ({ ...p, weight: this.weight(p.feature, p.weight) }));
  }

  private mapProductions(type: Type, key: Type, value: Type, env: Environment, depth: number): Production[] {
    const sub = () => this.expr(type, env, depth - 1);
    const productions: Production[] = [
      { feature: "containers", weight: 4, build: () => call(type, "Map.fromFoldable", this.expr(T.array(T.tuple(key, value)), env, depth - 1)) },
      { feature: "containers", weight: 1.5, build: () => annotate(type, variable(type, "Map.empty")) },
      { feature: "containers", weight: 2, build: () => call(type, "Map.singleton", this.expr(key, env, depth - 1), this.expr(value, env, depth - 1)) },
      { feature: "containers", weight: 3, build: () => call(type, "Map.insert", this.expr(key, env, depth - 1), this.expr(value, env, depth - 1), sub()) },
      { feature: "containers", weight: 2, build: () => call(type, "Map.delete", this.expr(key, env, depth - 1), sub()) },
      { feature: "containers", weight: 2, build: () => call(type, this.rng.pick(["Map.union", "Map.intersection"]), sub(), sub()) },
      { feature: "hof", weight: 2, build: () => {
        const source = this.showableType(env, 1);
        return call(type, "map", this.expr(T.fn(source, value), env, depth - 1), this.expr(T.map(key, source), env, depth - 1));
      } },
      { feature: "hof", weight: 1.5, build: () => call(type, "Map.filter", this.expr(T.fn(value, T.Boolean), env, depth - 1), sub()) },
      { feature: "hof", weight: 1, build: () => call(type, "Map.alter", this.expr(T.fn(T.maybe(value), T.maybe(value)), env, depth - 1), this.expr(key, env, depth - 1), sub()) },
      { feature: "hof", weight: 1, build: () => call(type, "Map.fromFoldableWith", this.expr(T.fnN([value, value], value), env, depth - 1), this.expr(T.array(T.tuple(key, value)), env, depth - 1)) },
      { feature: "hof", weight: 1, build: () => call(type, "Map.filterKeys", this.expr(T.fn(key, T.Boolean), env, depth - 1), sub()) },
    ];
    return productions.map((p) => ({ ...p, weight: this.weight(p.feature, p.weight) }));
  }

  private setProductions(type: Type, element: Type, env: Environment, depth: number): Production[] {
    const sub = () => this.expr(type, env, depth - 1);
    const productions: Production[] = [
      { feature: "containers", weight: 4, build: () => call(type, "Set.fromFoldable", this.expr(T.array(element), env, depth - 1)) },
      { feature: "containers", weight: 1.5, build: () => annotate(type, variable(type, "Set.empty")) },
      { feature: "containers", weight: 2, build: () => call(type, "Set.singleton", this.expr(element, env, depth - 1)) },
      { feature: "containers", weight: 3, build: () => call(type, "Set.insert", this.expr(element, env, depth - 1), sub()) },
      { feature: "containers", weight: 2, build: () => call(type, "Set.delete", this.expr(element, env, depth - 1), sub()) },
      { feature: "containers", weight: 2, build: () => call(type, this.rng.pick(["Set.union", "Set.intersection", "Set.difference"]), sub(), sub()) },
      { feature: "hof", weight: 2, build: () => {
        const source = this.keyType(env, 1);
        return call(type, "Set.map", this.expr(T.fn(source, element), env, depth - 1), this.expr(T.set(source), env, depth - 1));
      } },
      { feature: "hof", weight: 1.5, build: () => call(type, "Set.filter", this.expr(T.fn(element, T.Boolean), env, depth - 1), sub()) },
    ];
    return productions.map((p) => ({ ...p, weight: this.weight(p.feature, p.weight) }));
  }

  private recordProductions(type: Type & { tag: "Record" }, env: Environment, depth: number): Production[] {
    const productions: Production[] = [
      { feature: "records", weight: 4, build: () => ({ kind: "record", type, fields: type.fields.map((field) => ({ name: field.name, value: this.expr(field.type, env, depth - 1) })) }) },
      { feature: "records", weight: 3, build: () => {
        const updated = this.rng.shuffle(type.fields).slice(0, this.rng.int(1, type.fields.length));
        return { kind: "update", type, record: this.expr(type, env, depth - 1), fields: updated.map((field) => ({ name: field.name, value: this.expr(field.type, env, depth - 1) })) };
      } },
      { feature: "records", weight: 1.5, build: () => {
        const bumper = this.rowFunctions.find((f) => f.mode === "bump");
        if (!bumper || !type.fields.some((field) => field.name === bumper.field && field.type.tag === "Int")) return null;
        return call(type, bumper.name, this.expr(type, env, depth - 1));
      } },
    ];
    return productions.map((p) => ({ ...p, weight: this.weight(p.feature, p.weight) }));
  }

  private functionProductions(type: Type, from: Type, to: Type, env: Environment, depth: number): Production[] {
    const productions: Production[] = [
      { feature: "hof", weight: 5, build: () => {
        const bound = this.boundVariable("arg", from);
        return lambda(type, [bound.pattern], this.expr(to, this.extend(env, bound.variable), depth - 1));
      } },
      { feature: "hof", weight: 1.5, build: () => call(type, "const", this.expr(to, env, depth - 1)) },
      { feature: "hof", weight: 1.5, build: () => {
        const middle = this.showableType(env, 1);
        const outer = this.expr(T.fn(middle, to), env, depth - 1);
        const inner = this.expr(T.fn(from, middle), env, depth - 1);
        return this.rng.chance(0.5) ? binary(type, "<<<", outer, inner) : binary(type, ">>>", inner, outer);
      } },
      { feature: "hof", weight: 2, build: () => {
        const candidates = this.functions.filter((f) => this.matchResult(f.signature, type, env) !== null && f.signature.vars.length === 0);
        if (candidates.length === 0) return null;
        return variable(type, this.rng.pick(candidates).name);
      } },
      { feature: "patterns", weight: 1.5, build: () => {
        const generated = this.pattern(from, 2, env, "q");
        if (!generated.irrefutable) return null;
        return lambda(type, [generated.pattern], this.expr(to, this.extend(env, ...generated.bindings), depth - 1));
      } },
    ];
    if (typeEquals(from, to)) {
      productions.push({ feature: "hof", weight: 1, build: () => variable(type, "identity") });
      if (from.tag === "Int") productions.push({ feature: "hof", weight: 2, build: () => ({ kind: "section", type, op: this.rng.pick(["+", "-", "*"]), operand: this.expr(T.Int, env, depth - 1), side: this.rng.pick(["left", "right"]) }) });
      if (from.tag === "String") productions.push({ feature: "hof", weight: 2, build: () => ({ kind: "section", type, op: "<>", operand: this.expr(T.String, env, depth - 1), side: this.rng.pick(["left", "right"]) }) });
      if (from.tag === "Number") productions.push({ feature: "hof", weight: 1, build: () => ({ kind: "section", type, op: this.rng.pick(["+", "*", "/"]), operand: this.expr(T.Number, env, depth - 1), side: "right" }) });
    }
    if (to.tag === "String" && hasClass("Show", from, this.dataEnvironment, env.assumed)) {
      productions.push({ feature: "hof", weight: 2, build: () => variable(type, "show") });
    }
    if (to.tag === "Maybe" && typeEquals(to.arg, from)) {
      productions.push({ feature: "hof", weight: 1.5, build: () => variable(type, "Just") });
    }
    if (to.tag === "Boolean" && from.tag === "Int") {
      productions.push({ feature: "hof", weight: 2, build: () => ({ kind: "section", type, op: this.rng.pick(["<", ">", "==", "/=", "<=", ">="]), operand: this.expr(T.Int, env, depth - 1), side: "right" }) });
    }
    if (to.tag === "Array" && typeEquals(to.arg, from)) {
      productions.push({ feature: "hof", weight: 1, build: () => variable(type, "Array.singleton") });
    }
    if (from.tag === "Tuple") {
      productions.push({ feature: "hof", weight: 1.5, build: () => call(type, "uncurry", this.expr(T.fnN([from.first, from.second], to), env, depth - 1)) });
    }
    return productions.map((p) => ({ ...p, weight: this.weight(p.feature, p.weight) }));
  }

  private dataProductions(type: Type & { tag: "Data" }, env: Environment, depth: number): Production[] {
    const info = this.dataEnvironment.get(type.name);
    if (!info) return [];
    const bindings = new Map(info.params.map((p, i) => [p, type.args[i]]));
    const productions: Production[] = [
      { feature: "adts", weight: 5, build: () => {
        const constructor = this.rng.pick(info.constructors);
        const args = constructor.fields.map((field) => this.expr(substitute(field, bindings), env, depth - 1));
        const applied = args.length === 0 ? variable(type, constructor.name) : call(type, constructor.name, ...args);
        return args.length === 0 || info.params.length > 0 ? annotate(type, applied) : applied;
      } },
    ];
    if (info.isNewtype) {
      productions.push({ feature: "adts", weight: 2, build: () => annotate(type, call(type, "wrap", this.expr(substitute(info.constructors[0].fields[0], bindings), env, depth - 1))) });
      productions.push({ feature: "adts", weight: 2, build: () => {
        const inner = substitute(info.constructors[0].fields[0], bindings);
        return annotate(type, call(type, "over", variable(T.Unit, info.name), this.expr(T.fn(inner, inner), env, depth - 1), this.expr(type, env, depth - 1)));
      } });
    }
    if (info.params.length === 1 && info.classes.size > 0 && this.declarations.some((d) => d.kind === "data" && d.name === info.name && d.derived.includes("Functor"))) {
      productions.push({ feature: "hof", weight: 2, build: () => {
        const source = this.showableType(env, 1);
        return call(type, "map", this.expr(T.fn(source, type.args[0]), env, depth - 1), this.expr(T.data(type.name, [source]), env, depth - 1));
      } });
    }
    return productions.map((p) => ({ ...p, weight: this.weight(p.feature, p.weight) }));
  }

  private lazyProductions(type: Type, inner: Type, env: Environment, depth: number): Production[] {
    const productions: Production[] = [
      { feature: "lazy", weight: 4, build: () => call(type, "Lazy.defer", lambda(T.fn(T.Unit, inner), [wildcard], this.expr(inner, env, depth - 1))) },
      { feature: "lazy", weight: 2, build: () => annotate(type, call(type, "pure", this.expr(inner, env, depth - 1))) },
      { feature: "lazy", weight: 2, build: () => {
        const source = this.showableType(env, 1);
        return call(type, "map", this.expr(T.fn(source, inner), env, depth - 1), this.expr(T.lazy(source), env, depth - 1));
      } },
      { feature: "lazy", weight: 1, build: () => {
        if (!hasClass("Semigroup", inner, this.dataEnvironment, env.assumed)) return null;
        return binary(type, "<>", this.expr(type, env, depth - 1), this.expr(type, env, depth - 1));
      } },
    ];
    return productions.map((p) => ({ ...p, weight: this.weight(p.feature, p.weight) }));
  }

  // ---------------------------------------------------------------- effects

  private effectProductions(type: Type, inner: Type, env: Environment, depth: number): Production[] {
    const effectEnv = { ...env, inEffect: true };
    const productions: Production[] = [
      { feature: "effects", weight: 4, build: () => call(type, "pure", this.expr(inner, env, depth - 1)) },
      { feature: "effects", weight: 3, build: () => {
        const refName = this.fresh("ref");
        const refType = T.ref(inner);
        const current = this.boundVariable("cur", inner);
        const statements: Statement[] = [
          { kind: "bind", pattern: varPattern(refName, refType), expr: call(T.effect(refType), "Ref.new", this.expr(inner, env, depth - 1)) },
          { kind: "discard", expr: call(T.effect(T.Unit), "Ref.modify_", lambda(T.fn(inner, inner), [current.pattern], this.expr(inner, this.extend(env, current.variable), depth - 1)), variable(refType, refName)) },
        ];
        return { kind: "doBlock", type, statements, result: call(type, "Ref.read", variable(refType, refName)) };
      } },
      { feature: "exceptions", weight: 2, build: () => {
        const message = this.expr(T.String, env, depth - 1);
        const handler = lambda(T.fn(T.Unit, type), [varPattern("err", T.Unit)], call(type, "pure", this.expr(inner, env, depth - 1)));
        const thrower = this.rng.chance(0.5) ? call(type, "Exception.throw", message) : call(type, "pure", this.expr(inner, env, depth - 1));
        return call(type, "Exception.catchException", handler, thrower);
      } },
      { feature: "effects", weight: 1, build: () => {
        const statements: Statement[] = [{ kind: "discard", expr: call(T.effect(T.Unit), "log", this.expr(T.String, env, depth - 1)) }];
        return { kind: "doBlock", type, statements, result: call(type, "pure", this.expr(inner, env, depth - 1)) };
      } },
    ];
    if (env.refs.some((r) => r.type.tag === "Ref" && typeEquals(r.type.arg, inner))) {
      productions.push({ feature: "effects", weight: 3, build: () => {
        const candidates = env.refs.filter((r) => r.type.tag === "Ref" && typeEquals(r.type.arg, inner));
        const chosen = this.rng.pick(candidates);
        if (this.rng.chance(0.5)) return call(type, "Ref.read", variable(chosen.type, chosen.name));
        const current = this.boundVariable("cur", inner);
        return call(type, "Ref.modify", lambda(T.fn(inner, inner), [current.pattern], this.expr(inner, this.extend(env, current.variable), depth - 1)), variable(chosen.type, chosen.name));
      } });
    }
    void effectEnv;
    return productions.map((p) => ({ ...p, weight: this.weight(p.feature, p.weight) }));
  }

  private effectStatements(env: Environment): Statement[] {
    const statements: Statement[] = [];
    const choice = this.rng.int(0, 4);
    if (choice === 0) {
      const inner = this.showableType(env, 1);
      const refName = this.fresh("ref");
      const refType = T.ref(inner);
      statements.push({ kind: "bind", pattern: varPattern(refName, refType), expr: call(T.effect(refType), "Ref.new", this.expr(inner, env, this.options.depth - 1)) });
      env.refs.push({ name: refName, type: refType });
      const current = this.boundVariable("cur", inner);
      statements.push({ kind: "discard", expr: call(T.effect(T.Unit), "Ref.modify_", lambda(T.fn(inner, inner), [current.pattern], this.expr(inner, this.extend(env, current.variable), this.options.depth - 1)), variable(refType, refName)) });
      const valueName = this.fresh("val");
      statements.push({ kind: "bind", pattern: varPattern(valueName, inner), expr: call(T.effect(inner), "Ref.read", variable(refType, refName)) });
      env.variables.push({ name: valueName, type: inner });
      statements.push({ kind: "discard", expr: call(T.effect(T.Unit), "log", call(T.String, "show", variable(inner, valueName))) });
    } else if (choice === 1) {
      const inner = this.showableType(env, 2);
      const valueName = this.fresh("val");
      statements.push({ kind: "bind", pattern: varPattern(valueName, inner), expr: this.expr(T.effect(inner), env, this.options.depth) });
      env.variables.push({ name: valueName, type: inner });
      statements.push({ kind: "discard", expr: call(T.effect(T.Unit), "log", call(T.String, "show", variable(inner, valueName))) });
    } else if (choice === 2) {
      const element = this.showableType(env, 1);
      const bound = this.boundVariable("item", element);
      const body = call(T.effect(T.Unit), "log", call(T.String, "show", this.expr(this.showableType(env, 1), this.extend(env, bound.variable), this.options.depth - 1)));
      statements.push({ kind: "discard", expr: call(T.effect(T.Unit), "for_", this.expr(T.array(element), env, this.options.depth - 1), lambda(T.fn(element, T.effect(T.Unit)), [bound.pattern], body)) });
    } else if (choice === 3) {
      const index = this.boundVariable("i", T.Int);
      const body = call(T.effect(T.Unit), "log", call(T.String, "show", this.expr(this.showableType(env, 1), this.extend(env, index.variable), this.options.depth - 1)));
      statements.push({ kind: "discard", expr: call(T.effect(T.Unit), "forE", literal(T.Int, String(this.rng.int(-1, 2))), literal(T.Int, String(this.rng.int(0, 5))), lambda(T.fn(T.Int, T.effect(T.Unit)), [index.pattern], body)) });
    } else {
      const inner = this.showableType(env, 1);
      const bindings: Binding[] = [];
      const name = this.fresh("local");
      bindings.push({ name, signature: null, equations: [{ patterns: [], guards: [], body: this.expr(inner, env, this.options.depth - 1), where: [] }] });
      statements.push({ kind: "let", bindings });
      env.variables.push({ name, type: inner });
      statements.push({ kind: "discard", expr: call(T.effect(T.Unit), this.rng.pick(["when", "unless"]), this.expr(T.Boolean, env, 2), call(T.effect(T.Unit), "log", call(T.String, "show", variable(inner, name)))) });
    }
    return statements;
  }

  private exceptionStatement(env: Environment): Statement {
    const inner = this.showableType(env, 1);
    const choice = this.rng.int(0, 2);
    if (choice === 0) {
      const action = this.rng.chance(0.6)
        ? annotate(T.effect(inner), call(T.effect(inner), "Exception.throw", this.expr(T.String, env, 2)))
        : annotate(T.effect(inner), this.expr(T.effect(inner), env, 2));
      const result = this.boundVariable("res", T.Unit);
      const body: Expr = {
        kind: "case",
        type: T.effect(T.Unit),
        scrutinees: [variable(T.Unit, result.name)],
        alternatives: [
          { patterns: [{ kind: "constructor", name: "Left", args: [varPattern("err", T.Unit)] }], guards: [], body: call(T.effect(T.Unit), "log", binary(T.String, "<>", literal(T.String, '"caught: "'), call(T.String, "Exception.message", variable(T.Unit, "err")))) },
          { patterns: [{ kind: "constructor", name: "Right", args: [varPattern("ok", inner)] }], guards: [], body: call(T.effect(T.Unit), "log", call(T.String, "show", variable(inner, "ok"))) },
        ],
      };
      return { kind: "discard", expr: { kind: "doBlock", type: T.effect(T.Unit), statements: [{ kind: "bind", pattern: result.pattern, expr: call(T.Unit, "Exception.try", action) }], result: body } };
    }
    if (choice === 1) {
      const handler = lambda(T.Unit, [varPattern("err", T.Unit)], call(T.effect(T.Unit), "log", binary(T.String, "<>", literal(T.String, '"handled: "'), call(T.String, "Exception.message", variable(T.Unit, "err")))));
      const action = this.rng.chance(0.6)
        ? { kind: "doBlock" as const, type: T.effect(T.Unit), statements: [{ kind: "discard" as const, expr: call(T.effect(T.Unit), "log", this.expr(T.String, env, 2)) }], result: call(T.effect(T.Unit), "Exception.throwException", call(T.Unit, "Exception.error", this.expr(T.String, env, 2))) }
        : call(T.effect(T.Unit), "log", this.expr(T.String, env, 2));
      return { kind: "discard", expr: call(T.effect(T.Unit), "Exception.catchException", handler, action) };
    }
    const crash = this.rng.chance(0.5)
      ? call(inner, "unsafeCrashWith", this.expr(T.String, env, 1))
      : call(inner, "unsafePartial", call(inner, "fromJust", annotate(T.maybe(inner), variable(T.Unit, "Nothing"))));
    const guarded: Expr = { kind: "ifThenElse", type: inner, cond: this.expr(T.Boolean, env, 2), thenBranch: crash, elseBranch: this.expr(inner, env, 2) };
    const result = this.boundVariable("res", T.Unit);
    const action = call(T.Unit, "Exception.try", call(T.effect(inner), "pure", guarded));
    const body = call(T.effect(T.Unit), "log", call(T.String, "either", lambda(T.Unit, [varPattern("err", T.Unit)], binary(T.String, "<>", literal(T.String, '"crashed: "'), call(T.String, "Exception.message", variable(T.Unit, "err")))), variable(T.Unit, "show"), variable(T.Unit, result.name)));
    return { kind: "discard", expr: { kind: "doBlock", type: T.effect(T.Unit), statements: [{ kind: "bind", pattern: result.pattern, expr: action }], result: body } };
  }

  private affStatement(env: Environment): Statement {
    const inner = this.showableType(env, 1);
    const statements: Statement[] = [];
    const log = (expr: Expr) => call(T.Unit, "liftEffect", call(T.effect(T.Unit), "log", expr));
    statements.push({ kind: "discard", expr: log(literal(T.String, '"aff start"')) });
    const choice = this.rng.int(0, 3);
    if (choice === 0) {
      statements.push({ kind: "discard", expr: call(T.Unit, "Aff.delay", call(T.Unit, "Aff.Milliseconds", literal(T.Number, "1.0"))) });
      const results = this.boundVariable("results", T.array(inner));
      const item = this.boundVariable("item", T.Int);
      const body: Expr = { kind: "doBlock", type: T.Unit, statements: [{ kind: "discard", expr: call(T.Unit, "Aff.delay", call(T.Unit, "Aff.Milliseconds", call(T.Number, "Int.toNumber", variable(T.Int, item.name)))) }], result: call(T.Unit, "pure", this.expr(inner, this.extend(env, item.variable), 2)) };
      statements.push({ kind: "bind", pattern: results.pattern, expr: call(T.Unit, "parTraverse", lambda(T.Unit, [item.pattern], body), { kind: "array", type: T.array(T.Int), elements: [literal(T.Int, "3"), literal(T.Int, "1"), literal(T.Int, "2")] }) });
      statements.push({ kind: "discard", expr: log(call(T.String, "show", variable(T.array(inner), results.name))) });
    } else if (choice === 1) {
      const result = this.boundVariable("res", inner);
      const acquire = { kind: "doBlock" as const, type: T.Unit, statements: [{ kind: "discard" as const, expr: log(literal(T.String, '"acquire"')) }], result: call(T.Unit, "pure", this.expr(inner, env, 2)) };
      const release = lambda(T.Unit, [wildcard], log(literal(T.String, '"release"')));
      const resource = this.boundVariable("resource", inner);
      const use = lambda(T.Unit, [resource.pattern], call(T.Unit, "pure", this.expr(inner, this.extend(env, resource.variable), 2)));
      statements.push({ kind: "bind", pattern: result.pattern, expr: call(T.Unit, "Aff.bracket", acquire, release, use) });
      statements.push({ kind: "discard", expr: log(call(T.String, "show", variable(inner, result.name))) });
    } else if (choice === 2) {
      const fiber = this.boundVariable("fiber", T.Unit);
      const forked = { kind: "doBlock" as const, type: T.Unit, statements: [{ kind: "discard" as const, expr: call(T.Unit, "Aff.delay", call(T.Unit, "Aff.Milliseconds", literal(T.Number, "2000.0"))) }], result: log(literal(T.String, '"never printed"')) };
      statements.push({ kind: "bind", pattern: fiber.pattern, expr: call(T.Unit, "Aff.forkAff", forked) });
      statements.push({ kind: "discard", expr: call(T.Unit, "Aff.killFiber", call(T.Unit, "Aff.error", literal(T.String, '"killed"')), variable(T.Unit, fiber.name)) });
      const joined = this.boundVariable("joined", T.Unit);
      statements.push({ kind: "bind", pattern: joined.pattern, expr: call(T.Unit, "Aff.forkAff", call(T.Unit, "pure", this.expr(inner, env, 2))) });
      const value = this.boundVariable("value", inner);
      statements.push({ kind: "bind", pattern: value.pattern, expr: call(T.Unit, "Aff.joinFiber", variable(T.Unit, joined.name)) });
      statements.push({ kind: "discard", expr: log(call(T.String, "show", variable(inner, value.name))) });
    } else {
      const result = this.boundVariable("res", T.Unit);
      const failing = this.rng.chance(0.6)
        ? call(T.Unit, "Aff.throwError", call(T.Unit, "Aff.error", this.expr(T.String, env, 2)))
        : call(T.Unit, "pure", this.expr(inner, env, 2));
      statements.push({ kind: "bind", pattern: result.pattern, expr: call(T.Unit, "Aff.try", annotate(T.tvar(`Aff.Aff ${printTypeArgument(inner)}`), failing)) });
      const shown = call(T.String, "either", lambda(T.Unit, [varPattern("err", T.Unit)], binary(T.String, "<>", literal(T.String, '"aff error: "'), call(T.String, "Exception.message", variable(T.Unit, "err")))), variable(T.Unit, "show"), variable(T.Unit, result.name));
      statements.push({ kind: "discard", expr: log(shown) });
    }
    statements.push({ kind: "discard", expr: log(literal(T.String, '"aff end"')) });
    const block: Expr = { kind: "doBlock", type: T.Unit, statements: statements.slice(0, -1), result: statements[statements.length - 1].kind === "discard" ? (statements[statements.length - 1] as { expr: Expr }).expr : literal(T.Unit, "pure unit") };
    return { kind: "discard", expr: call(T.effect(T.Unit), "Aff.launchAff_", block) };
  }

  // ---------------------------------------------------------------- patterns

  /** A pattern for a type, with the variables it binds; `irrefutable` says it matches everything. */
  private pattern(type: Type, depth: number, env: Environment, prefix: string): { pattern: Pattern; bindings: Variable[]; irrefutable: boolean } {
    const bind = (): { pattern: Pattern; bindings: Variable[]; irrefutable: boolean } => {
      const name = this.fresh(prefix);
      return { pattern: varPattern(name, type), bindings: [{ name, type }], irrefutable: true };
    };
    if (depth <= 0 || this.rng.chance(0.2)) return this.rng.chance(0.2) ? { pattern: wildcard, bindings: [], irrefutable: true } : bind();
    const sub = (t: Type) => this.pattern(t, depth - 1, env, prefix);
    const combine = (name: string, parts: { pattern: Pattern; bindings: Variable[]; irrefutable: boolean }[], refutable: boolean) => ({
      pattern: { kind: "constructor" as const, name: QUALIFIED_CONSTRUCTORS[name] ?? name, args: parts.map((p) => p.pattern) },
      bindings: parts.flatMap((p) => p.bindings),
      irrefutable: !refutable && parts.every((p) => p.irrefutable),
    });
    const maybeNamed = (result: { pattern: Pattern; bindings: Variable[]; irrefutable: boolean }) => {
      if (!this.rng.chance(0.15) || result.pattern.kind === "variable" || result.pattern.kind === "wildcard") return result;
      const name = this.fresh(prefix);
      return { pattern: { kind: "named" as const, name, type, pattern: result.pattern }, bindings: [...result.bindings, { name, type }], irrefutable: result.irrefutable };
    };
    switch (type.tag) {
      case "Boolean":
        return { pattern: { kind: "literal", text: this.rng.pick(["true", "false"]) }, bindings: [], irrefutable: false };
      case "Int":
        return { pattern: { kind: "literal", text: String(this.rng.pick([0, 1, 2, -1, 42, 7])) }, bindings: [], irrefutable: false };
      case "String":
        return { pattern: { kind: "literal", text: this.rng.pick(['""', '"a"', '"abc"', '"\\x1F600"']) }, bindings: [], irrefutable: false };
      case "Char":
        return { pattern: { kind: "literal", text: this.rng.pick(["'a'", "'x'", "'\\n'", "'0'"]) }, bindings: [], irrefutable: false };
      case "Maybe":
        return maybeNamed(this.rng.chance(0.35) ? { pattern: { kind: "constructor", name: "Nothing", args: [] }, bindings: [], irrefutable: false } : combine("Just", [sub(type.arg)], true));
      case "Either":
        return maybeNamed(this.rng.chance(0.5) ? combine("Left", [sub(type.left)], true) : combine("Right", [sub(type.right)], true));
      case "Tuple":
        return maybeNamed(combine("Tuple", [sub(type.first), sub(type.second)], false));
      case "Array": {
        const count = this.rng.int(0, 3);
        const parts = Array.from({ length: count }, () => sub(type.arg));
        return maybeNamed({ pattern: { kind: "array", elements: parts.map((p) => p.pattern) }, bindings: parts.flatMap((p) => p.bindings), irrefutable: false });
      }
      case "List":
        return maybeNamed(this.rng.chance(0.4) ? { pattern: { kind: "constructor", name: "List.Nil", args: [] }, bindings: [], irrefutable: false } : combine("Cons", [sub(type.arg), sub(type)], true));
      case "Record": {
        const chosen = this.rng.shuffle(type.fields).slice(0, this.rng.int(1, type.fields.length));
        const parts = chosen.map((field) => ({ field, generated: sub(field.type) }));
        return {
          pattern: { kind: "record", fields: parts.map((p) => ({ name: p.field.name, pattern: p.generated.pattern })) },
          bindings: parts.flatMap((p) => p.generated.bindings),
          irrefutable: parts.every((p) => p.generated.irrefutable),
        };
      }
      case "Data": {
        const info = this.dataEnvironment.get(type.name);
        if (!info) return bind();
        const constructor = this.rng.pick(info.constructors);
        const bindings = new Map(info.params.map((p, i) => [p, type.args[i]]));
        const parts = constructor.fields.map((field) => sub(substitute(field, bindings)));
        return maybeNamed(combine(constructor.name, parts, info.constructors.length > 1));
      }
      default:
        return bind();
    }
  }
}

/** Whether a value of the type can grow with every recursive step, which bounds recursion depths. */
const growable = (type: Type): boolean => !["Int", "Number", "Boolean", "Char", "Unit", "Ordering"].includes(type.tag);

/** Whether deriving Functor over `param` is possible: the parameter only appears in covariant last positions. */
const functorSafe = (type: Type, param: string, self: string): boolean => {
  const mentions = (t: Type) => T.freeVars(t).has(param);
  if (!mentions(type)) return true;
  switch (type.tag) {
    case "Var":
      return true;
    case "Maybe":
    case "Array":
    case "List":
    case "Lazy":
      return functorSafe(type.arg, param, self);
    case "Tuple":
      return !mentions(type.first) && functorSafe(type.second, param, self);
    case "Either":
      return !mentions(type.left) && functorSafe(type.right, param, self);
    case "Map":
      return !mentions(type.key) && functorSafe(type.value, param, self);
    case "Record":
      return type.fields.every((field) => functorSafe(field.type, param, self));
    case "Function":
      return !mentions(type.from) && functorSafe(type.to, param, self);
    case "Data":
      return type.name === self && type.args.every((arg) => arg.tag === "Var" && arg.name === param);
    default:
      return false;
  }
};

const printTypeArgument = (type: Type): string => {
  const text = printType(type);
  const atomic = ["Int", "Number", "Boolean", "Char", "String", "Unit", "Ordering", "Record", "Var"].includes(type.tag) || (type.tag === "Data" && type.args.length === 0);
  return atomic ? text : `(${text})`;
};

export const generateProgram = (seed: number, moduleName: string, options: GeneratorOptions): Program =>
  new Generator(seed, options).generate(moduleName);

export const parseFeatures = (text: string | undefined): Record<Feature, number> => {
  const weights = defaultWeights();
  if (!text) return weights;
  const entries = text.split(",").map((part) => part.trim()).filter(Boolean);
  const explicitOnly = entries.length > 0 && !entries.some((entry) => entry.startsWith("+") || entry.startsWith("-") || entry.includes("="));
  if (explicitOnly) for (const feature of FEATURES) weights[feature] = 0;
  for (const entry of entries) {
    const assignment = /^([+-]?)(\w+)(?:=([\d.]+))?$/.exec(entry);
    if (!assignment) throw new Error(`cannot parse feature ${entry}`);
    const [, sign, name, value] = assignment;
    if (!FEATURES.includes(name as Feature)) throw new Error(`unknown feature ${name}; known: ${FEATURES.join(", ")}`);
    weights[name as Feature] = sign === "-" ? 0 : value !== undefined ? Number(value) : 1;
  }
  return weights;
};
