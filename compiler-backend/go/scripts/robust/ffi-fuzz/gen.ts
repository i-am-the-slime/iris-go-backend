// Generates the FFI fuzz programs: PureScript modules that call the library functions whose
// foreigns go-support implements, on adversarial and seeded random inputs, one output line per
// call. Every case is also written to cases.json with readable inputs, so that the comparison can
// show the minimal input behind a divergence.
//
//   bun gen.ts <src-dir> <cases.json> [seed] [random-cases-per-function]

import { mkdirSync, writeFileSync } from "node:fs";
import { join } from "node:path";

const [srcDir, casesFile, seedArg, randomArg] = process.argv.slice(2);
const seed = Number(seedArg ?? 1);
const randomPerFunction = Number(randomArg ?? 24);
const chunkSize = Number(process.env.FUZZ_CHUNK ?? 1200);

// ---------------------------------------------------------------- deterministic random
let state = seed >>> 0;
const random = () => {
  state = (state + 0x6d2b79f5) >>> 0;
  let t = state;
  t = Math.imul(t ^ (t >>> 15), t | 1);
  t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
  return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
};
const pick = <T>(xs: readonly T[]): T => xs[Math.floor(random() * xs.length)];
const int = (lo: number, hi: number) => lo + Math.floor(random() * (hi - lo + 1));

// ---------------------------------------------------------------- values and their literals
// A value is either literal data or a PureScript expression (for huge or computed inputs).
type Value = { ps: string; show: string; lone?: boolean };

const hasLoneSurrogate = (text: string) => {
  for (let i = 0; i < text.length; i++) {
    const unit = text.charCodeAt(i);
    if (unit >= 0xd800 && unit <= 0xdbff) {
      const next = text.charCodeAt(i + 1);
      if (next >= 0xdc00 && next <= 0xdfff) i++;
      else return true;
    } else if (unit >= 0xdc00 && unit <= 0xdfff) return true;
  }
  return false;
};

const escapeUnits = (text: string) =>
  Array.from({ length: text.length }, (_, i) => {
    const unit = text.charCodeAt(i);
    return unit >= 0x20 && unit < 0x7f && unit !== 0x5c && unit !== 0x22
      ? text[i]
      : "\\u" + unit.toString(16).padStart(4, "0");
  }).join("");

// purs writes a literal holding a lone surrogate into CoreFn as an array of code units, which
// purs-backend-es cannot decode, so such strings are built at run time from their code units.
const pursString = (text: string) => {
  if (hasLoneSurrogate(text)) {
    const units = Array.from({ length: text.length }, (_, i) => `R.ch ${text.charCodeAt(i)}`);
    return `(CU.fromCharArray [${units.join(", ")}])`;
  }
  let out = '"';
  for (const ch of text) {
    const code = ch.codePointAt(0)!;
    if (ch.length === 1 && code >= 0x20 && code < 0x7f && ch !== '"' && ch !== "\\") out += ch;
    else if (ch.length === 2) out += "\\x" + code.toString(16).padStart(6, "0");
    else {
      // A lone surrogate is one code unit; `for of` yields it alone.
      out += "\\x" + code.toString(16).padStart(6, "0");
    }
  }
  return out + '"';
};

const S = (text: string): Value => ({
  ps: pursString(text),
  show: '"' + escapeUnits(text) + '"',
  lone: hasLoneSurrogate(text),
});
const SExpr = (ps: string, show: string, lone = false): Value => ({ ps: `(${ps})`, show, lone });

const I = (n: number): Value => {
  if (n === -2147483648) return { ps: "(bottom :: Int)", show: String(n) };
  return { ps: n < 0 ? `(${n})` : String(n), show: String(n) };
};

const pursNumber = (x: number): string => {
  if (Number.isNaN(x)) return "nan";
  if (x === Infinity) return "infinity";
  if (x === -Infinity) return "(-infinity)";
  // purs-backend-es folds the literal `-0.0` to `0.0`, so -0 is computed at run time.
  if (Object.is(x, -0)) return "(negate (Number.abs 0.0))";
  const negative = x < 0;
  const [mantissa, exponent] = Math.abs(x).toExponential().split("e");
  const body = (mantissa.includes(".") ? mantissa : mantissa + ".0") + "e" + Number(exponent);
  return negative ? `(-${body})` : body;
};
const N = (x: number): Value => ({ ps: pursNumber(x), show: Object.is(x, -0) ? "-0" : String(x) });

const C = (unit: number): Value => ({
  ps: `(R.ch ${unit})`,
  show: "'\\u" + unit.toString(16).padStart(4, "0") + "'",
  lone: unit >= 0xd800 && unit <= 0xdfff,
});

const arrayOf = (values: Value[], element: string): Value => ({
  ps: "([" + values.map((v) => v.ps).join(", ") + "] :: Array " + element + ")",
  show: "[" + values.map((v) => v.show).join(",") + "]",
  lone: values.some((v) => v.lone),
});

// ---------------------------------------------------------------- input pools
const alphabet = [
  "a", "b", "z", "A", "Z", "0", "9", " ", "\t", "\n", "\r", "\0", ",", ".", "$", "&", "'", "`",
  "\\", '"', "*", "(", ")", "[", "-", "^", "|", "?", "+",
  "é", "ß", "İ", "ı", "Σ", "σ", "ς", "ǅ", "ﬀ", "ŉ", "Ω", "K", "Å",
  "\u00a0", "\u0085", "\u1680", "\u180e", "\u2000", "\u2028", "\u2029", "\u200b", "\u3000", "\ufeff",
  "\u0301", "\u0308", "\ue000", "\uffff", "\ufffd", "中", "日",
  "😀", "𝒳", "🇩🇪", "\u{10ffff}", "\u{1d11e}",
];
const loneSurrogates = ["\ud800", "\udbff", "\udc00", "\udfff", "\ud83d"];

const randomString = (allowLone: boolean) => {
  const length = pick([0, 1, 2, 3, 5, 8, 13]);
  let out = "";
  for (let k = 0; k < length; k++) out += allowLone && random() < 0.08 ? pick(loneSurrogates) : pick(alphabet);
  return out;
};

const stringEdges = [
  "", "a", "ab", "abc", "aaa", "a,b,,c,", ",", " ", "  padded\t\n", "\u00a0nbsp\u00a0", "\ufeffbom\ufeff",
  "\u0085nel\u0085", "\u180emvs\u180e", "\u2028ls\u2029", "\u3000ideo\u3000", "\u200bzwsp\u200b",
  "😀", "a😀b", "😀😀", "𝒳y𝒳", "🇩🇪🇫🇷", "\u{10ffff}", "e\u0301", "ÅΩK",
  "STRASSE straße", "İstanbul ıi", "ΟΔΥΣΣΕΥΣ", "ΑΣ ΑΣ.", "ǅungla", "ﬀ ŉ", "ⅷ", "ǰ̌",
  "\ue000\uffff", "\uffff\u{10000}", "$&$$$'$`$1", "a.b*c", "\\d+", "\0\x01\x1f\x7f",
  "\ud800", "a\udc00b", "\ud83d", "x\ude00", "\udfff\ud800",
];

const strings = (allowLone = true): Value[] => [
  ...stringEdges.filter((t) => allowLone || !hasLoneSurrogate(t)).map(S),
];
const randomStringValue = (allowLone = true) => S(randomString(allowLone));
const hugeStrings: Value[] = [
  SExpr(`power "ab\\x01F600" 20000`, 'power("ab😀",20000)'),
  SExpr(`power "x" 100000`, 'power("x",100000)'),
];

const ints = [0, 1, -1, 2, 3, -3, 5, 10, 31, 32, 33, 36, 37, 100, 255, -255, 65535, 65536,
  2147483647, -2147483648, -2147483647, 1073741824, 46341, -46341];
const indices = [-5, -2, -1, 0, 1, 2, 3, 4, 7, 100, 2147483647, -2147483648];
const randomInt = () =>
  pick([() => int(-10, 10), () => int(-1000, 1000), () => (random() * 4294967296) | 0])();

const numbers = [0, -0, 1, -1, 0.5, -0.5, 1.5, 2.5, -2.5, 0.1, 0.2, 0.30000000000000004, 1 / 3,
  123456789.125, 1e21, 1e-7, 1e-6, 1e20, 9007199254740993, 2147483647.5, 2147483648, -2147483649,
  4294967296, 5e-324, 2.2250738585072014e-308, 1.7976931348623157e308, -1.7976931348623157e308,
  Math.PI, Math.E, 100, 1e300, 0.000001234, 123e-20, NaN, Infinity, -Infinity];
const randomNumber = () =>
  pick([
    () => (random() - 0.5) * 200,
    () => Math.round((random() - 0.5) * 2e6) / 8,
    () => (random() - 0.5) * 10 ** int(-30, 30),
    () => new Float64Array(new Uint32Array([int(0, 0xffffffff) >>> 0, int(0, 0xffffffff) >>> 0]).buffer)[0],
  ])();

const chars = [0x41, 0x61, 0x7a, 0x30, 0x20, 0x0, 0x7f, 0x22, 0x27, 0x5c, 0xa, 0x7, 0xe9, 0xdf, 0x130,
  0x3a3, 0xd800, 0xdbff, 0xdc00, 0xdfff, 0xe000, 0xfeff, 0xffff];

// ---------------------------------------------------------------- function specs
type Pool = { edges: Value[]; random: () => Value };
const P = {
  S: { edges: strings(), random: () => randomStringValue() } as Pool,
  Sh: { edges: [...strings(), ...hugeStrings], random: () => randomStringValue() } as Pool,
  Sep: { edges: ["", ",", ", ", "a", "😀", "\ud83d", "ab", "\\"].map(S), random: () => S(pick(alphabet)) } as Pool,
  I: { edges: ints.map(I), random: () => I(randomInt()) } as Pool,
  Ix: { edges: indices.map(I), random: () => I(int(-12, 12)) } as Pool,
  Small: { edges: [0, 1, 2, 3, -1, 10].map(I), random: () => I(int(-3, 20)) } as Pool,
  Radix: { edges: [2, 8, 10, 16, 36, 1, 37, 0, -2].map(I), random: () => I(int(2, 36)) } as Pool,
  Digits: { edges: [-1, 0, 1, 2, 6, 15, 20, 21, 25, 100].map(I), random: () => I(int(0, 21)) } as Pool,
  N: { edges: numbers.map(N), random: () => N(randomNumber()) } as Pool,
  C: { edges: chars.map(C), random: () => C(pick([int(0, 0x7f), int(0, 0xffff)])) } as Pool,
  AI: {
    edges: [[], [1], [3, 1, 2], [1, 2, 3, 4, 5, 6], [5, 5, 1, 5], [2147483647, -2147483648, 0]].map((xs) => arrayOf(xs.map(I), "Int")),
    random: () => arrayOf(Array.from({ length: int(0, 9) }, () => I(int(-5, 9))), "Int"),
  } as Pool,
  AS: {
    edges: [[], [""], ["a", "b"], ["😀", "", "x,y"], ["b", "a", "B", "é", "\ue000", "😀"]].map((xs) => arrayOf(xs.map(S), "String")),
    random: () => arrayOf(Array.from({ length: int(0, 5) }, () => randomStringValue(false)), "String"),
  } as Pool,
  AN: {
    edges: [[], [NaN, 1, -0, 0], [3.5, -1e21, Infinity]].map((xs) => arrayOf(xs.map(N), "Number")),
    random: () => arrayOf(Array.from({ length: int(0, 6) }, () => N(pick([randomNumber(), pick(numbers)]))), "Number"),
  } as Pool,
  Key: {
    edges: ["", "a", "b", "1", "2", "10", "01", "-1", "1.5", "4294967294", "4294967295", "9007199254740993",
      "__proto__", "constructor", "toString", "😀", "\ue000", "Z", "é"].map(S),
    random: () => S(pick(["k", "1", "x", "2", "😀"]) + String(int(0, 30))),
  } as Pool,
  Num: {
    edges: ["1.5", " 1.5", "1.5 ", "+3", "-0", ".5", "5.", "1e3", "1E3", "1e+3", "1e", "1e400", "1e-400",
      "0x10", "0b11", "0o7", "Infinity", "-Infinity", "NaN", "infinity", "12abc", "abc", "", " ", "1_000",
      "1,5", "\u00a01", "\ufeff1", "\u00851", "\u20091", "١٢", "１", "00012", "-.5e-2", "9007199254740993",
      "2147483648", "-2147483649", "2147483647", "-2147483648", "+0", "0.1e1", "--1", "Ff", "zz", "7fffffff",
      "-80000000", "z1", "1z"].map(S),
    random: () => S(pick(["", "-", "+", " "]) + String(int(0, 99999)) + pick(["", ".", ".5", "e2", "x"])),
  } as Pool,
  Re: {
    edges: ["a", "b+", "^a", "a$", ".", "\\d+", "\\w+", "\\s+", "\\b", "(a)(b)?", "(?:x)", "[a-z]+", "[^a]",
      "a|b", "a*?", "(a+)+b", "\\u0041", "\\x41", "\\p{L}", "😀", ".", "(?<n>a)", "a{2,}", "\\/", "[", "(",
      "a(?=b)", "(?<=a)b", "\\1", "(a)\\1", "", "^", "$", "\\B", "[\\s\\S]", "\\S", "\\D", "\\W", "é"].map(S),
    random: () => S(pick(["a", "b", ".", "\\d", "[ab]", "x"]) + pick(["", "+", "*", "?", "{2}"])),
  } as Pool,
  // Regex.split's JS foreign returns `undefined` for a capture group that did not take part, so
  // split only gets patterns without capture groups.
  ReSplit: {
    edges: ["a", "b+", ",", "\\s*", "", "(?:a|b)", "[^a-z]", "\\b", "😀", ".", "a(?=b)", "x*"].map(S),
    random: () => S(pick(["a", "b", ".", "\\d", "[ab]", "x"]) + pick(["", "+", "*", "?", "{2}"])),
  } as Pool,
  // Array.range allocates its whole result in JS, so its bounds stay close.
  Range: {
    edges: [-5, -1, 0, 1, 3, 12, 2147483647, -2147483648].map(I),
    random: () => I(int(-12, 12)),
  } as Pool,
  Flags: {
    edges: ["", "g", "i", "m", "gi", "s", "u", "y", "gimsuy", "x", "gg"].map(S),
    random: () => S(pick(["", "g", "i", "gi"])),
  } as Pool,
  Repl: {
    edges: ["", "X", "$&", "$$", "$1", "$2", "$<n>", "[$`|$']", "$0", "$10", "\\", "😀"].map(S),
    random: () => S(pick(["-", "$&", "$1", "y"])),
  } as Pool,
  Json: {
    edges: ["1", "-0", "1.5", "1e400", "\"a\"", "\"\\ud800\"", "\"\\ud83d\\ude00\"", "\"\\u0000\"", "[1,2]",
      "[]", "{}", "{\"a\":1}", "{\"a\":1,\"a\":2}", "null", "true", " 1 ", "01", "1.", ".5", "NaN", "",
      "[1,]", "\"\t\"", "2147483648", "2147483647", "-2147483648", "1.0", "1e2", "\"\\x41\"",
      "{\"b\":1,\"a\":2,\"1\":3}", "\"😀\"", "9007199254740993", "[1,\"a\"]", "\"é\""].map(S),
    random: () => S(String(int(-100, 100)) + pick(["", ".25", "e1"])),
  } as Pool,
};

type Spec = { fn: string; args: (keyof typeof P)[]; expr: (a: string[]) => string; edgeLimit?: number };

const R = (render: string, body: (a: string[]) => string) => (a: string[]) => `R.${render} (${body(a)})`;

const stringSpecs: Spec[] = [
  { fn: "CodeUnits.length", args: ["Sh"], expr: R("i", (a) => `CU.length ${a[0]}`) },
  { fn: "CodeUnits.singleton", args: ["C"], expr: R("s", (a) => `CU.singleton ${a[0]}`) },
  { fn: "CodeUnits.fromCharArray", args: ["C", "C"], expr: R("s", (a) => `CU.fromCharArray [${a[0]}, ${a[1]}]`) },
  { fn: "CodeUnits.toCharArray", args: ["S"], expr: R("ac", (a) => `CU.toCharArray ${a[0]}`) },
  { fn: "CodeUnits.charAt", args: ["Ix", "S"], expr: R("mc", (a) => `CU.charAt ${a[0]} ${a[1]}`) },
  { fn: "CodeUnits.toChar", args: ["S"], expr: R("mc", (a) => `CU.toChar ${a[0]}`) },
  { fn: "CodeUnits.take", args: ["Ix", "Sh"], expr: R("i", (a) => `CU.length (CU.take ${a[0]} ${a[1]})`) },
  { fn: "CodeUnits.take.s", args: ["Ix", "S"], expr: R("s", (a) => `CU.take ${a[0]} ${a[1]}`) },
  { fn: "CodeUnits.drop", args: ["Ix", "S"], expr: R("s", (a) => `CU.drop ${a[0]} ${a[1]}`) },
  { fn: "CodeUnits.takeRight", args: ["Ix", "S"], expr: R("s", (a) => `CU.takeRight ${a[0]} ${a[1]}`) },
  { fn: "CodeUnits.slice", args: ["Ix", "Ix", "S"], expr: R("s", (a) => `CU.slice ${a[0]} ${a[1]} ${a[2]}`) },
  { fn: "CodeUnits.splitAt", args: ["Ix", "S"], expr: R("s", (a) => `(\\r -> r.before <> "|" <> r.after) (CU.splitAt ${a[0]} ${a[1]})`) },
  { fn: "CodeUnits.countPrefix", args: ["Small", "S"], expr: R("i", (a) => `CU.countPrefix (\\x -> fromEnum x /= 97 + ${a[0]} && fromEnum x < 0xE000) ${a[1]}`) },
  { fn: "CodeUnits.takeWhile", args: ["S"], expr: R("s", (a) => `CU.takeWhile (\\x -> fromEnum x /= 0x20) ${a[0]}`) },
  { fn: "CodeUnits.indexOf", args: ["Sep", "S"], expr: R("mi", (a) => `CU.indexOf (Pattern ${a[0]}) ${a[1]}`) },
  { fn: "CodeUnits.indexOf'", args: ["Sep", "Ix", "S"], expr: R("mi", (a) => `CU.indexOf' (Pattern ${a[0]}) ${a[1]} ${a[2]}`) },
  { fn: "CodeUnits.lastIndexOf", args: ["Sep", "S"], expr: R("mi", (a) => `CU.lastIndexOf (Pattern ${a[0]}) ${a[1]}`) },
  { fn: "CodeUnits.lastIndexOf'", args: ["Sep", "Ix", "S"], expr: R("mi", (a) => `CU.lastIndexOf' (Pattern ${a[0]}) ${a[1]} ${a[2]}`) },
  { fn: "CodeUnits.contains", args: ["Sep", "S"], expr: R("b", (a) => `CU.contains (Pattern ${a[0]}) ${a[1]}`) },
  { fn: "CodeUnits.stripPrefix", args: ["Sep", "S"], expr: R("ms", (a) => `CU.stripPrefix (Pattern ${a[0]}) ${a[1]}`) },
  { fn: "CodeUnits.stripSuffix", args: ["Sep", "S"], expr: R("ms", (a) => `CU.stripSuffix (Pattern ${a[0]}) ${a[1]}`) },
  { fn: "CodeUnits.uncons", args: ["S"], expr: R("s", (a) => `maybe "Nothing" (\\r -> R.c r.head <> R.s r.tail) (CU.uncons ${a[0]})`) },
  { fn: "CodeUnits.char", args: ["S"], expr: R("mc", (a) => `if CU.length ${a[0]} == 1 then Just (Unsafe.char ${a[0]}) else Nothing`) },
  { fn: "Unsafe.charAt", args: ["Ix", "S"], expr: R("mc", (a) => `if ${a[0]} >= 0 && ${a[0]} < CU.length ${a[1]} then Just (Unsafe.charAt ${a[0]} ${a[1]}) else Nothing`) },
  { fn: "CodePoints.length", args: ["Sh"], expr: R("i", (a) => `CP.length ${a[0]}`) },
  { fn: "CodePoints.toCodePointArray", args: ["S"], expr: R("ai", (a) => `map fromEnum (CP.toCodePointArray ${a[0]})`) },
  { fn: "CodePoints.fromCodePointArray", args: ["I", "I"], expr: R("s", (a) => `CP.fromCodePointArray (Array.mapMaybe toEnum [${a[0]}, ${a[1]}, 0x1F600, 0xD800])`) },
  { fn: "CodePoints.singleton", args: ["I"], expr: R("ms", (a) => `map CP.singleton (toEnum ${a[0]})`) },
  { fn: "CodePoints.codePointAt", args: ["Ix", "S"], expr: R("mi", (a) => `map fromEnum (CP.codePointAt ${a[0]} ${a[1]})`) },
  { fn: "CodePoints.take", args: ["Ix", "S"], expr: R("s", (a) => `CP.take ${a[0]} ${a[1]}`) },
  { fn: "CodePoints.drop", args: ["Ix", "S"], expr: R("s", (a) => `CP.drop ${a[0]} ${a[1]}`) },
  { fn: "CodePoints.splitAt", args: ["Ix", "S"], expr: R("s", (a) => `(\\r -> r.before <> "|" <> r.after) (CP.splitAt ${a[0]} ${a[1]})`) },
  { fn: "CodePoints.countPrefix", args: ["S"], expr: R("i", (a) => `CP.countPrefix (\\x -> fromEnum x > 0x40) ${a[0]}`) },
  { fn: "CodePoints.uncons", args: ["S"], expr: R("s", (a) => `maybe "Nothing" (\\r -> show (fromEnum r.head) <> R.s r.tail) (CP.uncons ${a[0]})`) },
  { fn: "CodePoints.indexOf", args: ["Sep", "S"], expr: R("mi", (a) => `CP.indexOf (Pattern ${a[0]}) ${a[1]}`) },
  { fn: "CodePoints.lastIndexOf'", args: ["Sep", "Ix", "S"], expr: R("mi", (a) => `CP.lastIndexOf' (Pattern ${a[0]}) ${a[1]} ${a[2]}`) },
  { fn: "Common.split", args: ["Sep", "S"], expr: R("as", (a) => `String.split (Pattern ${a[0]}) ${a[1]}`) },
  { fn: "Common.joinWith", args: ["Sep", "AS"], expr: R("s", (a) => `String.joinWith ${a[0]} ${a[1]}`) },
  { fn: "Common.toUpper", args: ["S"], expr: R("s", (a) => `String.toUpper ${a[0]}`) },
  { fn: "Common.toLower", args: ["S"], expr: R("s", (a) => `String.toLower ${a[0]}`) },
  { fn: "Common.trim", args: ["S"], expr: R("s", (a) => `String.trim ${a[0]}`) },
  { fn: "Common.replace", args: ["Sep", "Repl", "S"], expr: R("s", (a) => `String.replace (Pattern ${a[0]}) (Replacement ${a[1]}) ${a[2]}`) },
  { fn: "Common.replaceAll", args: ["Sep", "Repl", "S"], expr: R("s", (a) => `String.replaceAll (Pattern ${a[0]}) (Replacement ${a[1]}) ${a[2]}`) },
  { fn: "Common.localeCompare", args: ["S", "S"], expr: R("o", (a) => `String.localeCompare ${a[0]} ${a[1]}`), edgeLimit: 120 },
  { fn: "Common.null", args: ["S"], expr: R("b", (a) => `String.null ${a[0]}`) },
  { fn: "Ord.compareString", args: ["S", "S"], expr: R("o", (a) => `compare ${a[0]} ${a[1]}`), edgeLimit: 300 },
  { fn: "Eq.eqString", args: ["S", "S"], expr: R("b", (a) => `${a[0]} == ${a[1]}`), edgeLimit: 120 },
  { fn: "Semigroup.append", args: ["S", "S"], expr: R("s", (a) => `${a[0]} <> ${a[1]}`), edgeLimit: 60 },
  { fn: "Show.showString", args: ["S"], expr: R("s", (a) => `show ${a[0]}`) },
  { fn: "Show.showChar", args: ["C"], expr: R("s", (a) => `show ${a[0]}`) },
  { fn: "Show.showArrayString", args: ["AS"], expr: R("s", (a) => `show ${a[0]}`) },
  { fn: "Ord.compareChar", args: ["C", "C"], expr: R("o", (a) => `compare ${a[0]} ${a[1]}`), edgeLimit: 60 },
  { fn: "Enum.charSucc", args: ["C"], expr: R("mc", (a) => `succ ${a[0]}`) },
  { fn: "Enum.charPred", args: ["C"], expr: R("mc", (a) => `pred ${a[0]}`) },
  { fn: "Enum.toEnumChar", args: ["I"], expr: R("mc", (a) => `toEnum ${a[0]} :: Maybe Char`) },
];

const regexSpecs: Spec[] = [
  { fn: "Regex.regex", args: ["Re", "Flags"], expr: R("s", (a) => `either (const "Left") (\\r -> show r <> " " <> Regex.source r <> " " <> show (Regex.flags r)) (Regex.regex ${a[0]} (Regex.parseFlags ${a[1]}))`) },
  { fn: "Regex.test", args: ["Re", "Flags", "S"], expr: R("s", (a) => `withRegex ${a[0]} ${a[1]} \\r -> show (Regex.test r ${a[2]})`) },
  { fn: "Regex.match", args: ["Re", "Flags", "S"], expr: R("s", (a) => `withRegex ${a[0]} ${a[1]} \\r -> maybe "Nothing" (\\m -> intercalate ";" (map R.ms (NEA.toArray m))) (Regex.match r ${a[2]})`) },
  { fn: "Regex.replace", args: ["Re", "Flags", "Repl", "S"], expr: R("s", (a) => `withRegex ${a[0]} ${a[1]} \\r -> R.s (Regex.replace r ${a[2]} ${a[3]})`) },
  { fn: "Regex.replace'", args: ["Re", "Flags", "S"], expr: R("s", (a) => `withRegex ${a[0]} ${a[1]} \\r -> R.s (Regex.replace' r (\\m groups -> "<" <> m <> ":" <> intercalate "," (map R.ms groups) <> ">") ${a[2]})`) },
  { fn: "Regex.search", args: ["Re", "Flags", "S"], expr: R("s", (a) => `withRegex ${a[0]} ${a[1]} \\r -> R.mi (Regex.search r ${a[2]})`) },
  { fn: "Regex.split", args: ["ReSplit", "Flags", "S"], expr: R("s", (a) => `withRegex ${a[0]} ${a[1]} \\r -> R.as (Regex.split r ${a[2]})`) },
];

const unaryNumber = ["abs", "acos", "asin", "atan", "ceil", "cos", "exp", "floor", "log", "round", "sign", "sin", "sqrt", "tan", "trunc"];
const numberSpecs: Spec[] = [
  ...unaryNumber.map((f): Spec => ({ fn: `Number.${f}`, args: ["N"], expr: R("n", (a) => `Number.${f} ${a[0]}`) })),
  { fn: "Number.isNaN", args: ["N"], expr: R("b", (a) => `Number.isNaN ${a[0]}`) },
  { fn: "Number.isFinite", args: ["N"], expr: R("b", (a) => `Number.isFinite ${a[0]}`) },
  ...["atan2", "pow", "max", "min", "remainder"].map((f): Spec => ({ fn: `Number.${f}`, args: ["N", "N"], expr: R("n", (a) => `Number.${f} ${a[0]} ${a[1]}`), edgeLimit: 200 })),
  ...["+", "-", "*", "/", "mod"].map((op): Spec => ({ fn: `Number.(${op})`, args: ["N", "N"], expr: R("n", (a) => op === "mod" ? `mod ${a[0]} ${a[1]}` : `${a[0]} ${op} ${a[1]}`), edgeLimit: 150 })),
  { fn: "Number.compare", args: ["N", "N"], expr: R("o", (a) => `compare ${a[0]} ${a[1]}`), edgeLimit: 200 },
  { fn: "Number.eq", args: ["N", "N"], expr: R("b", (a) => `${a[0]} == ${a[1]}`), edgeLimit: 120 },
  { fn: "Number.lessThan", args: ["N", "N"], expr: R("b", (a) => `${a[0]} < ${a[1]}`), edgeLimit: 120 },
  { fn: "Show.showNumber", args: ["N"], expr: R("s", (a) => `show ${a[0]}`) },
  { fn: "Format.toString", args: ["N"], expr: R("s", (a) => `Format.toString ${a[0]}`) },
  { fn: "Format.fixed", args: ["Digits", "N"], expr: R("s", (a) => `Format.toStringWith (Format.fixed ${a[0]}) ${a[1]}`), edgeLimit: 200 },
  { fn: "Format.precision", args: ["Digits", "N"], expr: R("s", (a) => `Format.toStringWith (Format.precision ${a[0]}) ${a[1]}`), edgeLimit: 200 },
  { fn: "Format.exponential", args: ["Digits", "N"], expr: R("s", (a) => `Format.toStringWith (Format.exponential ${a[0]}) ${a[1]}`), edgeLimit: 200 },
  { fn: "Number.fromString", args: ["Num"], expr: R("mn", (a) => `Number.fromString ${a[0]}`) },
  { fn: "Show.showArrayNumber", args: ["AN"], expr: R("s", (a) => `show ${a[0]}`) },
  { fn: "Bounded.topNumber", args: [], expr: () => `R.n (top :: Number) <> " " <> R.n (bottom :: Number)` },
];

const intSpecs: Spec[] = [
  ...["+", "-", "*", "/", "mod"].map((op): Spec => ({ fn: `Int.(${op})`, args: ["I", "I"], expr: R("i", (a) => op === "mod" ? `mod ${a[0]} ${a[1]}` : `${a[0]} ${op} ${a[1]}`), edgeLimit: 300 })),
  ...["quot", "rem", "pow", "gcd", "lcm"].map((f): Spec => ({ fn: `Int.${f}`, args: ["I", "I"], expr: R("i", (a) => `${f === "gcd" || f === "lcm" ? f : "Int." + f} ${a[0]} ${a[1]}`), edgeLimit: 300 })),
  ...["and", "or", "xor", "shl", "shr", "zshr"].map((f): Spec => ({ fn: `Bits.${f}`, args: ["I", "I"], expr: R("i", (a) => `Bits.${f} ${a[0]} ${a[1]}`), edgeLimit: 200 })),
  { fn: "Bits.complement", args: ["I"], expr: R("i", (a) => `Bits.complement ${a[0]}`) },
  { fn: "Int.negate", args: ["I"], expr: R("i", (a) => `negate ${a[0]}`) },
  { fn: "Int.degree", args: ["I"], expr: R("i", (a) => `degree ${a[0]}`) },
  { fn: "Int.compare", args: ["I", "I"], expr: R("o", (a) => `compare ${a[0]} ${a[1]}`), edgeLimit: 100 },
  { fn: "Int.even", args: ["I"], expr: R("b", (a) => `Int.even ${a[0]}`) },
  { fn: "Int.toNumber", args: ["I"], expr: R("n", (a) => `Int.toNumber ${a[0]}`) },
  { fn: "Int.fromNumber", args: ["N"], expr: R("mi", (a) => `Int.fromNumber ${a[0]}`) },
  ...["round", "floor", "ceil", "trunc"].map((f): Spec => ({ fn: `Int.${f}`, args: ["N"], expr: R("i", (a) => `Int.${f} ${a[0]}`) })),
  { fn: "Int.fromString", args: ["Num"], expr: R("mi", (a) => `Int.fromString ${a[0]}`) },
  { fn: "Int.fromStringAs", args: ["Radix", "Num"], expr: R("s", (a) => `maybe "NoRadix" (\\r -> R.mi (Int.fromStringAs r ${a[1]})) (Int.radix ${a[0]})`), edgeLimit: 300 },
  { fn: "Int.toStringAs", args: ["Radix", "I"], expr: R("s", (a) => `maybe "NoRadix" (\\r -> Int.toStringAs r ${a[1]}) (Int.radix ${a[0]})`), edgeLimit: 200 },
  { fn: "Show.showInt", args: ["I"], expr: R("s", (a) => `show ${a[0]}`) },
  { fn: "Enum.fromCharCode", args: ["I"], expr: R("mc", (a) => `Char.fromCharCode ${a[0]}`) },
  { fn: "Enum.toCharCode", args: ["C"], expr: R("i", (a) => `Char.toCharCode ${a[0]}`) },
  { fn: "Bounded.topInt", args: [], expr: () => `R.i (top :: Int) <> " " <> R.i (bottom :: Int)` },
];

const arraySpecs: Spec[] = [
  { fn: "Array.slice", args: ["Ix", "Ix", "AI"], expr: R("ai", (a) => `Array.slice ${a[0]} ${a[1]} ${a[2]}`), edgeLimit: 200 },
  { fn: "Array.take", args: ["Ix", "AI"], expr: R("ai", (a) => `Array.take ${a[0]} ${a[1]}`) },
  { fn: "Array.drop", args: ["Ix", "AI"], expr: R("ai", (a) => `Array.drop ${a[0]} ${a[1]}`) },
  { fn: "Array.takeEnd", args: ["Ix", "AI"], expr: R("ai", (a) => `Array.takeEnd ${a[0]} ${a[1]}`) },
  { fn: "Array.dropEnd", args: ["Ix", "AI"], expr: R("ai", (a) => `Array.dropEnd ${a[0]} ${a[1]}`) },
  { fn: "Array.splitAt", args: ["Ix", "AI"], expr: R("s", (a) => `(\\r -> show r.before <> show r.after) (Array.splitAt ${a[0]} ${a[1]})`) },
  { fn: "Array.insertAt", args: ["Ix", "AI"], expr: R("s", (a) => `show (Array.insertAt ${a[0]} 99 ${a[1]})`) },
  { fn: "Array.deleteAt", args: ["Ix", "AI"], expr: R("s", (a) => `show (Array.deleteAt ${a[0]} ${a[1]})`) },
  { fn: "Array.updateAt", args: ["Ix", "AI"], expr: R("s", (a) => `show (Array.updateAt ${a[0]} 99 ${a[1]})`) },
  { fn: "Array.modifyAt", args: ["Ix", "AI"], expr: R("s", (a) => `show (Array.modifyAt ${a[0]} (_ * 2) ${a[1]})`) },
  { fn: "Array.range", args: ["Range", "Range"], expr: R("i", (a) => `(\\r -> if Array.length r > 50 then Array.length r else sum r) (if Int.toNumber ${a[0]} - Int.toNumber ${a[1]} > 100.0 || Int.toNumber ${a[1]} - Int.toNumber ${a[0]} > 100.0 then [] else Array.range ${a[0]} ${a[1]})`), edgeLimit: 80 },
  { fn: "Array.replicate", args: ["Ix"], expr: R("i", (a) => `Array.length (Array.replicate (min 100000 ${a[0]}) 'x')`) },
  { fn: "Array.reverse", args: ["AI"], expr: R("ai", (a) => `Array.reverse ${a[0]}`) },
  { fn: "Array.concat", args: ["AI", "AI"], expr: R("ai", (a) => `Array.concat [${a[0]}, ${a[1]}, []]`) },
  { fn: "Array.filter", args: ["AI"], expr: R("ai", (a) => `Array.filter (_ > 2) ${a[0]}`) },
  { fn: "Array.partition", args: ["AI"], expr: R("s", (a) => `(\\r -> show r.yes <> show r.no) (Array.partition Int.even ${a[0]})`) },
  { fn: "Array.zipWith", args: ["AI", "AI"], expr: R("ai", (a) => `Array.zipWith (-) ${a[0]} ${a[1]}`) },
  { fn: "Array.scanl", args: ["AI"], expr: R("ai", (a) => `Array.scanl (-) 1 ${a[0]}`) },
  { fn: "Array.scanr", args: ["AI"], expr: R("ai", (a) => `Array.scanr (-) 1 ${a[0]}`) },
  { fn: "Array.uncons", args: ["AI"], expr: R("s", (a) => `maybe "Nothing" (\\r -> show r.head <> show r.tail) (Array.uncons ${a[0]})`) },
  { fn: "Array.unsnoc", args: ["AI"], expr: R("s", (a) => `maybe "Nothing" (\\r -> show r.init <> show r.last) (Array.unsnoc ${a[0]})`) },
  { fn: "Array.sortBy", args: ["AI"], expr: R("ai", (a) => `Array.sortBy (comparing (_ \`mod\` 3)) ${a[0]}`) },
  { fn: "Array.sort", args: ["AI"], expr: R("ai", (a) => `Array.sort ${a[0]}`) },
  { fn: "Array.sortString", args: ["AS"], expr: R("as", (a) => `Array.sort ${a[0]}`) },
  { fn: "Array.sortNumber", args: ["AN"], expr: R("an", (a) => `Array.sort ${a[0]}`) },
  { fn: "Array.nubNumber", args: ["AN"], expr: R("an", (a) => `Array.nub ${a[0]}`) },
  { fn: "Array.findMap", args: ["AI"], expr: R("mi", (a) => `Array.findMap (\\x -> if x > 2 then Just (x * 10) else Nothing) ${a[0]}`) },
  { fn: "Array.findIndex", args: ["AI"], expr: R("mi", (a) => `Array.findIndex (_ == 5) ${a[0]}`) },
  { fn: "Array.findLastIndex", args: ["AI"], expr: R("mi", (a) => `Array.findLastIndex (_ == 5) ${a[0]}`) },
  { fn: "Array.elemIndex", args: ["AN"], expr: R("mi", (a) => `Array.elemIndex nan ${a[0]} <|> Array.elemIndex 0.0 ${a[0]}`) },
  { fn: "Array.any", args: ["AI"], expr: R("b", (a) => `Array.any (_ > 4) ${a[0]}`) },
  { fn: "Array.all", args: ["AI"], expr: R("b", (a) => `Array.all (_ > 0) ${a[0]}`) },
  { fn: "Array.foldl", args: ["AI"], expr: R("i", (a) => `foldl (\\acc x -> acc * 3 - x) 7 ${a[0]}`) },
  { fn: "Array.foldr", args: ["AI"], expr: R("i", (a) => `foldr (\\x acc -> acc * 3 - x) 7 ${a[0]}`) },
  { fn: "Array.foldr1", args: ["AI"], expr: R("s", (a) => `maybe "Nothing" (show <<< NEA.foldr1 (-)) (NEA.fromArray ${a[0]})`) },
  { fn: "Array.foldl1", args: ["AI"], expr: R("s", (a) => `maybe "Nothing" (show <<< NEA.foldl1 (-)) (NEA.fromArray ${a[0]})`) },
  { fn: "Array.unfoldr", args: ["Small"], expr: R("ai", (a) => `unfoldr (\\k -> if k <= 0 then Nothing else Just (k /\\ (k - 1))) ${a[0]} :: Array Int`) },
  { fn: "Array.mapWithIndex", args: ["AI"], expr: R("ai", (a) => `mapWithIndex (\\k x -> k * 100 + x) ${a[0]}`) },
  { fn: "Array.apply", args: ["AI"], expr: R("ai", (a) => `[(_ + 1), (_ * 2)] <*> ${a[0]}`) },
  { fn: "Array.bind", args: ["AI"], expr: R("ai", (a) => `${a[0]} >>= \\x -> [x, x]`) },
  { fn: "Array.eq", args: ["AI", "AI"], expr: R("b", (a) => `${a[0]} == ${a[1]}`), edgeLimit: 60 },
  { fn: "Array.compare", args: ["AI", "AI"], expr: R("o", (a) => `compare ${a[0]} ${a[1]}`), edgeLimit: 60 },
  { fn: "Array.compareNumber", args: ["AN", "AN"], expr: R("o", (a) => `compare ${a[0]} ${a[1]}`), edgeLimit: 60 },
  { fn: "Array.eqNumber", args: ["AN", "AN"], expr: R("b", (a) => `${a[0]} == ${a[1]}`), edgeLimit: 60 },
  { fn: "Array.snoc", args: ["AI"], expr: R("ai", (a) => `Array.snoc ${a[0]} 0`) },
  { fn: "Array.cons", args: ["AI"], expr: R("ai", (a) => `Array.cons 0 ${a[0]}`) },
  { fn: "Array.fromFoldableList", args: ["AI"], expr: R("ai", (a) => `Array.fromFoldable (List.fromFoldable ${a[0]})`) },
  { fn: "Show.showArrayInt", args: ["AI"], expr: R("s", (a) => `show ${a[0]}`) },
];

// Its own program: a constant negative index fails to build (see the report), and that must
// not hide the other array cases.
const arrayIndexSpecs: Spec[] = [
  { fn: "Array.index", args: ["Ix", "AI"], expr: R("mi", (a) => `Array.index ${a[1]} ${a[0]}`) },
];

const collectionSpecs: Spec[] = [
  { fn: "Map.fromFoldable.keys", args: ["Key", "Key", "Key"], expr: R("as", (a) => `Array.fromFoldable (Map.keys (Map.fromFoldable [${a[0]} /\\ 1, ${a[1]} /\\ 2, ${a[2]} /\\ 3]))`), edgeLimit: 150 },
  { fn: "Map.toUnfoldable", args: ["AS"], expr: R("s", (a) => `show (map (\\(k /\\ v) -> R.s k <> "=" <> show v) (Map.toUnfoldable (Map.fromFoldable (Array.mapWithIndex (\\k x -> x /\\ k) ${a[0]})) :: Array (String /\\ Int)))`) },
  { fn: "Map.numberKeys", args: ["AN"], expr: R("s", (a) => `show (Array.fromFoldable (Map.keys (Map.fromFoldable (map (\\x -> x /\\ unit) ${a[0]}))))`) },
  { fn: "Map.lookupNaN", args: ["AN"], expr: R("s", (a) => `(\\m -> show (Map.lookup nan m) <> show (Map.lookup (-0.0) m) <> show (Map.size m)) (Map.fromFoldable (Array.mapWithIndex (\\k x -> x /\\ k) ${a[0]}))`) },
  { fn: "Set.fromFoldable", args: ["AS"], expr: R("as", (a) => `Array.fromFoldable (Set.fromFoldable ${a[0]})`) },
  { fn: "Map.deleteLookup", args: ["Key", "AS"], expr: R("s", (a) => `(\\m -> show (Map.size m) <> R.ms (Map.lookup ${a[0]} m) <> R.ms (map _.key (Map.findMin m))) (Map.delete ${a[0]} (Map.fromFoldable (map (\\x -> x /\\ x) ${a[1]})))`) },
  { fn: "Object.fromFoldable.keys", args: ["Key", "Key", "Key"], expr: R("as", (a) => `Object.keys (Object.fromFoldable [${a[0]} /\\ 1, ${a[1]} /\\ 2, ${a[2]} /\\ 3])`), edgeLimit: 300 },
  { fn: "Object.toUnfoldable", args: ["Key", "Key", "Key"], expr: R("s", (a) => `show (map (\\(k /\\ v) -> R.s k <> "=" <> show v) (Object.toUnfoldable (Object.fromFoldable [${a[0]} /\\ 1, ${a[1]} /\\ 2, ${a[2]} /\\ 3]) :: Array (String /\\ Int)))`), edgeLimit: 150 },
  { fn: "Object.values", args: ["Key", "Key"], expr: R("ai", (a) => `Object.values (Object.insert ${a[1]} 7 (Object.singleton ${a[0]} 5))`), edgeLimit: 120 },
  { fn: "Object.show", args: ["Key", "Key"], expr: R("s", (a) => `show (Object.insert ${a[1]} 7 (Object.singleton ${a[0]} 5))`), edgeLimit: 120 },
  { fn: "Object.lookupDelete", args: ["Key", "Key"], expr: R("s", (a) => `(\\o -> show (Object.lookup ${a[0]} o) <> show (Object.size o) <> show (Object.member ${a[1]} o)) (Object.delete ${a[1]} (Object.fromFoldable [${a[0]} /\\ 1, "b" /\\ 2]))`), edgeLimit: 120 },
  { fn: "Object.fold", args: ["Key", "Key", "Key"], expr: R("s", (a) => `Object.fold (\\acc k v -> acc <> R.s k <> show v) "" (Object.fromFoldable [${a[0]} /\\ 1, ${a[1]} /\\ 2, ${a[2]} /\\ 3])`), edgeLimit: 100 },
  { fn: "Object.foldMap", args: ["Key", "Key"], expr: R("s", (a) => `Object.foldMap (\\k v -> [R.s k <> show v]) (Object.fromFoldable [${a[0]} /\\ 1, ${a[1]} /\\ 2, "2" /\\ 3]) # intercalate ","`), edgeLimit: 100 },
  { fn: "Object.mapWithKey", args: ["Key", "Key"], expr: R("s", (a) => `show (Object.mapWithKey (\\k v -> k <> show v) (Object.fromFoldable [${a[0]} /\\ 1, ${a[1]} /\\ 2]))`), edgeLimit: 100 },
  { fn: "Object.union", args: ["Key", "Key", "Key"], expr: R("as", (a) => `Object.keys (Object.union (Object.fromFoldable [${a[0]} /\\ 1, ${a[1]} /\\ 2]) (Object.fromFoldable [${a[2]} /\\ 3, "0" /\\ 4]))`), edgeLimit: 100 },
  { fn: "Object.all", args: ["Key", "Key"], expr: R("b", (a) => `Object.all (\\k v -> k /= "1" && v < 3) (Object.fromFoldable [${a[0]} /\\ 1, ${a[1]} /\\ 2])`), edgeLimit: 60 },
  { fn: "Object.foldM", args: ["Key", "Key"], expr: R("s", (a) => `show (Object.foldM (\\acc k v -> if k == "" then Nothing else Just (acc <> k <> show v)) "" (Object.fromFoldable [${a[0]} /\\ 1, ${a[1]} /\\ 2]))`), edgeLimit: 60 },
  { fn: "Object.eq", args: ["Key", "Key"], expr: R("b", (a) => `Object.fromFoldable [${a[0]} /\\ 1, ${a[1]} /\\ 2] == Object.fromFoldable [${a[1]} /\\ 2, ${a[0]} /\\ 1]`), edgeLimit: 60 },
];

const jsonSpecs: Spec[] = [
  { fn: "JSON.writeString", args: ["S"], expr: R("s", (a) => `JSON.writeJSON ${a[0]}`) },
  { fn: "JSON.writeNumber", args: ["N"], expr: R("s", (a) => `JSON.writeJSON ${a[0]}`) },
  { fn: "JSON.writeInt", args: ["I"], expr: R("s", (a) => `JSON.writeJSON ${a[0]}`) },
  { fn: "JSON.writeArrayNumber", args: ["AN"], expr: R("s", (a) => `JSON.writeJSON ${a[0]}`) },
  { fn: "JSON.writeArrayString", args: ["AS"], expr: R("s", (a) => `JSON.writeJSON ${a[0]}`) },
  { fn: "JSON.writeRecord", args: ["S", "N"], expr: R("s", (a) => `JSON.writeJSON { zeta: ${a[0]}, alpha: ${a[1]}, maybe: (Nothing :: Maybe Int), just: Just 1 }`), edgeLimit: 80 },
  { fn: "JSON.writeObject", args: ["Key", "Key", "Key"], expr: R("s", (a) => `JSON.writeJSON (Object.fromFoldable [${a[0]} /\\ 1, ${a[1]} /\\ 2, ${a[2]} /\\ 3])`), edgeLimit: 120 },
  { fn: "JSON.writePretty", args: ["Key"], expr: R("s", (a) => `JSON.writePrettyJSON 2 { a: [1, 2], b: ${a[0]}, c: [] :: Array Int }`) },
  { fn: "JSON.readInt", args: ["Json"], expr: R("s", (a) => `either (const "Left") show (JSON.readJSON ${a[0]} :: _ Int)`) },
  { fn: "JSON.readNumber", args: ["Json"], expr: R("s", (a) => `either (const "Left") show (JSON.readJSON ${a[0]} :: _ Number)`) },
  { fn: "JSON.readString", args: ["Json"], expr: R("s", (a) => `either (const "Left") R.s (JSON.readJSON ${a[0]} :: _ String)`) },
  { fn: "JSON.readArrayInt", args: ["Json"], expr: R("s", (a) => `either (const "Left") show (JSON.readJSON ${a[0]} :: _ (Array Int))`) },
  { fn: "JSON.readRecord", args: ["Json"], expr: R("s", (a) => `either (const "Left") (\\(r :: { a :: Maybe Int }) -> show r.a) (JSON.readJSON ${a[0]})`) },
  { fn: "JSON.readObject", args: ["Json"], expr: R("s", (a) => `either (const "Left") (\\(o :: Object.Object Int) -> show (Object.keys o) <> show (Object.values o)) (JSON.readJSON ${a[0]})`) },
  { fn: "JSON.roundTripString", args: ["S"], expr: R("s", (a) => `either (const "Left") R.s (JSON.readJSON (JSON.writeJSON ${a[0]}) :: _ String)`) },
  { fn: "JSON.roundTripNumber", args: ["N"], expr: R("s", (a) => `either (const "Left") show (JSON.readJSON (JSON.writeJSON ${a[0]}) :: _ Number)`) },
];

// ---------------------------------------------------------------- case expansion
type Case = { label: string; fn: string; inputs: string[]; lone: boolean; expr: string };

const expand = (spec: Spec): Case[] => {
  const pools = spec.args.map((k) => P[k]);
  const combos: Value[][] = [];
  const cross = (k: number, acc: Value[]) => {
    if (k === pools.length) return void combos.push(acc);
    for (const v of pools[k].edges) cross(k + 1, [...acc, v]);
  };
  cross(0, []);
  const limit = Math.min(spec.edgeLimit ?? 150, 150);
  // A fixed-seed subsample keeps the cross product of multi-argument functions bounded.
  while (combos.length > limit) combos.splice(Math.floor(random() * combos.length), 1);
  if (pools.length > 0) {
    for (let r = 0; r < randomPerFunction; r++) {
      combos.push(pools.map((pool) => (random() < 0.5 ? pool.random() : pick(pool.edges))));
    }
  }
  return combos.map((values, k) => ({
    label: `${spec.fn}#${k}`,
    fn: spec.fn,
    inputs: values.map((v) => v.show),
    lone: values.some((v) => v.lone),
    expr: spec.expr(values.map((v) => v.ps)),
  }));
};

const header = (name: string) => `module Fuzz.${name} where

import Prelude

import Control.Alt ((<|>))
import Data.Array as Array
import Data.Array.NonEmpty as NEA
import Data.Char as Char
import Data.Either (either)
import Data.Enum (fromEnum, toEnum, succ, pred)
import Data.Foldable (foldl, foldr, intercalate, sum)
import Data.FunctorWithIndex (mapWithIndex)
import Data.Int as Int
import Data.Int.Bits as Bits
import Data.List as List
import Data.Map as Map
import Data.Maybe (Maybe(..), maybe)
import Data.Monoid (power)
import Data.Number as Number
import Data.Number (nan, infinity)
import Data.Number.Format as Format
import Data.Ord (comparing)
import Data.Set as Set
import Data.String as String
import Data.String.CodePoints as CP
import Data.String.CodeUnits as CU
import Data.String.Pattern (Pattern(..), Replacement(..))
import Data.String.Regex as Regex
import Data.String.Unsafe as Unsafe
import Data.Tuple.Nested ((/\\), type (/\\))
import Data.Unfoldable (unfoldr)
import Effect (Effect)
import Foreign.Object as Object
import Fuzz.Render as R
import Yoga.JSON as JSON

withRegex :: String -> String -> (Regex.Regex -> String) -> String
withRegex pattern flags k = either (const "BadRegex") k (Regex.regex pattern (Regex.parseFlags flags))
`;

const areas: [string, Spec[]][] = [
  ["Strings", stringSpecs],
  ["Regex", regexSpecs],
  ["Numbers", numberSpecs],
  ["Ints", intSpecs],
  ["Arrays", arraySpecs],
  ["ArrayIndex", arrayIndexSpecs],
  ["Collections", collectionSpecs],
  ["Json", jsonSpecs],
];

mkdirSync(join(srcDir, "Fuzz"), { recursive: true });
const allCases: Omit<Case, "expr">[] = [];
const modules: string[] = [];
for (const [area, specs] of areas) {
  const cases = specs.flatMap(expand);
  for (let start = 0, part = 1; start < cases.length; start += chunkSize, part++) {
    const name = `${area}${part}`;
    const chunk = cases.slice(start, start + chunkSize);
    const body = chunk
      .map((c) => `  , { label: ${JSON.stringify(c.label)}, result: \\_ -> ${c.expr} }`)
      .join("\n")
      .replace(/^  ,/, "  [");
    writeFileSync(
      join(srcDir, "Fuzz", `${name}.purs`),
      `${header(name)}\nmain :: Effect Unit\nmain = R.run cases\n\ncases :: Array { label :: String, result :: Unit -> String }\ncases =\n${body}\n  ]\n`,
    );
    modules.push(`Fuzz.${name}`);
    for (const { expr: _, ...rest } of chunk) allCases.push(rest);
  }
}
writeFileSync(casesFile, JSON.stringify({ seed, modules, cases: allCases }));
console.log(modules.join("\n"));
