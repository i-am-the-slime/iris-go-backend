// The types a generated program can mention, how they print, and which classes they belong to.

export type Field = { name: string; type: Type };

export type Type =
  | { tag: "Int" }
  | { tag: "Number" }
  | { tag: "Boolean" }
  | { tag: "Char" }
  | { tag: "String" }
  | { tag: "Unit" }
  | { tag: "Ordering" }
  | { tag: "Maybe"; arg: Type }
  | { tag: "Either"; left: Type; right: Type }
  | { tag: "Tuple"; first: Type; second: Type }
  | { tag: "Array"; arg: Type }
  | { tag: "List"; arg: Type }
  | { tag: "Map"; key: Type; value: Type }
  | { tag: "Set"; arg: Type }
  | { tag: "Record"; fields: Field[] }
  | { tag: "Function"; from: Type; to: Type }
  | { tag: "Data"; name: string; args: Type[] }
  | { tag: "Lazy"; arg: Type }
  | { tag: "Effect"; arg: Type }
  | { tag: "Ref"; arg: Type }
  | { tag: "Var"; name: string };

export const Int: Type = { tag: "Int" };
export const Number: Type = { tag: "Number" };
export const Boolean: Type = { tag: "Boolean" };
export const Char: Type = { tag: "Char" };
export const String: Type = { tag: "String" };
export const Unit: Type = { tag: "Unit" };
export const Ordering: Type = { tag: "Ordering" };
export const maybe = (arg: Type): Type => ({ tag: "Maybe", arg });
export const either = (left: Type, right: Type): Type => ({ tag: "Either", left, right });
export const tuple = (first: Type, second: Type): Type => ({ tag: "Tuple", first, second });
export const array = (arg: Type): Type => ({ tag: "Array", arg });
export const list = (arg: Type): Type => ({ tag: "List", arg });
export const map = (key: Type, value: Type): Type => ({ tag: "Map", key, value });
export const set = (arg: Type): Type => ({ tag: "Set", arg });
export const record = (fields: Field[]): Type => ({
  tag: "Record",
  fields: [...fields].sort((a, b) => (a.name < b.name ? -1 : a.name > b.name ? 1 : 0)),
});
export const fn = (from: Type, to: Type): Type => ({ tag: "Function", from, to });
export const fnN = (params: Type[], to: Type): Type =>
  params.reduceRight((result, param) => fn(param, result), to);
export const data = (name: string, args: Type[] = []): Type => ({ tag: "Data", name, args });
export const lazy = (arg: Type): Type => ({ tag: "Lazy", arg });
export const effect = (arg: Type): Type => ({ tag: "Effect", arg });
export const ref = (arg: Type): Type => ({ tag: "Ref", arg });
export const tvar = (name: string): Type => ({ tag: "Var", name });

export type PolyType = {
  vars: string[];
  constraints: { className: string; type: Type }[];
  type: Type;
};

/** What the generator knows about a user-declared type: its parameters and derived classes. */
export type DataInfo = {
  name: string;
  params: string[];
  constructors: { name: string; fields: Type[] }[];
  classes: Set<string>;
  isNewtype: boolean;
};

export type DataEnvironment = Map<string, DataInfo>;

export const typeEquals = (a: Type, b: Type): boolean => printType(a) === printType(b);

const atomic = (type: Type): boolean =>
  ["Int", "Number", "Boolean", "Char", "String", "Unit", "Ordering", "Record", "Var"].includes(type.tag) ||
  (type.tag === "Data" && type.args.length === 0);

const parenthesised = (type: Type): string => (atomic(type) ? printType(type) : `(${printType(type)})`);

export const printType = (type: Type): string => {
  switch (type.tag) {
    case "Int":
    case "Number":
    case "Boolean":
    case "Char":
    case "String":
    case "Unit":
    case "Ordering":
      return type.tag;
    case "Maybe":
      return `Maybe ${parenthesised(type.arg)}`;
    case "Either":
      return `Either ${parenthesised(type.left)} ${parenthesised(type.right)}`;
    case "Tuple":
      return `Tuple ${parenthesised(type.first)} ${parenthesised(type.second)}`;
    case "Array":
      return `Array ${parenthesised(type.arg)}`;
    case "List":
      return `List.List ${parenthesised(type.arg)}`;
    case "Map":
      return `Map.Map ${parenthesised(type.key)} ${parenthesised(type.value)}`;
    case "Set":
      return `Set.Set ${parenthesised(type.arg)}`;
    case "Record":
      if (type.fields.length === 0) return "{}";
      return `{ ${type.fields.map((field) => `${field.name} :: ${printType(field.type)}`).join(", ")} }`;
    case "Function":
      return `${type.from.tag === "Function" ? `(${printType(type.from)})` : printType(type.from)} -> ${printType(type.to)}`;
    case "Data":
      return type.args.length === 0 ? type.name : `${type.name} ${type.args.map(parenthesised).join(" ")}`;
    case "Lazy":
      return `Lazy.Lazy ${parenthesised(type.arg)}`;
    case "Effect":
      return `Effect ${parenthesised(type.arg)}`;
    case "Ref":
      return `Ref.Ref ${parenthesised(type.arg)}`;
    case "Var":
      return type.name;
  }
};

export const printPolyType = (poly: PolyType): string => {
  const quantifier = poly.vars.length > 0 ? `forall ${poly.vars.join(" ")}. ` : "";
  const constraints = poly.constraints.map((c) => `${c.className} ${parenthesised(c.type)} => `).join("");
  return `${quantifier}${constraints}${printType(poly.type)}`;
};

/** Substitutes type variables by name. */
export const substitute = (type: Type, bindings: Map<string, Type>): Type => {
  const go = (t: Type): Type => substitute(t, bindings);
  switch (type.tag) {
    case "Var":
      return bindings.get(type.name) ?? type;
    case "Maybe":
      return maybe(go(type.arg));
    case "Either":
      return either(go(type.left), go(type.right));
    case "Tuple":
      return tuple(go(type.first), go(type.second));
    case "Array":
      return array(go(type.arg));
    case "List":
      return list(go(type.arg));
    case "Map":
      return map(go(type.key), go(type.value));
    case "Set":
      return set(go(type.arg));
    case "Record":
      return record(type.fields.map((field) => ({ name: field.name, type: go(field.type) })));
    case "Function":
      return fn(go(type.from), go(type.to));
    case "Data":
      return data(type.name, type.args.map(go));
    case "Lazy":
      return lazy(go(type.arg));
    case "Effect":
      return effect(go(type.arg));
    case "Ref":
      return ref(go(type.arg));
    default:
      return type;
  }
};

export const freeVars = (type: Type, into: Set<string> = new Set()): Set<string> => {
  switch (type.tag) {
    case "Var":
      into.add(type.name);
      break;
    case "Maybe":
    case "Array":
    case "List":
    case "Set":
    case "Lazy":
    case "Effect":
    case "Ref":
      freeVars(type.arg, into);
      break;
    case "Either":
      freeVars(type.left, into);
      freeVars(type.right, into);
      break;
    case "Tuple":
      freeVars(type.first, into);
      freeVars(type.second, into);
      break;
    case "Map":
      freeVars(type.key, into);
      freeVars(type.value, into);
      break;
    case "Record":
      for (const field of type.fields) freeVars(field.type, into);
      break;
    case "Function":
      freeVars(type.from, into);
      freeVars(type.to, into);
      break;
    case "Data":
      for (const arg of type.args) freeVars(arg, into);
      break;
    default:
      break;
  }
  return into;
};

export type ClassName = "Show" | "Eq" | "Ord" | "Semigroup" | "Monoid";

/**
 * Whether a type has an instance of a standard class. Type variables are assumed to carry the
 * constraint the enclosing signature declares (the generator only asks under such a signature).
 */
export const hasClass = (
  className: ClassName,
  type: Type,
  dataEnvironment: DataEnvironment,
  assumedVars: Map<string, Set<string>> = new Map(),
): boolean => {
  const has = (t: Type) => hasClass(className, t, dataEnvironment, assumedVars);
  switch (type.tag) {
    case "Int":
    case "Number":
    case "Boolean":
    case "Char":
    case "String":
    case "Unit":
    case "Ordering":
      return className === "Semigroup" || className === "Monoid"
        ? type.tag === "String" || type.tag === "Unit" || type.tag === "Ordering" && className === "Semigroup"
        : true;
    case "Maybe":
      if (className === "Semigroup" || className === "Monoid") return hasClass("Semigroup", type.arg, dataEnvironment, assumedVars);
      return has(type.arg);
    case "Either":
      if (className === "Semigroup" || className === "Monoid") return false;
      return has(type.left) && has(type.right);
    case "Tuple":
      return has(type.first) && has(type.second);
    case "Array":
    case "List":
      if (className === "Semigroup" || className === "Monoid") return true;
      return has(type.arg);
    case "Map":
      if (className === "Semigroup" || className === "Monoid") {
        return hasClass("Ord", type.key, dataEnvironment, assumedVars) && hasClass("Semigroup", type.value, dataEnvironment, assumedVars);
      }
      return has(type.key) && has(type.value);
    case "Set":
      if (className === "Semigroup" || className === "Monoid") return hasClass("Ord", type.arg, dataEnvironment, assumedVars);
      return has(type.arg);
    case "Record":
      return type.fields.every((field) => has(field.type));
    case "Function":
      return false;
    case "Data": {
      const info = dataEnvironment.get(type.name);
      if (!info) return false;
      return info.classes.has(className) && type.args.every(has);
    }
    case "Lazy":
      return className === "Semigroup" || className === "Monoid" ? has(type.arg) : has(type.arg);
    case "Effect":
    case "Ref":
      return false;
    case "Var":
      return assumedVars.get(type.name)?.has(className) ?? false;
  }
};

/** The number of type constructors in a type, a size measure for keeping types bounded. */
export const typeSize = (type: Type): number => {
  switch (type.tag) {
    case "Maybe":
    case "Array":
    case "List":
    case "Set":
    case "Lazy":
    case "Effect":
    case "Ref":
      return 1 + typeSize(type.arg);
    case "Either":
      return 1 + typeSize(type.left) + typeSize(type.right);
    case "Tuple":
      return 1 + typeSize(type.first) + typeSize(type.second);
    case "Map":
      return 1 + typeSize(type.key) + typeSize(type.value);
    case "Record":
      return 1 + type.fields.reduce((sum, field) => sum + typeSize(field.type), 0);
    case "Function":
      return 1 + typeSize(type.from) + typeSize(type.to);
    case "Data":
      return 1 + type.args.reduce((sum, arg) => sum + typeSize(arg), 0);
    default:
      return 1;
  }
};
