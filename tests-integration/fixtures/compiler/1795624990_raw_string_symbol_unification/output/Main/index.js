export function name(dictionary) {
  return dictionary.name;
}
export const named = { name: ($proxy) => "a box" };
export const rawName = /* @__PURE__ */ name(named)("Proxy");
export const rawAsPlain = "Proxy";
export const plainAsRaw = "Proxy";
export const multilineAsEscaped = "Proxy";
