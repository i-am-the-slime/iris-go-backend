export function describe(dictionary) {
  return dictionary.describe;
}
export function described(describeADict) {
  return (value) => ({ label: /* @__PURE__ */ describe(describeADict)(value) });
}
export function defaulted(describeADict) {
  return { name: "defaulted" };
}
export const describeInt = { describe: ($int) => "Int" };
export const accessAfterApplication = (/* @__PURE__ */ described(describeInt)(1 | 0)).label;
export const accessAfterTypeApplication = (/* @__PURE__ */ defaulted(describeInt)).name;
export const accessNested = { outer: /* @__PURE__ */ defaulted(describeInt) }.outer.name;
