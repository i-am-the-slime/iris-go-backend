import * as $runtime from "../runtime.js";
export function describe(dictionary) {
  return dictionary.describe;
}
export function describeArray(describeADict) {
  return { describe: ($array) => "array" };
}
export function describeWrapped(describeADict) {
  return /* @__PURE__ */ describeArray(describeADict);
}
const $lazy_describeTree = $runtime.binding("describeTree", () => {
  return /* @__PURE__ */ describeArray($lazy_describeTree());
});
export const describeInt = { describe: ($int) => "int" };
export const describeTree = $lazy_describeTree();
export const describeLeaves = /* @__PURE__ */ describeArray(describeInt);
