export const V = "V";
export const P = "P";
export const Id = ($value0) => ({
  tag: "Id",
  _1: $value0
});
export function tVType(rowToListRRlDict) {
  return (tRLRlRDict) => {
    return {};
  };
}
export function casesConsType(consSymFRi_RiDict) {
  return (casesRlRi_Dict) => {
    return (handlerKFDict) => {
      return {};
    };
  };
}
export function elim(rowToListCasesCasesrlDict) {
  return (casesCasesrlAffectedDict) => {
    return (unionAffectedUnaffectedAllDict) => {
      return (tVUnaffectedDict) => {
        return ($record) => ($p) => 0 | 0;
      };
    };
  };
}
export function test(tVRDict) {
  return /* @__PURE__ */ elim({})(/* @__PURE__ */ casesConsType({})(casesNilTypeRow)(handlerTypeFunction))({})(tVRDict)({ x: ($id) => {
    if ($id.tag === "Id") {
      const { _1: n } = $id;
      return {
        tag: "Id",
        _1: n
      };
    } else {
      throw new Error("Pattern match failure");
    }
  } });
}
export const casesNilTypeRow = {};
export const handlerTypeFunction = {};
