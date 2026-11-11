export const Just = ($value0) => ({
  tag: "Just",
  _1: $value0
});
export const Nothing = "Nothing";
export const Pair = ($value0) => ($value1) => ({
  tag: "Pair",
  _1: $value0,
  _2: $value1
});
export function wrap(inner) {
  return { inner };
}
export function pair(a) {
  return {
    tag: "Pair",
    _1: a,
    _2: a
  };
}
export function newtypeGuard(section66) {
  if (section66.tag === "Just") {
    const { _1: n } = section66;
    const $scrutinee = wrap(n);
    const inner = $scrutinee.inner;
    return inner;
  }
  if (section66 === "Nothing") {
    return 0 | 0;
  }
  throw new Error("Pattern match failure");
}
export function singleConstructorGuard(section101) {
  if (section101.tag === "Just") {
    const { _1: n } = section101;
    const $scrutinee = pair(n);
    if ($scrutinee.tag === "Pair") {
      const { _1: a } = $scrutinee;
      return a;
    }
  }
  if (section101 === "Nothing") {
    return 0 | 0;
  }
  throw new Error("Pattern match failure");
}
export function recordGuard(section136) {
  if (section136.tag === "Just") {
    const { _1: n } = section136;
    const $scrutinee = { value: n };
    const value = $scrutinee.value;
    return value;
  }
  if (section136 === "Nothing") {
    return 0 | 0;
  }
  throw new Error("Pattern match failure");
}
export function refutableGuard(partialDict) {
  return (section163) => {
    return /* @__PURE__ */ ((partialDict$1) => {
      if (section163.tag === "Just") {
        const { _1: n } = section163;
        const $scrutinee = {
          tag: "Just",
          _1: n
        };
        if ($scrutinee.tag === "Just") {
          const { _1: m } = $scrutinee;
          return m;
        }
      }
      if (section163 === "Nothing") {
        return 0 | 0;
      }
      throw new Error("Pattern match failure");
    })(partialDict);
  };
}
