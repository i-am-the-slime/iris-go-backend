export const performImpl = (effect) => () => effect();
export const guardedImpl = (handler) => (action) => () => action();
export const combineImpl = (combine) => (left) => (right) => () => combine(left())(right());
export const modifyImpl = (f) => (result) => () => result(f(41));
