export const serve = (route) => () => {
  route.handle("world", "hi", {});
  route.done(route.path);
  route.prefixed("p")("x", {});
};
export const call = (handle) => () => handle("a", "b", {});
export const builtIn = { path: "/built-in", handle: () => {}, done: () => {}, prefixed: () => () => {} };
export const noReply = {};
