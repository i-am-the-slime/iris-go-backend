export const empty = () => new Map();
export const lookupImpl = (just) => (nothing) => (key) => (entries) => () =>
  entries.has(key) ? just(entries.get(key)) : nothing;
export const insert = (key) => (value) => (entries) => () => {
  entries.set(key, value);
};
export const values = (entries) => () =>
  [...entries.keys()].sort((left, right) => (left < right ? -1 : left > right ? 1 : 0)).map((key) => entries.get(key));
