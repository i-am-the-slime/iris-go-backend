export const empty = [];
export const snocImpl = (items, item) => [...items, item];
export const freeze = (items) => items;
export const length = (items) => items.length;
export const indexOrImpl = (fallback, index, items) =>
  index >= 0 && index < items.length ? items[index] : fallback;
export const describe = (value) => (typeof value === "number" ? "an int" : "something else");
