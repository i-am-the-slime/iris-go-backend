export const absent = undefined;
export const present = (value) => value;
export const withDefault = (fallback) => (optional) => optional === undefined ? fallback : optional;
export const emptyArray = [];
export const swappedPair = (a) => (b) => [b, a];
export const emptySwappedPair = [];
export const pairSize = (pair) => pair.length;
export const newCounter = () => undefined;
