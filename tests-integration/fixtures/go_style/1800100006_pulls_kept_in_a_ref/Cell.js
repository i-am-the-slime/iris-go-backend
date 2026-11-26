export const new_ = (value) => () => ({ value });
export { new_ as new };
export const read = (ref) => () => ref.value;
export const write = (ref) => (value) => () => {
  ref.value = value;
};
