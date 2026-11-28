export const handedOver = (value) => () => value;
export const twice = (thunk) => () => {
  thunk();
  return thunk();
};
export const log = (line) => () => console.log(line);
