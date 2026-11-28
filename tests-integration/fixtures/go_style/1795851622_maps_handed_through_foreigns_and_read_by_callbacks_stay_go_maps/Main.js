export const handedOver = (value) => () => value;
export const twice = (thunk) => () => {
  thunk();
  return thunk();
};
