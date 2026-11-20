export const assertImpl = (message) => (success) => () => {
  if (!success) throw new Error(message);
};
