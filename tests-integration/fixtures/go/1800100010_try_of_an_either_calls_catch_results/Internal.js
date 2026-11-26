export const catchImpl = (handler) => (action) => () => {
  try {
    return action();
  } catch (failure) {
    return handler(failure)();
  }
};
