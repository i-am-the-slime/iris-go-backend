export const onAnotherGoroutine = (callback) => () => {
  setTimeout(callback, 0);
};
