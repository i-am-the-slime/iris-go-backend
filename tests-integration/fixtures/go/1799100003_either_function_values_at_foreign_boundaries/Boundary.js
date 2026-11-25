export const repeatImpl = (times) => (action) => () => {
  const results = [];
  for (let i = 0; i < times; i++) results.push(action());
  return results;
};
export const keepImpl = (value) => () => value;
