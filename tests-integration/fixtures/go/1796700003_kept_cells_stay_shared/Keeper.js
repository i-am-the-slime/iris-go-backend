let stored;
export const keep = (value) => {
  stored = value;
  return 1;
};
export const kept = () => stored;
