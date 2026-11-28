export const timed = (thunk) => () => thunk();
export const log = (line) => () => console.log(line);
