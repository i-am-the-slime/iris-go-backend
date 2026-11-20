export const now = () => Date.now();
export const elapsed = (since) => () => Date.now() - since;
