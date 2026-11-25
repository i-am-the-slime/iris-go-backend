export const outcomeImpl = (failed, finished, succeeded) => succeeded ? finished : failed(7)("connection reset");
