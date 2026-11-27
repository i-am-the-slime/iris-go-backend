export const newPipe = (value) => ({ value });
export const onTake = (pipe) => (taken) => () => taken(pipe.value, true);
export const leaked = (_pipe) => 1;
