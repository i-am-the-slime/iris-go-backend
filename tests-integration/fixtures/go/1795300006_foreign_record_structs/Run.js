export const run = (program) => () => ({ stdout: program, stderr: "", exitCode: 0 });
export const runAll = (programs) => () => programs.map((program) => ({ stdout: program, stderr: "", exitCode: 0 }));
export const describe = (output) => output.stdout + "/" + output.exitCode;
