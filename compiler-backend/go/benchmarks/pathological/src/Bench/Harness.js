let started = 0;

export const startClock = (size) => () => {
  started = performance.now();
  return size;
};

export const stopClock = (_result) => () => performance.now() - started;

const environment = (name) =>
  typeof Deno !== "undefined" ? Deno.env.get(name) : process.env[name];

export const repetitionCount = () => {
  const configured = parseInt(environment("PATHO_REPETITIONS") ?? "", 10);
  return Number.isFinite(configured) && configured > 0 ? configured : 5;
};

export const startProfile = () => {};

export const stopProfile = () => {};

export const logTiming = (best) => (first) => () => {
  const line = `BENCH ${best.toFixed(3)} ${first.toFixed(3)}\n`;
  if (typeof Deno !== "undefined") Deno.stderr.writeSync(new TextEncoder().encode(line));
  else process.stderr.write(line);
};
