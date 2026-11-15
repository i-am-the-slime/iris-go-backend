let started = 0;

// PATHO_SIZE replaces the benchmark's size, so that scripts/robust/scaling.sh can time it at n, 2n and 4n.
export const startClock = (size) => () => {
  const configured = parseInt(environment("PATHO_SIZE") ?? "", 10);
  started = performance.now();
  return Number.isFinite(configured) && configured > 0 ? configured : size;
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
