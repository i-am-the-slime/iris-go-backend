// Compares two files that may differ only in the last digits of their numbers:
// everything outside numbers must be identical, and two numbers count as equal
// when they differ by at most TOLERANCE relative to the larger. Go's math package
// and the JavaScript engines round transcendental functions differently in the
// last ulp, and that difference is documented, not a bug. Exit 0 when close,
// 1 when not; prints the largest relative difference seen.
//
//   bun float-close.ts a.svg b.svg [tolerance]

const [left, right, given] = Bun.argv.slice(2);
const tolerance = Number(given ?? "1e-9");
const number = /-?(?:\d+\.?\d*|\.\d+)(?:[eE][+-]?\d+)?/g;
const a = await Bun.file(left).text();
const b = await Bun.file(right).text();
const split = (text: string) => ({ text: text.split(number), numbers: text.match(number) ?? [] });
const x = split(a), y = split(b);
let worst = 0;
let close = x.text.length === y.text.length && x.numbers.length === y.numbers.length
  && x.text.every((part, i) => part === y.text[i]);
for (let i = 0; close && i < x.numbers.length; i++) {
  if (x.numbers[i] === y.numbers[i]) continue;
  const p = Number(x.numbers[i]), q = Number(y.numbers[i]);
  const relative = Math.abs(p - q) / Math.max(Math.abs(p), Math.abs(q), 1e-300);
  worst = Math.max(worst, relative);
  close = relative <= tolerance;
}
console.log(close ? `close (largest relative difference ${worst})` : `different (at relative ${worst})`);
process.exit(close ? 0 : 1);
