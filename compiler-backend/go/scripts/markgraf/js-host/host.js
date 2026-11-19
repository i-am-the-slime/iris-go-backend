// `globalThis.__purescriptNativeHost` for Deno (V8) and Bun (JavaScriptCore),
// so that they run the same engine.js as the Tauri native host
// (purescript-tauri/native/runtime, macOS jsc.rs) and must print the same bytes.
//
//   deno run -A --allow-ffi host.js ENGINE MEASURE_LIBRARY -- ARGS...
//   bun host.js ENGINE MEASURE_LIBRARY -- ARGS...
//
// Each primitive mirrors the Rust one, including its error messages. Text is
// measured by the host's own Rust code through MEASURE_LIBRARY
// (build-js-measure.sh), so the FFI crossing is part of the measured time, as
// the Tauri host's crossing is. Primitives the SVG export does not reach throw
// a loud error rather than pretending.

import fs from "node:fs";
import path from "node:path";
import process from "node:process";
import tty from "node:tty";

const started = performance.now();
const [engine, measureLibrary, separator, ...cliArguments] = process.argv.slice(2);
if (!engine || !measureLibrary || separator !== "--") {
  process.stderr.write("usage: host.js ENGINE MEASURE_LIBRARY -- ARGS...\n");
  process.exit(2);
}

const native = await loadNative(measureLibrary);
if (typeof Deno !== "undefined") useCMathLibrary();
const encoder = new TextEncoder();
const utf8 = new TextDecoder("utf-8", { fatal: true, ignoreBOM: true });
const metrics = new Float64Array(3);
const standardInput = { buffered: new Uint8Array(0), ended: false };

const primitives = {
  arguments: () => [...cliArguments],
  // option_env!("MARKGRAF_VERSION") is unset when build-js-cli.sh compiles the reference.
  version: () => "dev",
  isStdinTTY: () => tty.isatty(0),
  readStdin: () => decode(io(() => readAllStandardInput())),
  readLine: () => readLine(),
  readText: (file) => decode(io(() => fs.readFileSync(string(file)))),
  readFileBase64: (file) => io(() => fs.readFileSync(string(file))).toString("base64"),
  writeText: (file, text) => { io(() => fs.writeFileSync(string(file), encoder.encode(string(text)))); },
  stdout: (text) => { writeAll(1, string(text)); },
  stderr: (text) => { writeAll(2, string(text)); },
  absolutePath: (file) => absolutePath(string(file)),
  environment: (name) => environment(string(name)),
  monotonicMilliseconds: () => performance.now() - started,
  platform: () => ({ darwin: "macos", win32: "windows" })[process.platform] ?? process.platform,
  measureText: (font, text) => native.measure(string(font), string(text)),
  sleepMilliseconds: (milliseconds) => sleep(milliseconds),
};

globalThis.__purescriptNativeHost = {
  call(name, ...args) {
    if (typeof name !== "string") throw new TypeError("native argument must be a string");
    const primitive = primitives[name];
    if (!primitive) throw new Error(`${name} is not provided by the ${runtime()} baseline host (js-host/host.js)`);
    return primitive(...args);
  },
};

process.exit(await main());

async function main() {
  try {
    await import(path.resolve(engine));
    const run = globalThis.__purescriptMain;
    if (typeof run !== "function") throw new TypeError("__purescriptMain must be a function");
    const status = run();
    if (typeof status !== "number" || !Number.isInteger(status) || status < -2147483648 || status > 2147483647) {
      throw new TypeError("__purescriptMain must return an integer exit status");
    }
    return Math.min(Math.max(status, 0), 255);
  } catch (error) {
    // main.rs: eprintln!("markgraf: {error}") with jsc.rs's exception_string.
    writeAll(2, `markgraf: ${exceptionString(error)}\n`);
    return 1;
  }
}

function exceptionString(value) {
  const description = String(value);
  const stack = value !== null && typeof value === "object" ? value.stack : undefined;
  return typeof stack === "string" && stack !== "" && !stack.startsWith(description)
    ? `${description}\n${stack}`
    : description;
}

function string(value) {
  if (typeof value !== "string") throw new TypeError("native argument must be a string");
  return value;
}

// std::io::Error's Display for an OS error, e.g. "No such file or directory (os error 2)".
function io(operation) {
  try {
    return operation();
  } catch (error) {
    if (typeof error?.errno === "number") throw new Error(native.osError(Math.abs(error.errno)));
    throw error;
  }
}

// String::from_utf8 as read_to_string reports it; a BOM is kept, as Rust keeps it.
function decode(bytes) {
  try {
    return utf8.decode(bytes);
  } catch {
    throw new Error("stream did not contain valid UTF-8");
  }
}

function writeAll(descriptor, text) {
  const bytes = encoder.encode(text);
  let written = 0;
  while (written < bytes.length) written += io(() => fs.writeSync(descriptor, bytes, written));
}

// std::path::absolute on POSIX: no symlink resolution, `..` kept, `.` and
// repeated separators dropped, a trailing separator kept.
function absolutePath(file) {
  if (file === "") throw new Error("cannot make an empty path absolute");
  const components = file.split("/").filter((part) => part !== "" && part !== ".");
  const base = !file.startsWith("/") ? io(() => process.cwd())
    : file.startsWith("//") && !file.startsWith("///") ? "//" : "/";
  const joined = components.reduce(push, base);
  return file.endsWith("/") ? push(joined, "") : joined;

  function push(directory, part) {
    return directory.endsWith("/") ? directory + part : `${directory}/${part}`;
  }
}

// std::env::var(name).unwrap_or_default()
function environment(name) {
  try {
    if (name === "" || name.includes("=") || name.includes("\0")) return "";
    return process.env[name] ?? "";
  } catch {
    return "";
  }
}

function sleep(milliseconds) {
  if (typeof milliseconds !== "number") throw new TypeError("native argument must be a number");
  if (milliseconds < 0) throw new Error("sleep duration must not be negative");
  Atomics.wait(new Int32Array(new SharedArrayBuffer(4)), 0, 0, milliseconds);
}

function readAllStandardInput() {
  const chunks = [standardInput.buffered];
  standardInput.buffered = new Uint8Array(0);
  while (!standardInput.ended) chunks.push(readStandardInputChunk());
  return Buffer.concat(chunks);
}

function readLine() {
  for (;;) {
    const newline = standardInput.buffered.indexOf(10);
    if (newline >= 0 || standardInput.ended) {
      const end = newline >= 0 ? newline + 1 : standardInput.buffered.length;
      if (end === 0) return undefined;
      const line = decode(standardInput.buffered.subarray(0, end));
      standardInput.buffered = standardInput.buffered.subarray(end);
      return line.endsWith("\r\n") ? line.slice(0, -2) : line.endsWith("\n") ? line.slice(0, -1) : line;
    }
    standardInput.buffered = Buffer.concat([standardInput.buffered, readStandardInputChunk()]);
  }
}

function readStandardInputChunk() {
  const chunk = Buffer.alloc(65536);
  const count = io(() => fs.readSync(0, chunk, 0, chunk.length, null));
  if (count === 0) standardInput.ended = true;
  return chunk.subarray(0, count);
}

function runtime() {
  return typeof Deno !== "undefined" ? "Deno" : typeof Bun !== "undefined" ? "Bun" : "JavaScript";
}

// ECMAScript leaves Math's transcendental functions implementation-approximated.
// JavaScriptCore takes them from the C library; V8 has its own port of fdlibm,
// which differs in the last bit for some arguments (sin, cos, tan, acos, atan2,
// exp and log all do on the Markgraf examples). V8
// calls the C library here, so that Deno computes the reference's numbers.
// Math.pow follows JavaScriptCore's operationMathPow, which squares and
// multiplies for integer exponents 0..1000 (0.9 ** 4 is 0.6561000000000001,
// not V8's 0.6561) and takes 1 / sqrt(x) for an exponent of -0.5.
function useCMathLibrary() {
  const unary = ["sin", "cos", "tan", "exp", "log", "acos"];
  const library = Deno.build.os === "darwin" ? "/usr/lib/libSystem.B.dylib" : "libm.so.6";
  const { symbols } = Deno.dlopen(library, {
    ...Object.fromEntries(unary.map((name) => [name, { parameters: ["f64"], result: "f64" }])),
    atan2: { parameters: ["f64", "f64"], result: "f64" },
    pow: { parameters: ["f64", "f64"], result: "f64" },
  });
  for (const name of unary) {
    const call = symbols[name];
    Math[name] = (x) => call(+x);
  }
  const atan2 = symbols.atan2;
  Math.atan2 = (y, x) => atan2(+y, +x);
  const pow = symbols.pow;
  Math.pow = (base, exponent) => javaScriptCorePow(+base, +exponent);

  function javaScriptCorePow(x, y) {
    if (Number.isNaN(y)) return NaN;
    if (Math.abs(x) === 1 && !Number.isFinite(y)) return NaN;
    if (y === 0.5) return x === 0 ? 0 : x === -Infinity ? Infinity : Math.sqrt(x);
    if (y === -0.5) return x === 0 ? Infinity : !Number.isFinite(x) ? 0 : 1 / Math.sqrt(x);
    if (Number.isInteger(y) && y >= 0 && y <= 1000) {
      let result = 1;
      for (let n = y; n !== 0; n >>= 1) {
        if (n & 1) result *= x;
        x *= x;
      }
      return result;
    }
    return pow(x, y);
  }
}

// markgraf_measure_text and markgraf_os_error from build-js-measure.sh's library.
async function loadNative(library) {
  const fontBuffer = { bytes: new Uint8Array(256) };
  const textBuffer = { bytes: new Uint8Array(1024) };
  const encodeInto = (buffer, text) => {
    if (buffer.bytes.length < text.length * 3) buffer.bytes = new Uint8Array(text.length * 3);
    return encoder.encodeInto(text, buffer.bytes).written;
  };
  const result = () => ({ width: metrics[0], ascent: metrics[1], descent: metrics[2] });

  if (typeof Deno !== "undefined") {
    const { symbols } = Deno.dlopen(library, {
      markgraf_measure_text: { parameters: ["buffer", "usize", "buffer", "usize", "buffer"], result: "pointer" },
      markgraf_os_error: { parameters: ["i32"], result: "pointer" },
    });
    const message = (pointer) => Deno.UnsafePointerView.getCString(pointer);
    return {
      measure(font, text) {
        const fontLength = encodeInto(fontBuffer, font);
        const textLength = encodeInto(textBuffer, text);
        const failure = symbols.markgraf_measure_text(fontBuffer.bytes, fontLength, textBuffer.bytes, textLength, metrics);
        if (failure !== null) throw new Error(message(failure));
        return result();
      },
      osError: (code) => message(symbols.markgraf_os_error(code)),
    };
  }

  const { dlopen, FFIType, CString } = await import("bun:ffi");
  const { symbols } = dlopen(library, {
    markgraf_measure_text: {
      args: [FFIType.ptr, FFIType.u64_fast, FFIType.ptr, FFIType.u64_fast, FFIType.ptr],
      returns: FFIType.ptr,
    },
    markgraf_os_error: { args: [FFIType.i32], returns: FFIType.ptr },
  });
  return {
    measure(font, text) {
      const fontLength = encodeInto(fontBuffer, font);
      const textLength = encodeInto(textBuffer, text);
      const failure = symbols.markgraf_measure_text(fontBuffer.bytes, fontLength, textBuffer.bytes, textLength, metrics);
      if (failure !== null && failure !== 0) throw new Error(String(new CString(failure)));
      return result();
    },
    osError: (code) => String(new CString(symbols.markgraf_os_error(code))),
  };
}
