//! The native host's foreign imports: purescript-tauri's `Tauri.Native`
//! modules and the browser canvas and font APIs a native host lacks. Their Go
//! implementations live in go-support's `tauri` package; rendering surfaces,
//! video, terminal graphics and shared frames are reported there as
//! unsupported at run time.

use super::{Boundary, Foreign, GoFunction, GoPackage, PLAIN, RECORD};

const fn perform(name: &'static str, arity: usize) -> Foreign {
    host(name, arity, PLAIN)
}

const fn perform_record(name: &'static str, arity: usize) -> Foreign {
    host(name, arity, RECORD)
}

const fn host(name: &'static str, arity: usize, boundary: Boundary) -> Foreign {
    Foreign::Perform { function: GoFunction { package: GoPackage::Tauri, name }, arity, boundary }
}

const fn record_argument(name: &'static str, arity: usize, position: usize) -> Foreign {
    let boundary = Boundary {
        record_arguments: match position {
            0 => &[0],
            _ => &[1],
        },
        ..PLAIN
    };
    host(name, arity, boundary)
}

/// Every native canvas operation is the same unsupported call.
const fn canvas(arity: usize) -> Foreign {
    perform("Canvas", arity)
}

pub(super) const HOST_IMPORTS: &[(&str, &str, Foreign)] = &[
    ("Tauri.Native", "arguments", perform("Arguments", 0)),
    ("Tauri.Native", "version", perform("Version", 0)),
    ("Tauri.Native", "isStdinTTY", perform("IsStdinTTY", 0)),
    ("Tauri.Native", "readStdin", perform("ReadStdin", 0)),
    ("Tauri.Native", "readLineImpl", perform("ReadLineImpl", 0)),
    ("Tauri.Native", "readText", perform("ReadText", 1)),
    ("Tauri.Native", "readFileBase64", perform("ReadFileBase64", 1)),
    ("Tauri.Native", "writeText", perform("WriteText", 2)),
    ("Tauri.Native", "stdout", perform("Stdout", 1)),
    ("Tauri.Native", "stderr", perform("Stderr", 1)),
    ("Tauri.Native", "absolutePath", perform("AbsolutePath", 1)),
    ("Tauri.Native", "environment", perform("Environment", 1)),
    ("Tauri.Native", "monotonicMilliseconds", perform("MonotonicMilliseconds", 0)),
    ("Tauri.Native", "platform", perform("Platform", 0)),
    ("Tauri.Native", "runApplicationTaskImpl", perform_record("RunApplicationTaskImpl", 2)),
    ("Tauri.Native", "runApplicationImpl", perform_record("RunApplicationImpl", 2)),
    ("Tauri.Native", "measureText", perform_record("MeasureText", 2)),
    ("Tauri.Native", "beginVideo", record_argument("BeginVideo", 1, 0)),
    ("Tauri.Native", "writeVideoFrame", perform("WriteVideoFrame", 2)),
    ("Tauri.Native", "finishVideo", perform("FinishVideo", 1)),
    ("Tauri.Native", "cancelVideo", perform("CancelVideo", 1)),
    ("Tauri.Native", "enterTerminal", perform("EnterTerminal", 0)),
    ("Tauri.Native", "restoreTerminal", perform("RestoreTerminal", 0)),
    ("Tauri.Native", "terminalSize", perform_record("TerminalSize", 0)),
    ("Tauri.Native", "readKey", perform("ReadKey", 0)),
    ("Tauri.Native", "sleepMilliseconds", perform("SleepMilliseconds", 1)),
    (
        "Tauri.Native.TerminalGraphics",
        "inspectSize",
        perform_record("TerminalGraphicsInspectSize", 0),
    ),
    ("Tauri.Native.TerminalGraphics", "open", perform("TerminalGraphicsOpen", 0)),
    ("Tauri.Native.TerminalGraphics", "size", perform_record("TerminalGraphicsSize", 0)),
    ("Tauri.Native.TerminalGraphics", "present", record_argument("TerminalGraphicsPresent", 2, 1)),
    ("Tauri.Native.TerminalGraphics", "readKey", perform("TerminalGraphicsReadKey", 0)),
    ("Tauri.Native.TerminalGraphics", "close", perform("TerminalGraphicsClose", 0)),
    ("Tauri.Native.SharedFrame", "open", perform("SharedFrameOpen", 0)),
    ("Tauri.Native.SharedFrame", "capture", perform("SharedFrameCapture", 1)),
    (
        "Tauri.Native.SharedFrame",
        "info",
        Foreign::Call {
            function: GoFunction { package: GoPackage::Tauri, name: "SharedFrameInfo" },
            arity: 1,
            boundary: RECORD,
        },
    ),
    ("Tauri.Native.SharedFrame", "consumed", perform("SharedFrameConsumed", 1)),
    ("Tauri.Native.SharedFrame", "release", perform("SharedFrameRelease", 1)),
    ("Tauri.Native.SharedFrame", "close", perform("SharedFrameClose", 0)),
    ("Tauri.Native.Canvas", "createImpl", canvas(2)),
    ("Tauri.Native.Canvas", "release", canvas(1)),
    ("Tauri.Native.Canvas", "decodeImage", perform_record("CanvasDecodeImage", 1)),
    ("Tauri.Native.Canvas", "releaseImage", canvas(1)),
    ("Tauri.Native.Canvas", "drawImage", canvas(3)),
    ("Tauri.Native.Canvas", "reset", canvas(1)),
    ("Tauri.Native.Canvas", "clear", canvas(2)),
    ("Tauri.Native.Canvas", "save", canvas(1)),
    ("Tauri.Native.Canvas", "restore", canvas(1)),
    ("Tauri.Native.Canvas", "setTransform", canvas(2)),
    ("Tauri.Native.Canvas", "transform", canvas(2)),
    ("Tauri.Native.Canvas", "clip", canvas(3)),
    ("Tauri.Native.Canvas", "setBlend", canvas(2)),
    ("Tauri.Native.Canvas", "setBlur", canvas(2)),
    ("Tauri.Native.Canvas", "setTintImpl", canvas(2)),
    ("Tauri.Native.Canvas", "fillPath", canvas(3)),
    ("Tauri.Native.Canvas", "strokePath", canvas(3)),
    ("Tauri.Native.Canvas", "fillStrokePath", canvas(4)),
    ("Tauri.Native.Canvas", "text", canvas(2)),
    ("Tauri.Native.Canvas", "circlePattern", canvas(2)),
    ("Tauri.Native.Canvas", "surface", canvas(2)),
    ("Tauri.Native.Canvas", "writePng", canvas(2)),
    ("Graphics.Canvas", "setFont", canvas(2)),
    ("Graphics.Canvas.Extra", "supportsOffscreenCanvas", perform("SupportsOffscreenCanvas", 0)),
    ("Graphics.Canvas.Extra", "supportsCanvasElement", perform("SupportsCanvasElement", 0)),
    ("Graphics.Canvas.Extra", "createCanvasElementImpl", canvas(0)),
    ("Graphics.Canvas.Extra", "createOffscreenCanvasImpl", canvas(2)),
    ("Graphics.Canvas.Extra", "getContext2DNullable", perform("GetContext2DNullable", 1)),
    ("Graphics.Canvas.Extra", "setFontKerningImpl", canvas(2)),
    ("Graphics.Canvas.Extra", "measureTextInkImpl", perform_record("MeasureTextInkImpl", 2)),
    ("Web.Font.Loading", "hasFontSet", perform("HasFontSet", 0)),
    ("Web.Font.Loading", "supportsFontFace", perform("SupportsFontFace", 0)),
    ("Web.Font.Loading", "checkFont", perform("CheckFont", 1)),
    ("Web.Font.Loading", "loadFontImpl", perform("LoadFontImpl", 1)),
    ("Web.Font.Loading", "fontsReadyImpl", perform("FontsReadyImpl", 0)),
];

/// Host handles that Go code only passes back to the host: surfaces, images,
/// video encoders, frames and browser canvas objects.
pub fn is_opaque_foreign_data(module_name: &str, name: &str) -> bool {
    matches!(
        (module_name, name),
        ("Tauri.Native", "Video")
            | ("Tauri.Native.Canvas", "Surface" | "Image")
            | ("Tauri.Native.SharedFrame", "Frame")
            | (
                "Graphics.Canvas",
                "CanvasElement"
                    | "Context2D"
                    | "ImageData"
                    | "CanvasImageSource"
                    | "CanvasPattern"
                    | "CanvasGradient"
            )
            | ("Web.Font.Loading", "FontFace")
    )
}
