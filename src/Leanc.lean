/-
Copyright (c) 2022 Sebastian Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
import Lean.Compiler.FFI

open Lean.Compiler.FFI

def main (args : List String) : IO UInt32 := do
  let root ← match (← IO.getEnv "LEAN_SYSROOT") with
    | some root => pure <| System.FilePath.mk root
    | none      => pure <| (← IO.appDir).parent.get!
  let mut cc := "@LEANC_CC@".replace "ROOT" root.toString
  let wasmTarget := "--target=wasm32-wasip1"

  if args.contains wasmTarget then
    let sdk ← match ← IO.getEnv "WASI_SDK_PATH" with
      | some sdk => pure <| System.FilePath.mk sdk
      | none =>
        IO.eprintln "leanc: set WASI_SDK_PATH to an extracted wasi-sdk toolchain"
        return 1
    let runtime := root / "wasm32-wasip1" / "libleanrt.a"
    unless ← runtime.pathExists do
      IO.eprintln s!"leanc: WebAssembly runtime archive not found at '{runtime}'"
      return 1
    let args := args.filter fun arg => arg != wasmTarget && !arg.startsWith "--root-module="
    -- Core language runtime only (no IO/libuv). Exception flag must match `build_wasm_runtime.sh`.
    -- Prefer libc++/libc++abi over libunwind: recent wasi-sdk drops libunwind, and we ship
    -- aborting `__cxa_*` stubs in `wasm_support.cpp` when the sysroot lacks them.
    let args := args.toArray ++ #["-fwasm-exceptions",
      "-mexec-model=reactor", "-Wl,--no-entry", runtime.toString, "-lc++", "-lc++abi"]
    let child ← IO.Process.spawn { cmd := (sdk / "bin" / "clang++").toString, args }
    return ← child.wait

  if args.isEmpty then
    IO.println s!"Lean C compiler

A simple wrapper around a C compiler. Defaults to `{cc}`,
which can be overridden with the environment variable `LEAN_CC`. All parameters are passed
as-is to the wrapped compiler.

Interesting options:
* `--print-cflags`: print C compiler flags necessary for building against the Lean runtime and exit
* `--print-ldflags`: print C compiler flags necessary for statically linking against the Lean library and exit
* `--target=wasm32-wasip1`: link WebAssembly objects with the language-core Lean runtime"
    return 1

  -- It is difficult to identify the correct minor version here, leading to linking warnings like:
  -- `ld64.lld: warning: /usr/lib/system/libsystem_kernel.dylib has version 13.5.0, which is newer than target minimum of 13.0.0`
  -- In order to suppress these we set the MACOSX_DEPLOYMENT_TARGET variable into the far future.
  let env := match (← IO.getEnv "MACOSX_DEPLOYMENT_TARGET") with
    | some _ => #[]
    | none   => #[("MACOSX_DEPLOYMENT_TARGET", "99.0")]

  -- let compileOnly := args.contains "-c"
  let linkStatic := !(args.contains "-shared" || args.contains "-leanshared")
  let args := args.erase "-leanshared"

  -- We assume that the CMake variables do not contain escaped spaces
  let cflags := getCFlags root
  let mut cflagsInternal := getInternalCFlags root
  let mut ldflagsInternal := getInternalLinkerFlags root
  let mut ldflags := getLinkerFlags root linkStatic
  if System.Platform.isWindows && !args.contains "-shared" then
    ldflags := ldflags ++ #["-Wl,--whole-archive", "-lleanmanifest", "-Wl,--no-whole-archive"]

  for arg in args do
    match arg with
    | "--print-cflags" =>
      IO.println <| " ".intercalate cflags.toList
      return 0
    | "--print-ldflags" =>
      IO.println <| " ".intercalate (cflags ++ ldflags).toList
      return 0
    | _ => pure ()

  if let some cc' ← IO.getEnv "LEAN_CC" then
    cc := cc'
    -- these are intended for the bundled compiler only
    cflagsInternal := #[]
    ldflagsInternal := #[]
  let args := cflags ++ cflagsInternal ++ args ++ ldflagsInternal ++ ldflags ++ ["-Wno-unused-command-line-argument"]
  let args := args.filter (!·.isEmpty)
  if args.contains "-v" then
    IO.eprintln s!"{cc} {" ".intercalate args.toList}"
  let child ← IO.Process.spawn { cmd := cc, args, env }
  child.wait
