import Lean.Compiler.FFI

open Lean.Compiler.FFI

def main (args : List String) : IO UInt32 := do
  if args.isEmpty then
    IO.println "Lean C compiler

A simple wrapper around a C compiler. Defaults to `@LEANC_CC@`,
which can be overridden with the environment variable `LEAN_CC`. All parameters are passed
as-is to the wrapped compiler.

Interesting options:
* `--print-cflags`: print C compiler flags necessary for building against the Lean runtime and exit
* `--print-ldflags`: print C compiler flags necessary for statically linking against the Lean library and exit"
    return 1

  let root ← match (← IO.getEnv "LEAN_SYSROOT") with
    | some root => pure <| System.FilePath.mk root
    | none      => pure <| (← IO.appDir).parent.get!
  let rootify s := s.replace "ROOT" root.toString

  -- let compileOnly := args.contains "-c"
  let linkStatic := !args.contains "-shared"

  -- We assume that the CMake variables do not contain escaped spaces
  let cflags := getCFlags root
  let mut cflagsInternal := "@LEANC_INTERNAL_FLAGS@".trim.splitOn
  let mut ldflagsInternal := "@LEANC_INTERNAL_LINKER_FLAGS@".trim.splitOn
  let ldflags := getLinkerFlags root linkStatic

  for arg in args do
    match arg with
    | "--print-cflags" =>
      IO.println <| " ".intercalate (cflags.map rootify |>.toList)
      return 0
    | "--print-ldflags" =>
      IO.println <| " ".intercalate ((cflags ++ ldflags).map rootify |>.toList)
      return 0
    | _ => pure ()

  let mut cc := "@LEANC_CC@"
  if let some cc' ← IO.getEnv "LEAN_CC" then
    cc := cc'
    -- these are intended for the bundled compiler only
    cflagsInternal := []
    ldflagsInternal := []
  cc := rootify cc
  let args := cflags ++ cflagsInternal ++ args ++ ldflagsInternal ++ ldflags ++ ["-Wno-unused-command-line-argument"]
  let args := args.filter (!·.isEmpty) |>.map rootify
  if args.contains "-v" then
    IO.eprintln s!"{cc} {" ".intercalate args.toList}"
  let child ← IO.Process.spawn { cmd := cc, args }
  child.wait
