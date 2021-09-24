def main (args : List String) : IO UInt32 := do
  if args.isEmpty then
    IO.println "Lean C compiler

A simple wrapper around a C compiler. Defaults to `@LEANC_CC@`,
which can be overridden with the environment variable `LEAN_CC`. All parameters are passed
as-is to the wrapped compiler.

Interesting options:
* `-U LEAN_MULTI_THREAD` can be used to optimize programs not making use of multi-threading
* `--print-cflags`: print C compiler flags necessary for building against the Lean runtime and exit
* `--print-ldlags`: print C compiler flags necessary for statically linking against the Lean library and exit
* Set the `LEANC_GMP` environment variable to a path to `libgmp.a` (or `-l:libgmp.a` on Linux) to link GMP statically.
Beware of the licensing consequences since GMP is LGPL."
    return 1

  let binDir ← IO.appDir
  -- Zig gets confused by relative include paths on Windows
  let binDir ← IO.FS.realPath binDir
  let root := binDir.parent.get!
  -- We assume that the CMake variables do not contain escaped spaces
  let cflags := ["-I", (root / "include").toString] ++ "@LEANC_EXTRA_FLAGS@".trim.splitOn
  let mut ldflags := ["-L", (root / "lib").toString, "-L", (root / "lib" / "lean").toString, (← IO.getEnv "LEANC_GMP").getD "-lgmp"] ++ "@LEAN_EXTRA_LINKER_FLAGS@".trim.splitOn
  let mut ldflagsExt := "@LEANC_STATIC_LINKER_FLAGS@".trim.splitOn

  for arg in args do
    match arg with
    | "-shared" =>
      -- switch to shared linker flags
      ldflagsExt := "@LEANC_SHARED_LINKER_FLAGS@".trim.splitOn
    | "-c" =>
      ldflags := []
      ldflagsExt := []
    | "--print-cflags" =>
      IO.println <| " ".intercalate cflags
      return 0
    | "--print-ldflags" =>
      IO.println <| " ".intercalate (cflags ++ ldflagsExt ++ ldflags)
      return 0
    | _ => ()

  let mut cc := (← IO.getEnv "LEAN_CC").getD "@LEANC_CC@"
  if cc.startsWith "." then
    cc := (binDir / cc).toString

  let args := cflags ++ args ++ ldflagsExt ++ ldflags ++ ["-Wno-unused-command-line-argument"]
  if args.contains "-v" then
    IO.eprintln s!"{cc} {" ".intercalate args}"
  let child ← IO.Process.spawn { cmd := cc, args := args.toArray }
  child.wait
