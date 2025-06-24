/-
Copyright (c) 2025 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mac Malone
-/
prelude
import Lean.Elab.Frontend
import Lean.Elab.ParseImportsFast
import Lean.Compiler.IR.EmitC

/-  Lean companion to  `shell.cpp` -/

open System

namespace Lean

/--
Decodes an array of bytes that encode a string as [UTF-8](https://en.wikipedia.org/wiki/UTF-8) into
the corresponding string. Invalid UTF-8 characters in the byte array are replaced with `U+FFFD`
(the unicode replacement character) in the resulting string.

This is used instead of the standard `String` functions because Lean is expected to not immediately
abort on files with invalid UTF-8.
-/
@[extern "lean_decode_lossy_utf8"]
private opaque decodeLossyUTF8 (a : @& ByteArray) : String

/- Runs the `main` function of the module with `args` using the Lean interpreter. -/
@[extern "lean_run_main"]
private opaque runMain (env : @& Environment) (opts : @& Options) (args : @& List String) : BaseIO UInt32

/--
Initializes the LLVM subsystem.
If Lean lacks LLVM support, this function will fail with an assertion violation.
-/
@[extern "lean_init_llvm"]
private opaque initLLVM : IO Unit

/--
Emits LLVM bitcode for the module.
Before calling this function, the LLVM subsystem must first be successfully initialized.
-/
@[extern "lean_emit_llvm"]
private opaque emitLLVM (env : Environment) (modName : Name) (filepath : FilePath) : IO Unit

/-- Print all profiling times (if any) to standard error. -/
@[extern "lean_display_cumulative_profiling_times"]
private opaque displayCumulativeProfilingTimes : BaseIO Unit

/-- Whether Lean was built with an address sanitizer enabled. -/
@[extern "lean_internal_has_address_sanitizer"]
private opaque Internal.hasAddressSanitizer (_ : Unit) : Bool

/-- Whether Lean was built with multithread support. -/
@[extern "lean_internal_is_multi_thread"]
private opaque Internal.isMultiThread (_ : Unit) : Bool

/-- Whether Lean was built in debug mode. -/
@[extern "lean_internal_is_debug"]
private opaque Internal.isDebug (_ : Unit) : Bool

/-- The mode Lean was built in. -/
@[extern "lean_internal_get_build_type"]
private opaque Internal.getBuildType (_ : Unit) : String

/-- Lean equivalent of `LEAN_VERSION_STRING` / `g_short_version_string` -/
private def shortVersionString : String :=
  if version.specialDesc ≠ "" then
    s!"{versionStringCore}-{version.specialDesc}"
  else if !version.isRelease then
    s!"{versionStringCore}-pre"
  else
    versionStringCore

/-- The full Lean version header (i.e, what is printed by `lean --version`). -/
private def versionHeader : String := Id.run do
  let mut ver := shortVersionString
  if Platform.target ≠ "" then
    ver := s!"{ver}, {Platform.target}"
  if githash ≠ "" then
    ver := s!"{ver}, commit {githash}"
  s!"Lean (version {ver}, {Internal.getBuildType ()})"

/-- Print the Lean version header. -/
@[export lean_display_header]
private def displayHeader : IO Unit := do
  IO.println versionHeader

/-- Print the Lean CLI help message. -/
@[export lean_display_help]
private def displayHelp (useStderr : Bool) : IO Unit := do
  let out ← if useStderr then IO.getStderr else IO.getStdout
  out.putStrLn    versionHeader
  out.putStrLn    "Miscellaneous"
  out.putStrLn    "  -h, --help             display this message"
  out.putStrLn    "      --features         display features compiler provides (eg. LLVM support)"
  out.putStrLn    "  -v, --version          display version information"
  out.putStrLn    "  -V, --short-version    display short version number"
  out.putStrLn    "  -g, --githash          display the git commit hash number used to build this binary"
  out.putStrLn    "      --run <file>       call the 'main' definition in the given file with the remaining arguments"
  out.putStrLn    "  -o, --o=oname          create olean file"
  out.putStrLn    "  -i, --i=iname          create ilean file"
  out.putStrLn    "  -c, --c=fname          name of the C output file"
  out.putStrLn    "  -b, --bc=fname         name of the LLVM bitcode file"
  out.putStrLn    "      --stdin            take input from stdin"
  out.putStrLn    "      --root=dir         set package root directory from which the module name\n"
  out.putStrLn    "                         of the input file is calculated\n"
  out.putStrLn    "                         (default: current working directory)\n";
  out.putStrLn    "  -t, --trust=num        trust level (default: max) 0 means do not trust any macro,\n"
  out.putStrLn    "                         and type check all imported modules\n";
  out.putStrLn    "  -q, --quiet            do not print verbose messages"
  out.putStrLn    "  -M, --memory=num       maximum amount of memory that should be used by Lean"
  out.putStrLn    "                         (in megabytes)"
  out.putStrLn    "  -T, --timeout=num      maximum number of memory allocations per task"
  out.putStrLn    "                         this is a deterministic way of interrupting long running tasks"
  if Internal.isMultiThread () then
    out.putStrLn  "  -j, --threads=num      number of threads used to process lean files"
    out.putStrLn  "  -s, --tstack=num       thread stack size in Kb"
    out.putStrLn  "      --server           start lean in server mode"
    out.putStrLn  "      --worker           start lean in server-worker mode"
  out.putStrLn    "      --plugin=file      load and initialize Lean shared library for registering linters etc."
  out.putStrLn    "      --load-dynlib=file load shared library to make its symbols available to the interpreter"
  out.putStrLn    "      --setup=file       JSON file with module setup data (supersedes the file's header)"
  out.putStrLn    "      --json             report Lean output (e.g., messages) as JSON (one per line)"
  out.putStrLn    "  -E  --error=kind       report Lean messages of kind as errors"
  out.putStrLn    "      --deps             just print dependencies of a Lean input"
  out.putStrLn    "      --src-deps         just print dependency sources of a Lean input"
  out.putStrLn    "      --print-prefix     print the installation prefix for Lean and exit"
  out.putStrLn    "      --print-libdir     print the installation directory for Lean's built-in libraries and exit"
  out.putStrLn    "      --profile          display elaboration/type checking time for each definition/theorem"
  out.putStrLn    "      --stats            display environment statistics"
  if Internal.isDebug () then
    out.putStrLn  "      --debug=tag        enable assertions with the given tag"
  out.putStrLn    "      -D name=value      set a configuration option (see set_option command)"

@[export lean_shell_main]
private def shellMain
    (args : List String)
    (useStdin : Bool := false)
    (onlyDeps : Bool := false)
    (onlySrcDeps : Bool := false)
    (depsJson : Bool := false)
    (opts : Options := {})
    (trustLevel : UInt32 := 0)
    (rootDir? : Option System.FilePath := none)
    (setupFileName? : Option System.FilePath := none)
    (oleanFileName? : Option System.FilePath := none)
    (ileanFileName? : Option System.FilePath := none)
    (cFileName? : Option System.FilePath := none)
    (bcFileName? : Option System.FilePath := none)
    (jsonOutput : Bool := false)
    (errorOnKinds : Array Name := #[])
    (printStats : Bool := false)
    (run : Bool := false)
    : IO UInt32 := do
  if onlyDeps && depsJson then
    let fns ←
      if useStdin then
        (← IO.getStdin).lines
      else
        pure args.toArray
    printImportsJson fns
    return 0
  let (fileName?, args) :=
    match args with
    | fileName :: args => (some fileName, args)
    | [] => (none, args)
  if !run && !args.isEmpty then
    IO.eprintln "Expected exactly one file name"
    displayHelp (useStderr := true)
    return 1
  let fileName ←
    if let some fileName := fileName? then
      pure fileName
    else if useStdin then
      pure "<stdin>"
    else
      IO.eprintln "Expected exactly one file name"
      displayHelp (useStderr := true)
      return 1
  let contents ← decodeLossyUTF8 <$> do
    if useStdin then
      (← IO.getStdin).readBinToEnd
    else
      IO.FS.readBinFile fileName
  if onlyDeps then
    Elab.printImports contents fileName
    return 0
  if onlySrcDeps then
    Elab.printImportSrcs contents fileName
    return 0
  -- Quick and dirty `#lang` support
  ---TODO: make it extensible, and add `lean4md`
  let contents ←
    if contents.startsWith "#lang" then
      let endLinePos := contents.posOf '\n'
      let langId := contents.extract ⟨6⟩ endLinePos |>.trim
      if langId == "lean4" then
        pure () -- do nothing for now
      else
        IO.eprintln s!"unknown language '{langId}'\n";
        return 1
      -- Remove up to `\n`
      pure <| contents.extract endLinePos contents.endPos
    else
      pure contents
  let setup? ← setupFileName?.mapM ModuleSetup.load
  let mainModuleName ←
    if let some setup := setup? then
      pure setup.name
    else if let some fileName := fileName? then
      try moduleNameOfFileName fileName rootDir? catch e =>
        if oleanFileName?.isNone && ileanFileName?.isNone then
          pure `_stdin
        else
          throw e
    else
      pure `_stdin
  let env? ← Elab.runFrontend contents opts fileName mainModuleName trustLevel
      oleanFileName? ileanFileName? jsonOutput errorOnKinds #[] printStats setup?
  if let some env := env? then
    if run then
      return ← runMain env opts args
    if let some c := cFileName? then
      let .ok out ← IO.FS.Handle.mk c .write |>.toBaseIO
        | IO.eprintln s!"failed to create '{c}'"
          return 1
      profileitIO "C code generation" opts do
        let data ← IO.ofExcept <| IR.emitC env mainModuleName
        out.write data.toUTF8
    if let some bc := bcFileName? then
      initLLVM
      profileitIO "LLVM code generation" opts do
        emitLLVM env mainModuleName bc
  displayCumulativeProfilingTimes
  if Internal.hasAddressSanitizer () then
    return if env?.isSome then 0 else 1
  else
    -- When not using the address/leak sanitizer, we interrupt execution without garbage collecting.
    -- This is useful when profiling improvements to Lean startup time.
    IO.Process.exit <| if env?.isSome then 0 else 1
