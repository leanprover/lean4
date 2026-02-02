/-
Copyright (c) 2025 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mac Malone
-/
module

prelude
import Lean.Elab.Frontend
import Lean.Elab.ParseImportsFast
import Lean.Server.Watchdog
import Lean.Server.FileWorker
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
opaque decodeLossyUTF8 (a : @& ByteArray) : String

/- Runs the `main` function of the module with `args` using the Lean interpreter. -/
@[extern "lean_run_main"]
opaque runMain (env : @& Environment) (opts : @& Options) (args : @& List String) : BaseIO UInt32

/--
Initializes the LLVM subsystem.
If Lean lacks LLVM support, this function will fail with an assertion violation.
-/
@[extern "lean_init_llvm"]
opaque initLLVM : IO Unit

/--
Emits LLVM bitcode for the module.
Before calling this function, the LLVM subsystem must first be successfully initialized.
-/
@[extern "lean_emit_llvm"]
opaque emitLLVM (env : Environment) (modName : Name) (filepath : FilePath) : IO Unit

/-- Print all profiling times (if any) to standard error. -/
@[extern "lean_display_cumulative_profiling_times"]
opaque displayCumulativeProfilingTimes : BaseIO Unit

/-- Whether Lean was built with an address sanitizer enabled. -/
@[extern "lean_internal_has_address_sanitizer"]
opaque Internal.hasAddressSanitizer (_ : Unit) : Bool

/-- Whether Lean was built with multithread support (i.e., `LEAN_MULTI_THREAD`). -/
@[extern "lean_internal_is_multi_thread"]
opaque Internal.isMultiThread (_ : Unit) : Bool

/-- Whether Lean was built in debug mode (i.e., `LEAN_DEBUG`). -/
@[extern "lean_internal_is_debug"]
opaque Internal.isDebug (_ : Unit) : Bool

/-- Returns the mode Lean was built in (i.e., `LEAN_BUILD_TYPE`). -/
@[extern "lean_internal_get_build_type"]
opaque Internal.getBuildType (_ : Unit) : String

/--
Returns the default max memory (in megabytes) Lean was built with
(i.e., `LEAN_DEFAULT_MAX_MEMORY`).
-/
@[extern "lean_internal_get_default_max_memory"]
opaque Internal.getDefaultMaxMemory (_ : Unit) : Nat

/-- Sets Lean's internal maximum memory (in bytes) for the C runtime. -/
@[extern "lean_internal_set_max_memory"]
opaque Internal.setMaxMemory (max : USize) : BaseIO Unit

/--
Returns the default max heartbeats (in thousands) Lean was built with
(i.e., `LEAN_DEFAULT_MAX_HEARTBEAT`).
-/
@[extern "lean_internal_get_default_max_heartbeat"]
opaque Internal.getDefaultMaxHeartbeat (_ : Unit) : Nat

/-- Sets Lean's internal maximum heartbeats for the C runtime. -/
@[extern "lean_internal_set_max_heartbeat"]
opaque Internal.setMaxHeartbeat (max : USize) : BaseIO Unit

/-- Returns whether Lean was built as verbose by default (i.e., `LEAN_DEFAULT_VERBOSE`). -/
@[extern "lean_internal_get_default_verbose"]
opaque Internal.getDefaultVerbose (_ : Unit) : Bool

/-- Sets whether Lean aborts when a panic occurs. -/
@[extern "lean_internal_set_exit_on_panic"]
opaque Internal.setExitOnPanic (exit : Bool) : BaseIO Unit

/-- Sets the stack size (in bytes) of a Lean thread. -/
@[extern "lean_internal_set_thread_stack_size"]
opaque Internal.setThreadStackSize (sz : USize) : BaseIO Unit

/-- Enables debug assertions with the given tag. -/
@[extern "lean_internal_enable_debug"]
opaque Internal.enableDebug (tag : @& String) : BaseIO Unit

/--
Lean's short version string (i.e., what is printed by `lean --short-version`).

This is the Lean equivalent of of the C++ `LEAN_VERSION_STRING` / `g_short_version_string`.
-/
def shortVersionString : String :=
  if version.specialDesc ≠ "" then
    s!"{versionStringCore}-{version.specialDesc}"
  else if !version.isRelease then
    s!"{versionStringCore}-pre"
  else
    versionStringCore

/-- The full Lean version header (i.e, what is printed by `lean --version`). -/
def versionHeader : String := Id.run do
  let mut ver := shortVersionString
  if Platform.target ≠ "" then
    ver := s!"{ver}, {Platform.target}"
  if githash ≠ "" then
    ver := s!"{ver}, commit {githash}"
  s!"Lean (version {ver}, {Internal.getBuildType ()})"

/--
A string containing the list of additional features Lean was built with.

This is printed by `lean --features`.
-/
def featuresString :=
  if Internal.hasLLVMBackend () then
    "[LLVM]"
  else "[]"

/-- Print the Lean CLI help message. -/
def displayHelp (useStderr : Bool) : IO Unit := do
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
  out.putStrLn    "  -R, --root=dir         set package root directory from which the module name\n"
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
  out.putStrLn    "  -E, --error=kind       report Lean messages of kind as errors"
  out.putStrLn    "      --deps             just print dependencies of a Lean input"
  out.putStrLn    "      --src-deps         just print dependency sources of a Lean input"
  out.putStrLn    "      --print-prefix     print the installation prefix for Lean and exit"
  out.putStrLn    "      --print-libdir     print the installation directory for Lean's built-in libraries and exit"
  out.putStrLn    "      --profile          display elaboration/type checking time for each definition/theorem"
  out.putStrLn    "      --stats            display environment statistics"
  if Internal.isDebug () then
    out.putStrLn  "      --debug=tag        enable assertions with the given tag"
  out.putStrLn    "      -D name=value      set a configuration option (see set_option command)"

inductive ShellComponent
| frontend
| watchdog
| worker

private builtin_initialize maxMemory : Lean.Option Nat ←
  Lean.Option.register `max_memory {defValue := Internal.getDefaultMaxMemory ()}

private builtin_initialize timeout : Lean.Option Nat ←
  Lean.Option.register `timeout {defValue := Internal.getDefaultMaxHeartbeat ()}

private builtin_initialize verbose : Lean.Option Bool ←
  Lean.Option.register `verbose {defValue := Internal.getDefaultVerbose ()}

/--
Returns the default options Lean was built with
(i.e., those set in `stdlib_flags.h`).
-/
@[extern "lean_internal_get_default_options"]
opaque Internal.getDefaultOptions (_ : Unit) : Options

/--
Returns the believer trust level of the Lean environment (i.e., `LEAN_BELIEVER_TRUST_LEVEL`).

If an environment is created with a trust level greater than this, then we can add declarations
to it without type checking them.
-/
@[extern "lean_internal_get_believer_trust_level"]
opaque Internal.getBelieverTrustLevel (_ : Unit) : UInt32

/-- Returns the shell's default trust level. -/
def defaultTrustLevel : UInt32 :=
  Internal.getBelieverTrustLevel () + 1

/-- Returns the platform's native concurrency limit. -/
@[extern "lean_internal_get_hardware_concurrency"]
opaque Internal.getHardwareCurrency (_ : Unit) : UInt32

/-- Returns the default number of threads for the shell's task manager. -/
def defaultNumThreads : UInt32 :=
  if Internal.isMultiThread () then
    Internal.getHardwareCurrency ()
  else 0

structure ShellOptions where
  leanOpts : Options := Internal.getDefaultOptions ()
  forwardedArgs : Array String := #[]
  component : ShellComponent := .frontend
  printPrefix : Bool := false
  printLibDir : Bool := false
  useStdin : Bool := false
  onlyDeps : Bool := false
  onlySrcDeps : Bool := false
  depsJson : Bool := false
  opts : Options := {}
  trustLevel : UInt32 := defaultTrustLevel
  numThreads : UInt32 := defaultNumThreads
  rootDir? : Option System.FilePath := none
  setupFileName? : Option System.FilePath := none
  oleanFileName? : Option System.FilePath := none
  ileanFileName? : Option System.FilePath := none
  cFileName? : Option System.FilePath := none
  bcFileName? : Option System.FilePath := none
  jsonOutput : Bool := false
  errorOnKinds : Array Name := #[]
  printStats : Bool := false
  run : Bool := false

@[export lean_shell_options_mk]
def mkShellOptions (_ : Unit) : ShellOptions := {}

@[export lean_shell_options_get_run]
def ShellOptions.getRun (opts : ShellOptions) : Bool :=
  opts.run

@[export lean_shell_options_get_profiler]
def ShellOptions.getProfiler (opts : ShellOptions) : Bool :=
  profiler.get opts.leanOpts

@[export lean_shell_options_get_num_threads]
def ShellOptions.getNumThreads (opts : ShellOptions) : UInt32 :=
  opts.numThreads

def checkOptArg (optName : String) (optArg? : Option String) : IO String := do
  if let some arg := optArg? then
    return arg
  else
    throw <| .userError s!"argument missing for option '-{optName}'"

def setConfigOption (opts : Options) (arg : String) : IO Options := do
  let pos := arg.find '='
  if h : pos.IsAtEnd then
    throw <| .userError "invalid -D parameter, argument must contain '='"
  else
    let name := arg.sliceTo pos |>.toName
    let val := arg.sliceFrom (pos.next h) |>.copy
    if let some decl := (← getOptionDecls).find? name then
      Language.Lean.setOption opts decl name val
    else
      -- More options may be registered by imports, so we leave validating them to the elaborator.
      -- This (minor) duplication may be resolved later.
      return opts.set name val

/--
Process a command-line option parsed by the C++ shell.

Runs under `IO.initializing` and without a task manager.
-/
@[export lean_shell_options_process]
def ShellOptions.process (opts : ShellOptions)
    (opt : Char) (optArg? : Option String) : EIO UInt32 ShellOptions := do
  have : MonadLift IO (EIO UInt32) := ⟨liftIO⟩
  match opt with
  | 'e' => -- undocumented
    Internal.setExitOnPanic true
    return opts
  | 'j' => -- `-j, --threads=num`
    let arg ← checkOptArg "j" optArg?
    let some numThreads := arg.toNat?
      | throwExpectedNumeric "j"
    if h : numThreads < UInt32.size then
      let numThreads := UInt32.ofNatLT numThreads h
      let forwardedArgs := opts.forwardedArgs.push s!"-j{arg}";
      return {opts with forwardedArgs, numThreads}
    else
      throwTooLarge "j"
  | 'v' => --- `-v, --version`
    IO.println Lean.versionHeader
    throw 0
  | 'V' => --- `-V, --short-version`
    IO.println Lean.shortVersionString
    throw 0
  | 'g' => -- `-g, --githash`
    IO.println Lean.githash
    throw 0
  | 'h' => -- `-h, --help`
    displayHelp (useStderr := false)
    throw 0
  | 'f' => -- `--features`
    IO.println Lean.featuresString
    throw 0
  | 'c' => -- `-c, --c=fname`
    return {opts with cFileName? := ← checkOptArg "c" optArg?}
  | 'b' => -- `-b, --bc=fname`
    return {opts with bcFileName? := ← checkOptArg "b" optArg?}
  | 's' => -- `-s, --tstack=num`
    let arg ← checkOptArg "s" optArg?
    let some stackSize := arg.toNat?
      | throwExpectedNumeric "s"
    let stackSize := stackSize / 4 * 4 * 1024
    if h : stackSize < USize.size then
      let stackSize := USize.ofNatLT stackSize h
      Internal.setThreadStackSize stackSize
      let forwardedArgs := opts.forwardedArgs.push s!"-s{arg}"
      return {opts with forwardedArgs}
    else
      throwTooLarge "s"
  | 'I' => -- `-I, --stdin`
    return {opts with useStdin := true}
  | 'r' => -- `--run`
    return {opts with run := true}
  | 'o' => -- `--o, olean=fname`
    return {opts with oleanFileName? := ← checkOptArg "o" optArg?}
  | 'i' => -- `--i, ilean=fname`
    return {opts with ileanFileName? := ← checkOptArg "i" optArg?}
  | 'R' => -- `-R, --root=dir`
    let arg ← checkOptArg "R" optArg?
    let forwardedArgs := opts.forwardedArgs.push s!"-R{arg}"
    return {opts with forwardedArgs, rootDir? := arg}
  | 'M' => -- `-M, --memory=num`
    let arg ← checkOptArg "M" optArg?
    let some val := arg.toNat?
      | throwExpectedNumeric "M"
    let leanOpts := maxMemory.set opts.leanOpts val
    let forwardedArgs := opts.forwardedArgs.push s!"-M{arg}"
    return {opts with forwardedArgs, leanOpts}
  | 'T' => -- `-T, --timeout=num`
    let arg ← checkOptArg "T" optArg?
    let some val := arg.toNat?
      | throwExpectedNumeric "T"
    let leanOpts := timeout.set opts.leanOpts val
    let forwardedArgs := opts.forwardedArgs.push s!"-T{arg}"
    return {opts with forwardedArgs, leanOpts}
  | 't' => -- `--trust=num`
    let arg ← checkOptArg "t" optArg?
    let some trustLevel := arg.toNat?
      | throwExpectedNumeric "t"
    if h : trustLevel < UInt32.size then
      let trustLevel := UInt32.ofNatLT trustLevel h
      let forwardedArgs := opts.forwardedArgs.push s!"-t{arg}";
      return {opts with forwardedArgs, trustLevel}
    else
      throwTooLarge "t"
  | 'q' =>
    return {opts with leanOpts := verbose.set opts.leanOpts false}
  | 'd' => -- `--deps`
    return {opts with onlyDeps := true}
  | 'O' => -- `--src-deps`
    return {opts with onlySrcDeps := true}
  | 'N' => -- `--deps-json`
    return {opts with onlyDeps := true, depsJson := true}
  | 'J' => -- `--json`
    return {opts with jsonOutput := true}
  | 'a' => -- `--stats`
    return {opts with printStats := true}
  | 'x' =>  -- `--print-prefix`
    return {opts with printPrefix := true}
  | 'L' =>  -- `--print-libdir`
    return {opts with printLibDir := true}
  | 'D' => -- `-D name=value`
    let arg ← checkOptArg "D" optArg?
    let leanOpts ← setConfigOption opts.leanOpts arg
    let forwardedArgs := opts.forwardedArgs.push s!"-D{arg}"
    return {opts with forwardedArgs, leanOpts}
  | 'S' => -- `--server`
    return {opts with component := .watchdog}
  | 'W' => -- `--worker`
    return {opts with component := .worker}
  | 'P' => -- `--profile`
    return {opts with leanOpts := profiler.set opts.leanOpts true}
  | 'B' => -- `--debug=tag`
    if Internal.isDebug () then
      let arg ← checkOptArg "B" optArg?
      Internal.enableDebug arg
      return opts
    -- if not `LEAN_DEBUG`, fall through to unknown option
  | 'p' => -- `--plugin=file`
    let arg ← checkOptArg "p" optArg?
    Lean.loadPlugin arg
    let forwardedArgs := opts.forwardedArgs.push s!"-p{arg}"
    return {opts with forwardedArgs}
  | 'l' => -- `--load-dynlib=file`
    let arg ← checkOptArg "l" optArg?
    Lean.loadDynlib arg
    let forwardedArgs := opts.forwardedArgs.push s!"-l{arg}"
    return {opts with forwardedArgs}
  | 'u' => -- `--setup=file`
    return {opts with setupFileName? := ← checkOptArg "u" optArg?}
  | 'E' => -- `-E, --error=kind`
    let arg ← checkOptArg "E" optArg?
    let errorOnKinds := opts.errorOnKinds.push arg.toName
    return {opts with errorOnKinds}
  | _ =>
    pure ()
  eprint "Unknown command line option\n"
  displayHelp (useStderr := true)
  throw 1
where
  @[inline] eprint msg := do
    IO.eprint msg |>.catchExceptions fun _ => pure ()
  @[inline] liftIO {α} (x : IO α) := do
    match (← x.toBaseIO) with
    | .ok a =>
      return a
    | .error e =>
      eprint s!"error: "
      eprint (toString e)
      eprint "\n"
      throw 1
  @[inline] throwExpectedNumeric opt := do
    eprint s!"error: expected numeric argument for option '-{opt}'\n"
    throw 1
  @[inline] throwTooLarge opt := do
    eprint s!"error: argument value for '-{opt}' is too large\n"
    throw 1

@[export lean_shell_main]
def shellMain (args : List String) (opts : ShellOptions) : IO UInt32 := do
  if opts.printPrefix then
    IO.println (← getBuildDir)
    return 0
  if opts.printLibDir then
    IO.println (← getLibDir (← getBuildDir))
    return 0
  let maxMemory := maxMemory.get opts.leanOpts
  if maxMemory != 0 then
    Internal.setMaxMemory (maxMemory.toUSize * 1024 * 1024)
  let timeout := timeout.get opts.leanOpts
  if timeout != 0 then
    Internal.setMaxHeartbeat (timeout.toUSize * 1000)
  match opts.component with
  | .frontend =>
    pure ()
  | .watchdog =>
    return ← Server.Watchdog.watchdogMain opts.forwardedArgs.toList
  | .worker =>
    return ← Server.FileWorker.workerMain opts.leanOpts
  if opts.onlyDeps && opts.depsJson then
    let fns ←
      if opts.useStdin then
        (← IO.getStdin).lines
      else
        pure args.toArray
    printImportsJson fns
    return 0
  let (fileName?, args) :=
    match args with
    | fileName :: args => (some fileName, args)
    | [] => (none, args)
  if !opts.run && !args.isEmpty then
    IO.eprintln "Expected exactly one file name"
    displayHelp (useStderr := true)
    return 1
  let fileName ←
    if let some fileName := fileName? then
      pure fileName
    else if opts.useStdin then
      pure "<stdin>"
    else
      IO.eprintln "Expected exactly one file name"
      displayHelp (useStderr := true)
      return 1
  let contents ← decodeLossyUTF8 <$> do
    if opts.useStdin then
      (← IO.getStdin).readBinToEnd
    else
      IO.FS.readBinFile fileName
  if opts.onlyDeps then
    Elab.printImports contents fileName
    return 0
  if opts.onlySrcDeps then
    Elab.printImportSrcs contents fileName
    return 0
  -- Quick and dirty `#lang` support
  ---TODO: make it extensible, and add `lean4md`
  let contents ←
    if let some contents := contents.dropPrefix? "#lang" then
      let endLinePos := contents.find '\n'
      let langId := contents.sliceTo endLinePos |>.trimAscii
      if langId == "lean4" then
        pure () -- do nothing for now
      else
        IO.eprintln s!"unknown language '{langId}'\n";
        return 1
      -- Remove up to `\n`
      pure (contents.sliceFrom endLinePos).copy
    else
      pure contents
  let setup? ← opts.setupFileName?.mapM ModuleSetup.load
  let mainModuleName ←
    if let some setup := setup? then
      pure setup.name
    else if let some fileName := fileName? then
      try moduleNameOfFileName fileName opts.rootDir? catch e =>
        if opts.oleanFileName?.isNone && opts.cFileName?.isNone then
          pure `_stdin
        else
          throw e
    else
      pure `_stdin
  let env? ← Elab.runFrontend contents opts.leanOpts fileName mainModuleName
    opts.trustLevel opts.oleanFileName? opts.ileanFileName? opts.jsonOutput opts.errorOnKinds
    #[] opts.printStats setup?
  if let some env := env? then
    if opts.run then
      return ← runMain env opts.leanOpts args
    if let some c := opts.cFileName? then
      let .ok out ← IO.FS.Handle.mk c .write |>.toBaseIO
        | IO.eprintln s!"failed to create '{c}'"
          return 1
      profileitIO "C code generation" opts.leanOpts do
        let data ← IO.ofExcept <| IR.emitC env mainModuleName
        out.write data.toUTF8
    if let some bc := opts.bcFileName? then
      initLLVM
      profileitIO "LLVM code generation" opts.leanOpts do
        emitLLVM env mainModuleName bc
  displayCumulativeProfilingTimes
  if Internal.hasAddressSanitizer () then
    return if env?.isSome then 0 else 1
  else
    -- When not using the address/leak sanitizer, we interrupt execution without garbage collecting.
    -- This is useful when profiling improvements to Lean startup time.
    IO.Process.exit <| if env?.isSome then 0 else 1
