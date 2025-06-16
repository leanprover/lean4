/-
Copyright (c) 2025 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mac Malone
-/
prelude
import Lean.Elab.Frontend
import Lean.Compiler.IR.EmitC

/-  Lean companion to  `shell.cpp` -/

open System

namespace Lean

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

@[export lean_shell_main]
private def shellMain
    (args : List String)
    (input : String)
    (opts : Options)
    (fileName : String)
    (mainModuleName : Name)
    (trustLevel : UInt32 := 0)
    (oleanFileName? : Option System.FilePath := none)
    (ileanFileName? : Option System.FilePath := none)
    (cFileName? : Option System.FilePath := none)
    (bcFileName? : Option System.FilePath := none)
    (jsonOutput : Bool := false)
    (errorOnKinds : Array Name := #[])
    (printStats : Bool := false)
    (setupFileName? : Option System.FilePath := none)
    (run : Bool := false)
    : IO UInt32 := do
  let setup? ← setupFileName?.mapM ModuleSetup.load
  let mainModuleName := setup?.map (·.name) |>.getD mainModuleName
  let env? ← Elab.runFrontend input opts fileName mainModuleName trustLevel
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
