import LeanCheckerTests.OpenPrivate

set_option Elab.async false

open private Lean.Kernel.Environment.add from Lean.Environment
open private Lean.Environment.setCheckedSync from Lean.Environment

open Lean in
run_elab
  let env ← getEnv
  let kenv := env.toKernelEnv
  let kenv := Lean.Kernel.Environment.add kenv <| .ctorInfo {
    name := `False.intro
    levelParams := []
    type := .const ``False []
    induct := `False
    cidx := 0
    numParams := 0
    numFields := 0
    isUnsafe := false
  }
  setEnv <| Lean.Environment.setCheckedSync env kenv
