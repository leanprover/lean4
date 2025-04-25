module

import Lean
import Module.Basic

/-! # Module system basic tests -/

open Lean

/-! Non-essential metadata should only be accessible at level >= .server -/

#eval show IO Unit from do
  let env ← importModules (level := .exported) #[`Module.Basic] {}
  assert! env.header.isModule
  let _ ← Core.CoreM.toIO (ctx := { fileName := "module.lean", fileMap := default }) (s := { env }) do
    assert! (← findDeclarationRanges? ``f).isNone
    assert! (getModuleDoc? (← getEnv) `Module.Basic).any (·.size == 0)

#eval show IO Unit from do
  let env ← importModules (level := .server) #[`Module.Basic] {}
  let _ ← Core.CoreM.toIO (ctx := { fileName := "module.lean", fileMap := default }) (s := { env }) do
    assert! (← findDeclarationRanges? ``f).isSome
    assert! (getModuleDoc? (← getEnv) `Module.Basic).any (·.size == 1)

/-! Theorems should be exported without their bodies -/

/--
info: theorem t : f = 1 :=
<not imported>
-/
#guard_msgs in
#print t

/-- error: dsimp made no progress -/
#guard_msgs in
example : f = 1 := by dsimp only [t]

example : t = t := by dsimp only [trfl]
