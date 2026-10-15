import Lean

/-!
A write to an extension with `logWrites` must name the declaration it is about
(`log := .decl`), which logs it, or be marked `log := .unlogged`; any other write panics.
-/

open Lean

def foo := 1

#guard_panic in
#eval show CoreM Unit from do
  modifyEnv fun env => defHeightOverrideExt.modifyState env id

#guard_panic in
#eval show CoreM Unit from do
  modifyEnv fun env => classExtension.addEntry env { name := ``foo, outParams := #[], outLevelParams := #[] }

#eval show CoreM Unit from do
  modifyEnv fun env => defHeightOverrideExt.modifyState (log := .decl ``foo) env id

#eval show CoreM Unit from do
  modifyEnv fun env => defHeightOverrideExt.modifyState (log := .unlogged) env id
