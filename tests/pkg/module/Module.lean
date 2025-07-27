public import Lean
public import Module.Basic
public import Module.Imported
public import Module.ImportedAll
public import Module.ImportedPrivateImported
public import Module.PrivateImported
public import Module.ImportedAllPrivateImported
public import Module.NonModule

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
    assert! (getModuleDoc? (← getEnv) `Module.Basic).any (·.size >= 1)
