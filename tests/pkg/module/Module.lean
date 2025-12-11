import Lean
import Module.Basic
import Module.Imported
import Module.ImportedAll
import Module.ImportedPrivateImported
import Module.PrivateImported
import Module.ImportedAllPrivateImported
import Module.ImportedAllImportedAll
import Module.NonModule
import Module.MetaImported

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
