/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Compiler.LCNF.CompilerM
import Lean.Compiler.LCNF.DeclHash
import Lean.Compiler.LCNF.Internalize

namespace Lean.Compiler.LCNF

abbrev AuxDeclCache := PHashMap Decl Name

builtin_initialize auxDeclCacheExt : EnvExtension AuxDeclCache ←
  registerEnvExtension (pure {}) (asyncMode := .sync)  -- compilation is non-parallel anyway

inductive CacheAuxDeclResult where
  | new
  | alreadyCached (declName : Name)

def cacheAuxDecl (decl : Decl) : CompilerM CacheAuxDeclResult := do
  let key := { decl with name := .anonymous }
  let key ← normalizeFVarIds key
  match auxDeclCacheExt.getState (← getEnv) |>.find? key with
  | some declName =>
    return .alreadyCached declName
  | none =>
    modifyEnv fun env => auxDeclCacheExt.modifyState env fun s => s.insert key decl.name
    return .new

end Lean.Compiler.LCNF
