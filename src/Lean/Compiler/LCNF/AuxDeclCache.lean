/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Compiler.LCNF.CompilerM
import Lean.Compiler.LCNF.DeclHash
import Lean.Compiler.LCNF.Internalize

namespace Lean.Compiler.LCNF

namespace AuxDecl
abbrev Cache := SMap Decl Name

structure CacheEntry where
  key : Decl
  declName : Name
  deriving Inhabited

def addEntry (cache : Cache) (e : CacheEntry) : Cache :=
  cache.insert e.key e.declName

builtin_initialize auxDeclCacheExt : SimplePersistentEnvExtension CacheEntry Cache ←
  registerSimplePersistentEnvExtension {
    addEntryFn    := addEntry
    addImportedFn := fun es => (mkStateFromImportedEntries addEntry {} es).switch
  }

inductive CacheAuxDeclResult where
  | new
  | alreadyCached (declName : Name)

def cache (decl : Decl) : CompilerM CacheAuxDeclResult := do
  if (← getPhase) matches .base then
    -- We do not cache eager lambda lifting results
    return .new
  else
    let key := { decl with name := .anonymous }
    let key ← normalizeFVarIds key
    match auxDeclCacheExt.getState (← getEnv) |>.find? key with
    | some declName =>
      return .alreadyCached declName
    | none =>
      modifyEnv fun env => auxDeclCacheExt.addEntry env { key, declName := decl.name }
      return .new

end AuxDecl

open AuxDecl

def cacheAuxDecl (decl : Decl) : CompilerM CacheAuxDeclResult := do
  cache decl

end Lean.Compiler.LCNF

