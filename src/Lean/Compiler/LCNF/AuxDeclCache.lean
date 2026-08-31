/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Compiler.LCNF.DeclHash
public import Lean.Compiler.LCNF.Internalize

public section

namespace Lean.Compiler.LCNF

structure  AuxDeclCacheKey where
  pu : Purity
  decl : Decl pu
  deriving BEq, Hashable

builtin_initialize auxDeclCacheExt : CacheExtension AuxDeclCacheKey Name ← CacheExtension.register

inductive CacheAuxDeclResult where
  | new
  | alreadyCached (declName : Name)

def cacheAuxDecl (decl : Decl pu) : CompilerM CacheAuxDeclResult := do
  let key := { decl with name := .anonymous }
  let key ← normalizeFVarIds key
  let key := ⟨pu, key⟩
  match (← auxDeclCacheExt.find? key) with
  | some declName =>
    return .alreadyCached declName
  | none =>
    auxDeclCacheExt.insert key decl.name
    return .new

end Lean.Compiler.LCNF
