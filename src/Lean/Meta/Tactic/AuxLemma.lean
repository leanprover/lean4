/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.AddDecl
import Lean.Meta.Basic
import Lean.DefEqAttrib

namespace Lean.Meta

structure AuxLemmas where
  lemmas : PHashMap Expr (Name × List Name) := {}
  deriving Inhabited

builtin_initialize auxLemmasExt : EnvExtension AuxLemmas ←
  registerEnvExtension (pure {}) (asyncMode := .local)  -- a mere cache, keep local

/--
  Helper method for creating auxiliary lemmas in the environment.

  It uses a cache that maps `type` to declaration name. The cache is not stored in `.olean` files.
  It is useful to make sure the same auxiliary lemma is not created over and over again in the same
  environment branch. For expensive auxiliary lemmas that should be deduplicated even across
  different environment branches, consider using `realizeConst` instead.

  This method is useful for tactics (e.g., `simp`) that may perform preprocessing steps to lemmas provided by
  users. For example, `simp` preprocessor may convert a lemma into multiple ones.
-/
def mkAuxLemma (levelParams : List Name) (type : Expr) (value : Expr) (kind? : Option Name := none)
    (cache := true) (inferRfl := false) : MetaM Name := do
  let env ← getEnv
  let s := auxLemmasExt.getState env
  let mkNewAuxLemma := do
    let auxName ← mkAuxDeclName (kind := kind?.getD `_proof)
    let decl :=
      if env.hasUnsafe type || env.hasUnsafe value then
        -- `result` contains unsafe code, thus we cannot use a theorem.
        Declaration.defnDecl {
          name        := auxName
          hints       := ReducibilityHints.opaque
          safety      := DefinitionSafety.unsafe
          levelParams, type, value
        }
      else
        Declaration.thmDecl {
          name := auxName
          levelParams, type, value
        }
    addDecl decl
    if inferRfl then
      inferDefEqAttr auxName
    modifyEnv fun env => auxLemmasExt.modifyState env fun ⟨lemmas⟩ => ⟨lemmas.insert type (auxName, levelParams)⟩
    return auxName
  if cache then
    if let some (name, levelParams') := s.lemmas.find? type then
      if levelParams == levelParams' then
        return name
  mkNewAuxLemma

end Lean.Meta
