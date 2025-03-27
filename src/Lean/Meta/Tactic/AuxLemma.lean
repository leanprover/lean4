/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.AddDecl
import Lean.Meta.Basic

namespace Lean.Meta

structure AuxLemmas where
  idx    : Nat := 1
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
def mkAuxLemma (levelParams : List Name) (type : Expr) (value : Expr) : MetaM Name := do
  let env ← getEnv
  let s := auxLemmasExt.getState env
  let mkNewAuxLemma := do
    let auxName := Name.mkNum (env.asyncPrefix?.getD env.mainModule ++ `_auxLemma) s.idx
    addDecl <| Declaration.thmDecl {
      name := auxName
      levelParams, type, value
    }
    modifyEnv fun env => auxLemmasExt.modifyState env fun ⟨idx, lemmas⟩ => ⟨idx + 1, lemmas.insert type (auxName, levelParams)⟩
    return auxName
  match s.lemmas.find? type with
  | some (name, levelParams') => if levelParams == levelParams' then return name else mkNewAuxLemma
  | none => mkNewAuxLemma

end Lean.Meta
