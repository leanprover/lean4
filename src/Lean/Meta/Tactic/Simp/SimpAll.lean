/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Tactic.Util
import Lean.Meta.Tactic.Simp.Main

namespace Lean.Meta

namespace SimpAll

structure Entry where
  fvarId : FVarId -- original fvarId
  id     : Name   -- id of the lemma at `SimpLemmas`
  type   : Expr
  proof  : Expr

structure State where
  modified : Bool := false
  ctx      : Simp.Context

end SimpAll

def simpAll (mvarId : MVarId) (ctx : Simp.Context) : MetaM (Option MVarId) := do
  let hs ← getNondepPropHyps mvarId
  return mvarId
  -- Simp.main e ctx (methods := Simp.DefaultMethods.methods)


end Lean.Meta