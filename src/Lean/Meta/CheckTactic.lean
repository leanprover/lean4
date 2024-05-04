/-
Copyright (c) 2024 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joe Hendrix
-/
prelude
import Lean.Meta.Basic

namespace Lean.Meta.CheckTactic

def mkCheckGoalType (val type : Expr) : MetaM Expr := do
  let lvl ← mkFreshLevelMVar
  pure <| mkApp2 (mkConst ``CheckGoalType [lvl]) type val

def matchCheckGoalType (goalType : Expr) : MetaM (Expr × Expr × Level) := do
  let u ← mkFreshLevelMVar
  let type ← mkFreshExprMVar (some (.sort u))
  let val  ← mkFreshExprMVar (some type)
  let extType := mkAppN (.const ``CheckGoalType [u]) #[type, val]
  if !(← isDefEq goalType extType) then
    throwError "Goal{indentExpr goalType}\nis expected to match {indentExpr extType}"
  pure (val, type, u)

end Lean.Meta.CheckTactic
