/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Sorry -- TODO: remove
import Lean.Meta.Tactic.Grind.Types

namespace Lean.Meta.Grind

/--
Returns a proof that `a = b` (or `HEq a b`).
It assumes `a` and `b` are in the same equivalence class.
-/
def mkEqProof (a b : Expr) : GoalM Expr := do
  -- TODO
  if (← isDefEq (← inferType a) (← inferType b)) then
    mkSorry (← mkEq a b) (synthetic := false)
  else
    mkSorry (← mkHEq a b) (synthetic := false)

/--
Returns a proof that `a = True`.
It assumes `a` and `True` are in the same equivalence class.
-/
def mkEqTrueProof (a : Expr) : GoalM Expr := do
  mkEqProof a (← getTrueExpr)

/--
Returns a proof that `a = False`.
It assumes `a` and `False` are in the same equivalence class.
-/
def mkEqFalseProof (a : Expr) : GoalM Expr := do
  mkEqProof a (← getFalseExpr)

end Lean.Meta.Grind
