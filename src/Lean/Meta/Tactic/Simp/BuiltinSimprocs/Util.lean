/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Simp.Simproc

namespace Lean.Meta.Simp

/--
Let `result` be the result of evaluating proposition `p`, return a `.done` step where
the resulting expression is `True`(`False`) if `result is `true`(`false`), and the
proof is uses `Decidable p` and the auxiliary theorems `eq_true_of_decide`/`eq_false_of_decide`.
-/
def evalPropStep (p : Expr) (result : Bool) : SimpM Step := do
  let d ← mkDecide p
  if result then
    return .done { expr := mkConst ``True, proof? := mkAppN (mkConst ``eq_true_of_decide) #[p, d.appArg!, (← mkEqRefl (mkConst ``true))] }
  else
    return .done { expr := mkConst ``False, proof? := mkAppN (mkConst ``eq_false_of_decide) #[p, d.appArg!, (← mkEqRefl (mkConst ``false))] }

end Lean.Meta.Simp
