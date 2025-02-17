/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Grind.Arith.Cutsat.Var

namespace Lean.Meta.Grind.Arith.Cutsat

def assertDvdCnstr (e : Expr) : GoalM Unit := do
  let_expr Dvd.dvd _ inst a b ← e | return ()
  unless (← isInstDvdInt inst) do return ()
  let some k ← getIntValue? a
    | reportIssue! "non-linear divisibility constraint found{indentExpr e}"
  let p ← toPoly b
  let c : DvdCnstr := { k, p }
  trace[grind.cutsat.assert.dvd] "{e}, {repr c}"
  -- TODO
  return ()

end Lean.Meta.Grind.Arith.Cutsat
