/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Grind.Lemmas
import Lean.Meta.Tactic.Grind.Types
import Lean.Meta.Tactic.Grind.Internalize
import Lean.Meta.Tactic.Grind.Simp

namespace Lean.Meta.Grind
/--
If `parent` is a projection-application `proj_i c`,
check whether the root of the equivalence class containing `c` is a constructor-application `ctor ... a_i ...`.
If so, internalize the term `proj_i (ctor ... a_i ...)` and add the equality `proj_i (ctor ... a_i ...) = a_i`.
-/
def propagateForallProp (parent : Expr) : GoalM Unit := do
  let .forallE n p q bi := parent | return ()
  unless (← isEqTrue p) do return ()
  let h₁ ← mkEqTrueProof p
  let qh₁ := q.instantiate1 (mkApp2 (mkConst ``of_eq_true) p h₁)
  let r ← pre qh₁
  let q := mkLambda n bi p q
  let q' := r.expr
  internalize q' (← getGeneration parent)
  let h₂ ← r.getProof
  let h := mkApp5 (mkConst ``Lean.Grind.forall_propagator) p q q' h₁ h₂
  pushEq parent q' h

end Lean.Meta.Grind
