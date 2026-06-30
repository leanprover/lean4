/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Meta.Tactic.Simp.Simproc

public section

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

/--
Like `evalPropStep`, but specialized for `@Eq.{u} α a b`. When the values are equal, uses
`eq_true rfl` which requires no kernel evaluation. When different, calls `mkNeProof` to build
a proof of `a ≠ b`.
-/
def evalEqPropStep (e : Expr) (eq : Bool) (mkNeProof : SimpM Expr) : SimpM Step := do
  let α := e.appFn!.appFn!.appArg!
  let a := e.appFn!.appArg!
  let u := e.appFn!.appFn!.appFn!.constLevels!.head!
  if eq then
    let proof := mkApp2 (mkConst ``eq_true) e (mkApp2 (mkConst ``Eq.refl [u]) α a)
    return .done { expr := mkConst ``True, proof? := proof }
  else
    let neProof ← mkNeProof
    let proof := mkApp2 (mkConst ``eq_false) e neProof
    return .done { expr := mkConst ``False, proof? := proof }

/--
Like `evalPropStep`, but specialized for `@Ne.{u} α a b`. When the values differ, calls
`mkNeProof` to build a proof of `a ≠ b`. When equal, uses `eq_false (not_not_intro rfl)`
which requires no kernel evaluation.
-/
def evalNePropStep (e : Expr) (ne : Bool) (mkNeProof : SimpM Expr) : SimpM Step := do
  if ne then
    let neProof ← mkNeProof
    let proof := mkApp2 (mkConst ``eq_true) e neProof
    return .done { expr := mkConst ``True, proof? := proof }
  else
    let α := e.appFn!.appFn!.appArg!
    let a := e.appFn!.appArg!
    let u := e.appFn!.appFn!.appFn!.constLevels!.head!
    let eqProp := mkApp3 (mkConst ``Eq [u]) α a a
    let rflExpr := mkApp2 (mkConst ``Eq.refl [u]) α a
    let proof := mkApp2 (mkConst ``eq_false) e (mkApp2 (mkConst ``not_not_intro) eqProp rflExpr)
    return .done { expr := mkConst ``False, proof? := proof }

end Lean.Meta.Simp
