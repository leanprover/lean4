/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Simp.Arith.Util
import Lean.Meta.Tactic.Simp.Arith.Nat.Basic

namespace Lean.Meta.Simp.Arith.Nat

def simpCnstrPos? (e : Expr) : MetaM (Option (Expr × Expr)) := do
  let some (c, atoms) ← toLinearCnstr? e
    | return none
  withAbstractAtoms atoms ``Nat fun atoms => do
    let lhs ← c.toArith atoms
    let c₁ := c.toPoly
    let c₂ := c₁.norm
    if c₂.isUnsat then
      let r := mkConst ``False
      let p := mkApp3 (mkConst ``Nat.Linear.ExprCnstr.eq_false_of_isUnsat) (← toContextExpr atoms) (toExpr c) reflBoolTrue
      return some (r, mkExpectedPropHint p (mkPropEq lhs r))
    else if c₂.isValid then
      let r := mkConst ``True
      let p := mkApp3 (mkConst ``Nat.Linear.ExprCnstr.eq_true_of_isValid) (← toContextExpr atoms) (toExpr c) reflBoolTrue
      return some (r, mkExpectedPropHint p (mkPropEq lhs r))
    else
      let c₂ : LinearCnstr := c₂.toExpr
      let r ← c₂.toArith atoms
      if r != lhs then
        let p := mkApp4 (mkConst ``Nat.Linear.ExprCnstr.eq_of_toNormPoly_eq) (← toContextExpr atoms) (toExpr c) (toExpr c₂) reflBoolTrue
        return some (r, mkExpectedPropHint p (mkPropEq lhs r))
      else
        return none

def simpCnstr? (e : Expr) : MetaM (Option (Expr × Expr)) := do
  if let some arg := e.not? then
    let mut eNew? := none
    let mut h₁    := default
    match_expr arg with
    | LE.le α _ a b =>
      let_expr Nat ← α | pure ()
      eNew? := some (mkNatLE (mkNatAdd b (mkNatLit 1)) a)
      h₁    := mkApp2 (mkConst ``Nat.not_le_eq) a b
    | GE.ge α _ a b =>
      let_expr Nat ← α | pure ()
      eNew? := some (mkNatLE (mkNatAdd a (mkNatLit 1)) b)
      h₁    := mkApp2 (mkConst ``Nat.not_ge_eq) a b
    | LT.lt α _ a b =>
      let_expr Nat ← α | pure ()
      eNew? := some (mkNatLE b a)
      h₁    := mkApp2 (mkConst ``Nat.not_lt_eq) a b
    | GT.gt α _ a b =>
      let_expr Nat ← α | pure ()
      eNew? := some (mkNatLE a b)
      h₁    := mkApp2 (mkConst ``Nat.not_gt_eq) a b
    | _ => pure ()
    let some eNew := eNew? | return none
    let some (eNew', h₂) ← simpCnstrPos? eNew | return (eNew, h₁)
    let h  := mkApp6 (mkConst ``Eq.trans [levelOne]) (mkSort levelZero) e eNew eNew' h₁ h₂
    return some (eNew', h)
  else
    simpCnstrPos? e

def simpExpr? (input : Expr) : MetaM (Option (Expr × Expr)) := do
  let (e, ctx) ← toLinearExpr input
  let p  := e.toPoly
  let p' := p.norm
  let e' : LinearExpr := p'.toExpr
  if e' == e then
    return none
  let p := mkApp4 (mkConst ``Nat.Linear.Expr.eq_of_toNormPoly_eq) (← toContextExpr ctx) (toExpr e) (toExpr e') reflBoolTrue
  let r ← e'.toArith ctx
  return some (r, mkExpectedPropHint p (mkNatEq input r))

end Lean.Meta.Simp.Arith.Nat
