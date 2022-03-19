/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Tactic.LinearArith.Nat.Basic

namespace Lean.Meta.Linear.Nat

def simpCnstrPos? (e : Expr) : MetaM (Option (Expr × Expr)) := do
  let (some c, ctx) ← ToLinear.run (ToLinear.toLinearCnstr? e) | return none
  let c₁ := c.toPoly
  let c₂ := c₁.norm
  if c₂.isUnsat then
    let p := mkApp3 (mkConst ``Nat.Linear.ExprCnstr.eq_false_of_isUnsat) (← toContextExpr ctx) (toExpr c) reflTrue
    return some (mkConst ``False, p)
  else if c₂.isValid then
    let p := mkApp3 (mkConst ``Nat.Linear.ExprCnstr.eq_true_of_isValid) (← toContextExpr ctx) (toExpr c) reflTrue
    return some (mkConst ``True, p)
  else
    let c₂ : LinearCnstr := c₂.toExpr
    let r ← c₂.toArith ctx
    if r != e then
      let p := mkApp4 (mkConst ``Nat.Linear.ExprCnstr.eq_of_toNormPoly_eq) (← toContextExpr ctx) (toExpr c) (toExpr c₂) reflTrue
      return some (r, ← mkExpectedTypeHint p (← mkEq e r))
    else
      return none

def simpCnstr? (e : Expr) : MetaM (Option (Expr × Expr)) := do
  if let some arg := e.not? then
    let mut eNew?   := none
    let mut thmName := Name.anonymous
    if arg.isAppOfArity ``LE.le 4 then
      eNew?   := some (← mkLE (← mkAdd (arg.getArg! 3) (mkNatLit 1)) (arg.getArg! 2))
      thmName := ``Nat.not_le_eq
    else if arg.isAppOfArity ``GE.ge 4 then
      eNew?   := some (← mkLE (← mkAdd (arg.getArg! 2) (mkNatLit 1)) (arg.getArg! 3))
      thmName := ``Nat.not_ge_eq
    else if arg.isAppOfArity ``LT.lt 4 then
      eNew?   := some (← mkLE (arg.getArg! 3) (arg.getArg! 2))
      thmName := ``Nat.not_lt_eq
    else if arg.isAppOfArity ``GT.gt 4 then
      eNew?   := some (← mkLE (arg.getArg! 2) (arg.getArg! 3))
      thmName := ``Nat.not_gt_eq
    if let some eNew := eNew? then
      let h₁ := mkApp2 (mkConst thmName) (arg.getArg! 2) (arg.getArg! 3)
      if let some (eNew', h₂) ← simpCnstrPos? eNew then
        let h  := mkApp6 (mkConst ``Eq.trans [levelOne]) (mkSort levelZero) e eNew eNew' h₁ h₂
        return some (eNew', h)
      else
        return some (eNew, h₁)
    else
      return none
  else
    simpCnstrPos? e

def simpExpr? (e : Expr) : MetaM (Option (Expr × Expr)) := do
  let (e, ctx) ← ToLinear.run (ToLinear.toLinearExpr e)
  let p  := e.toPoly
  let p' := p.norm
  if p'.length < p.length then
    -- We only return some if monomials were fused
    let e' : LinearExpr := p'.toExpr
    let p := mkApp4 (mkConst ``Nat.Linear.Expr.eq_of_toNormPoly_eq) (← toContextExpr ctx) (toExpr e) (toExpr e') reflTrue
    let r ← e'.toArith ctx
    return some (r, p)
  else
    return none

end Lean.Meta.Linear.Nat
