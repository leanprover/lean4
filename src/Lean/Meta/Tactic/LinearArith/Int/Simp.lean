/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.LinearArith.Basic
import Lean.Meta.Tactic.LinearArith.Int.Basic

namespace Lean.Meta.Linear.Int

def simpCnstrPos? (e : Expr) : MetaM (Option (Expr × Expr)) := do
  let (some c, atoms) ← ToLinear.run (ToLinear.toLinearCnstr? e) | return none
  withAbstractAtoms atoms ``Int fun ctx => do
    let lhs ← c.toArith ctx
    let p := c.toPoly
    if p.isUnsat then
      let r := mkConst ``False
      let p := mkApp3 (mkConst ``Int.Linear.ExprCnstr.eq_false_of_isUnsat) (toContextExpr ctx) (toExpr c) reflBoolTrue
      return some (r, ← mkExpectedTypeHint p (← mkEq lhs r))
    else if p.isValid then
      let r := mkConst ``True
      let p := mkApp3 (mkConst ``Int.Linear.ExprCnstr.eq_true_of_isValid) (toContextExpr ctx) (toExpr c) reflBoolTrue
      return some (r, ← mkExpectedTypeHint p (← mkEq lhs r))
    else
      let c' : LinearCnstr := p.toExprCnstr
      if c != c' then
        let r ← c'.toArith ctx
        let p := mkApp4 (mkConst ``Int.Linear.ExprCnstr.eq_of_toPoly_eq) (toContextExpr ctx) (toExpr c) (toExpr c') reflBoolTrue
        return some (r, ← mkExpectedTypeHint p (← mkEq lhs r))
      else
        return none

def simpCnstr? (e : Expr) : MetaM (Option (Expr × Expr)) := do
  if let some arg := e.not? then
    let mut eNew?   := none
    let mut thmName := Name.anonymous
    match_expr arg with
    | LE.le α _ lhs rhs =>
      if α.isConstOf ``Int then
        eNew?   := some (mkIntLE (mkIntAdd rhs (mkIntLit 1)) lhs)
        thmName := ``Int.not_le_eq
    | GE.ge α _ lhs rhs =>
      if α.isConstOf ``Int then
        eNew?   := some (mkIntLE (mkIntAdd lhs (mkIntLit 1)) rhs)
        thmName := ``Int.not_ge_eq
    | LT.lt α _ lhs rhs =>
      if α.isConstOf ``Int then
        eNew?   := some (mkIntLE rhs lhs)
        thmName := ``Int.not_lt_eq
    | GT.gt α _ lhs rhs =>
      if α.isConstOf ``Int then
        eNew?   := some (mkIntLE lhs rhs)
        thmName := ``Int.not_gt_eq
    | _ => pure ()
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
  let e' := p.toExpr
  if e != e' then
    -- We only return some if monomials were fused
    let p := mkApp4 (mkConst ``Int.Linear.Expr.eq_of_toPoly_eq) (toContextExpr ctx) (toExpr e) (toExpr e') reflBoolTrue
    let r ← LinearExpr.toArith ctx e'
    return some (r, p)
  else
    return none

end Lean.Meta.Linear.Int
