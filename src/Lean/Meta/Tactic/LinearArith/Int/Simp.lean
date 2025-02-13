/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.LinearArith.Basic
import Lean.Meta.Tactic.LinearArith.Int.Basic

def Int.Linear.Poly.gcdAll : Poly → Nat
  | .num k => k.natAbs
  | .add k _ p => go k.natAbs p
where
  go (k : Nat) (p : Poly) : Nat :=
    if k == 1 then k
    else match p with
      | .num k' => Nat.gcd k k'.natAbs
      | .add k' _ p => go (Nat.gcd k k'.natAbs) p

def Int.Linear.PolyCnstr.gcdAll : PolyCnstr → Nat
  | .eq p => p.gcdAll
  | .le p => p.gcdAll

def Int.Linear.Poly.gcdCoeffs : Poly → Nat
  | .num _ => 1
  | .add k _ p => go k.natAbs p
where
  go (k : Nat) (p : Poly) : Nat :=
    if k == 1 then k
    else match p with
      | .num _ => k
      | .add k' _ p => go (Nat.gcd k k'.natAbs) p

def Int.Linear.PolyCnstr.gcdCoeffs : PolyCnstr → Nat
  | .eq p | .le p => p.gcdCoeffs

def Int.Linear.PolyCnstr.isEq : PolyCnstr → Bool
  | .eq _ => true
  | .le _ => false

def Int.Linear.PolyCnstr.getConst : PolyCnstr → Int
  | .eq p | .le p => p.getConst

namespace Lean.Meta.Linear.Int

def simpCnstrPos? (e : Expr) : MetaM (Option (Expr × Expr)) := do
  let some (c, atoms) ← toLinearCnstr? e | return none
  withAbstractAtoms atoms ``Int fun atoms => do
    let lhs ← c.toArith atoms
    let p := c.toPoly
    if p.isUnsat then
      let r := mkConst ``False
      let h := mkApp3 (mkConst ``Int.Linear.ExprCnstr.eq_false_of_isUnsat) (toContextExpr atoms) (toExpr c) reflBoolTrue
      return some (r, ← mkExpectedTypeHint h (← mkEq lhs r))
    else if p.isValid then
      let r := mkConst ``True
      let h := mkApp3 (mkConst ``Int.Linear.ExprCnstr.eq_true_of_isValid) (toContextExpr atoms) (toExpr c) reflBoolTrue
      return some (r, ← mkExpectedTypeHint h (← mkEq lhs r))
    else
      let c' : LinearCnstr := p.toExprCnstr
      if c != c' then
        match p with
        | .eq (.add 1 x (.add (-1) y (.num 0))) =>
          let r := mkIntEq atoms[x]! atoms[y]!
          let h := mkApp5 (mkConst ``Int.Linear.ExprCnstr.eq_of_toPoly_eq_var) (toContextExpr atoms) (toExpr x) (toExpr y) (toExpr c) reflBoolTrue
          return some (r, ← mkExpectedTypeHint h (← mkEq lhs r))
        | .eq (.add 1 x (.num k)) =>
          let r := mkIntEq atoms[x]! (toExpr (-k))
          let h := mkApp5 (mkConst ``Int.Linear.ExprCnstr.eq_of_toPoly_eq_const) (toContextExpr atoms) (toExpr x) (toExpr (-k)) (toExpr c) reflBoolTrue
          return some (r, ← mkExpectedTypeHint h (← mkEq lhs r))
        | _ =>
          let k := p.gcdCoeffs
          if k == 1 then
            let r ← c'.toArith atoms
            let h := mkApp4 (mkConst ``Int.Linear.ExprCnstr.eq_of_toPoly_eq) (toContextExpr atoms) (toExpr c) (toExpr c') reflBoolTrue
            return some (r, ← mkExpectedTypeHint h (← mkEq lhs r))
          else if p.getConst % k == 0 then
            let c' : LinearCnstr := (p.div k).toExprCnstr
            let r ← c'.toArith atoms
            let h := mkApp5 (mkConst ``Int.Linear.ExprCnstr.eq_of_divBy) (toContextExpr atoms) (toExpr c) (toExpr c') (toExpr (Int.ofNat k)) reflBoolTrue
            return some (r, ← mkExpectedTypeHint h (← mkEq lhs r))
          else if p.isEq then
            let r := mkConst ``False
            let h := mkApp4 (mkConst ``Int.Linear.ExprCnstr.eq_false_of_isUnsat_coeff) (toContextExpr atoms) (toExpr c) (toExpr (Int.ofNat k)) reflBoolTrue
            return some (r, ← mkExpectedTypeHint h (← mkEq lhs r))
          else
            -- `p.isLe`: tighten the bound
            let c' : LinearCnstr := (p.div k).toExprCnstr
            let r ← c'.toArith atoms
            let h := mkApp5 (mkConst ``Int.Linear.ExprCnstr.eq_of_divByLe) (toContextExpr atoms) (toExpr c) (toExpr c') (toExpr (Int.ofNat k)) reflBoolTrue
            return some (r, ← mkExpectedTypeHint h (← mkEq lhs r))
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
  let (e, atoms) ← toLinearExpr e
  let p  := e.toPoly
  let e' := p.toExpr
  if e != e' then
    -- We only return some if monomials were fused
    let p := mkApp4 (mkConst ``Int.Linear.Expr.eq_of_toPoly_eq) (toContextExpr atoms) (toExpr e) (toExpr e') reflBoolTrue
    let r ← LinearExpr.toArith atoms e'
    return some (r, p)
  else
    return none

end Lean.Meta.Linear.Int
