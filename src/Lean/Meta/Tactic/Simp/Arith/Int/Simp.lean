/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Simp.Arith.Util
public import Lean.Meta.Tactic.Simp.Arith.Int.Basic
public section

def Int.Linear.Poly.gcdAll : Poly → Nat
  | .num k => k.natAbs
  | .add k _ p => go k.natAbs p
where
  go (k : Nat) (p : Poly) : Nat :=
    if k == 1 then k
    else match p with
      | .num k' => Nat.gcd k k'.natAbs
      | .add k' _ p => go (Nat.gcd k k'.natAbs) p

def Int.Linear.Poly.gcdCoeffs' : Poly → Nat
  | .num _ => 1
  | .add k _ p => go k.natAbs p
where
  go (k : Nat) (p : Poly) : Nat :=
    if k == 1 then k
    else match p with
      | .num _ => k
      | .add k' _ p => go (Nat.gcd k k'.natAbs) p

namespace Lean.Meta.Simp.Arith.Int

def simpEq? (e : Expr) : MetaM (Option (Expr × Expr)) := do
  let some (a, b, atoms) ← eqCnstr? e | return none
  let e := mkIntEq (← a.denoteExpr (atoms[·]!)) (← b.denoteExpr (atoms[·]!))
  let p := a.sub b |>.norm
  if p.isUnsatEq then
    let r := mkConst ``False
    let h := mkApp4 (mkConst ``Int.Linear.eq_eq_false) (← toContextExpr atoms) (toExpr a) (toExpr b) eagerReflBoolTrue
    return some (r, mkExpectedPropHint h (mkPropEq e r))
  else if p.isValidEq then
    let r := mkConst ``True
    let h := mkApp4 (mkConst ``Int.Linear.eq_eq_true) (← toContextExpr atoms) (toExpr a) (toExpr b) eagerReflBoolTrue
    return some (r, mkExpectedPropHint h (mkPropEq e r))
  else if p.toExpr == a && b == .num 0 then
    return none
  else match p with
    | .add 1 x (.add (-1) y (.num 0)) =>
      let r := mkIntEq atoms[x]! atoms[y]!
      let h := mkApp6 (mkConst ``Int.Linear.norm_eq_var) (← toContextExpr atoms) (toExpr a) (toExpr b) (toExpr x) (toExpr y) eagerReflBoolTrue
      return some (r, mkExpectedPropHint h (mkPropEq e r))
    | .add 1 x (.num k) =>
      let r := mkIntEq atoms[x]! (toExpr (-k))
      let h := mkApp6 (mkConst ``Int.Linear.norm_eq_var_const) (← toContextExpr atoms) (toExpr a) (toExpr b) (toExpr x) (toExpr (-k)) eagerReflBoolTrue
      return some (r, mkExpectedPropHint h (mkPropEq e r))
    | _ =>
      let k := p.gcdCoeffs'
      if k == 1 then
        let r := mkIntEq (← p.denoteExpr (atoms[·]!)) (mkIntLit 0)
        let h := mkApp5 (mkConst ``Int.Linear.norm_eq) (← toContextExpr atoms) (toExpr a) (toExpr b) (toExpr p) eagerReflBoolTrue
        return some (r, mkExpectedPropHint h (mkPropEq e r))
      else if p.getConst % k == 0 then
        let p := p.div k
        let r := mkIntEq (← p.denoteExpr (atoms[·]!)) (mkIntLit 0)
        let h := mkApp6 (mkConst ``Int.Linear.norm_eq_coeff) (← toContextExpr atoms) (toExpr a) (toExpr b) (toExpr p) (toExpr (Int.ofNat k)) eagerReflBoolTrue
        return some (r, mkExpectedPropHint h (mkPropEq e r))
      else
        let r := mkConst ``False
        let h := mkApp5 (mkConst ``Int.Linear.eq_eq_false_of_divCoeff) (← toContextExpr atoms) (toExpr a) (toExpr b) (toExpr (Int.ofNat k)) eagerReflBoolTrue
        return some (r, mkExpectedPropHint h (mkPropEq e r))


def simpLe? (e : Expr) (checkIfModified : Bool) : MetaM (Option (Expr × Expr)) := do
  -- If `e` is not already a `≤`, then we should not check whether it has changed.
  let checkIfModified := e.isAppOf ``LE.le && checkIfModified
  let some (a, b, atoms) ← leCnstr? e | return none
  let e := mkIntLE (← a.denoteExpr (atoms[·]!)) (← b.denoteExpr (atoms[·]!))
  let p := a.sub b |>.norm
  if p.isUnsatLe then
    let r := mkConst ``False
    let h := mkApp4 (mkConst ``Int.Linear.le_eq_false) (← toContextExpr atoms) (toExpr a) (toExpr b) eagerReflBoolTrue
    return some (r, mkExpectedPropHint h (mkPropEq e r))
  else if p.isValidLe then
    let r := mkConst ``True
    let h := mkApp4 (mkConst ``Int.Linear.le_eq_true) (← toContextExpr atoms) (toExpr a) (toExpr b) eagerReflBoolTrue
    return some (r, mkExpectedPropHint h (mkPropEq e r))
  else if checkIfModified && p.toExpr == a && b == .num 0 then
    return none
  else
    let k := p.gcdCoeffs'
    if k == 1 then
      let r := mkIntLE (← p.denoteExpr (atoms[·]!)) (mkIntLit 0)
      let h := mkApp5 (mkConst ``Int.Linear.norm_le) (← toContextExpr atoms) (toExpr a) (toExpr b) (toExpr p) eagerReflBoolTrue
      return some (r, mkExpectedPropHint h (mkPropEq e r))
    else
      let tight := p.getConst % k != 0
      let p := p.div k
      let r := mkIntLE (← p.denoteExpr (atoms[·]!)) (mkIntLit 0)
      let h ← if tight then
        pure <| mkApp6 (mkConst ``Int.Linear.norm_le_coeff_tight) (← toContextExpr atoms) (toExpr a) (toExpr b) (toExpr p) (toExpr (Int.ofNat k)) eagerReflBoolTrue
      else
        pure <| mkApp6 (mkConst ``Int.Linear.norm_le_coeff) (← toContextExpr atoms) (toExpr a) (toExpr b) (toExpr p) (toExpr (Int.ofNat k)) eagerReflBoolTrue
      return some (r, mkExpectedPropHint h (mkPropEq e r))

def simpRel? (e : Expr) : MetaM (Option (Expr × Expr)) := do
  if let some arg := e.not? then
    let mut eNew? := none
    let mut h₁    := default
    match_expr arg with
    | LE.le α _ lhs rhs =>
      let_expr Int ← α | pure ()
      eNew?   := some (mkIntLE (mkIntAdd rhs (mkIntLit 1)) lhs)
      h₁      := mkApp2 (mkConst ``Int.not_le_eq) lhs rhs
    | GE.ge α _ lhs rhs =>
      let_expr Int ← α | pure ()
      eNew?   := some (mkIntLE (mkIntAdd lhs (mkIntLit 1)) rhs)
      h₁      := mkApp2 (mkConst ``Int.not_ge_eq) lhs rhs
    | LT.lt α _ lhs rhs =>
      let_expr Int ← α | pure ()
      eNew?   := some (mkIntLE rhs lhs)
      h₁      := mkApp2 (mkConst ``Int.not_lt_eq) lhs rhs
    | GT.gt α _ lhs rhs =>
      let_expr Int ← α | pure ()
      eNew?   := some (mkIntLE lhs rhs)
      h₁      := mkApp2 (mkConst ``Int.not_gt_eq) lhs rhs
    | _ => pure ()
    let some eNew := eNew? | return none
    let some (eNew', h₂) ← simpLe? eNew (checkIfModified := false) | return (eNew, h₁)
    let h  := mkApp6 (mkConst ``Eq.trans [levelOne]) (mkSort levelZero) e eNew eNew' h₁ h₂
    return some (eNew', h)
  else
    simpLe? e (checkIfModified := true)

def simpDvd? (e : Expr) : MetaM (Option (Expr × Expr)) := do
  let some (d, e, atoms) ← dvdCnstr? e | return none
  if d == 0 then return none
  let lhs := mkIntDvd (toExpr d) (← e.denoteExpr (atoms[·]!))
  let p := e.norm
  let g := p.gcdCoeffs d
  if p.getConst % g == 0 then
    let p := p.div g
    let d' := d / g
    if e == p.toExpr then
      return none
    let rhs := mkIntDvd (toExpr d') (← p.denoteExpr (atoms[·]!))
    let h ← if g == 1 then
      pure <| mkApp5 (mkConst ``Int.Linear.norm_dvd) (← toContextExpr atoms) (toExpr d) (toExpr e) (toExpr p) eagerReflBoolTrue
    else
      pure <| mkApp7 (mkConst ``Int.Linear.norm_dvd_gcd) (← toContextExpr atoms) (toExpr d) (toExpr e) (toExpr d') (toExpr p) (toExpr g) eagerReflBoolTrue
    return some (rhs, mkExpectedPropHint h (mkPropEq lhs rhs))
  else
    let rhs := mkConst ``False
    let h := mkApp4 (mkConst ``Int.Linear.dvd_eq_false) (← toContextExpr atoms) (toExpr d) (toExpr e) eagerReflBoolTrue
    return some (rhs, mkExpectedPropHint h (mkPropEq lhs rhs))

def simpExpr? (lhs : Expr) : MetaM (Option (Expr × Expr)) := do
  let (e, ctx) ← toLinearExpr lhs
  let p  := e.norm
  let e' := p.toExpr
  if e != e' then
    let h := mkApp4 (mkConst ``Int.Linear.Expr.eq_of_norm_eq) (← toContextExpr ctx) (toExpr e) (toExpr p) eagerReflBoolTrue
    let lhs ← e.denoteExpr (ctx[·]!)
    let rhs ← p.denoteExpr (ctx[·]!)
    return some (rhs, mkExpectedPropHint h (mkIntEq lhs rhs))
  else
    return none

end Lean.Meta.Simp.Arith.Int
