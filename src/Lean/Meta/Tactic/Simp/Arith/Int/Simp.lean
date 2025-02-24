/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Simp.Arith.Util
import Lean.Meta.Tactic.Simp.Arith.Int.Basic

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
  withAbstractAtoms atoms ``Int fun atoms => do
    let e := mkIntEq (← a.denoteExpr (atoms[·]!)) (← b.denoteExpr (atoms[·]!))
    let p := a.sub b |>.norm
    if p.isUnsatEq then
      let r := mkConst ``False
      let h := mkApp4 (mkConst ``Int.Linear.eq_eq_false) (toContextExpr atoms) (toExpr a) (toExpr b) reflBoolTrue
      return some (r, ← mkExpectedTypeHint h (← mkEq e r))
    else if p.isValidEq then
      let r := mkConst ``True
      let h := mkApp4 (mkConst ``Int.Linear.eq_eq_true) (toContextExpr atoms) (toExpr a) (toExpr b) reflBoolTrue
      return some (r, ← mkExpectedTypeHint h (← mkEq e r))
    else if p.toExpr == a && b == .num 0 then
      return none
    else match p with
      | .add 1 x (.add (-1) y (.num 0)) =>
        let r := mkIntEq atoms[x]! atoms[y]!
        let h := mkApp6 (mkConst ``Int.Linear.norm_eq_var) (toContextExpr atoms) (toExpr a) (toExpr b) (toExpr x) (toExpr y) reflBoolTrue
        return some (r, ← mkExpectedTypeHint h (← mkEq e r))
      | .add 1 x (.num k) =>
        let r := mkIntEq atoms[x]! (toExpr (-k))
        let h := mkApp6 (mkConst ``Int.Linear.norm_eq_var_const) (toContextExpr atoms) (toExpr a) (toExpr b) (toExpr x) (toExpr (-k)) reflBoolTrue
        return some (r, ← mkExpectedTypeHint h (← mkEq e r))
      | _ =>
        let k := p.gcdCoeffs'
        if k == 1 then
          let r := mkIntEq (← p.denoteExpr (atoms[·]!)) (mkIntLit 0)
          let h := mkApp5 (mkConst ``Int.Linear.norm_eq) (toContextExpr atoms) (toExpr a) (toExpr b) (toExpr p) reflBoolTrue
          return some (r, ← mkExpectedTypeHint h (← mkEq e r))
        else if p.getConst % k == 0 then
          let p := p.div k
          let r := mkIntEq (← p.denoteExpr (atoms[·]!)) (mkIntLit 0)
          let h := mkApp6 (mkConst ``Int.Linear.norm_eq_coeff) (toContextExpr atoms) (toExpr a) (toExpr b) (toExpr p) (toExpr (Int.ofNat k)) reflBoolTrue
          return some (r, ← mkExpectedTypeHint h (← mkEq e r))
        else
          let r := mkConst ``False
          let h := mkApp5 (mkConst ``Int.Linear.eq_eq_false_of_divCoeff) (toContextExpr atoms) (toExpr a) (toExpr b) (toExpr (Int.ofNat k)) reflBoolTrue
          return some (r, ← mkExpectedTypeHint h (← mkEq e r))

def simpLe? (e : Expr) : MetaM (Option (Expr × Expr)) := do
  let some (a, b, atoms) ← leCnstr? e | return none
  withAbstractAtoms atoms ``Int fun atoms => do
    let e := mkIntLE (← a.denoteExpr (atoms[·]!)) (← b.denoteExpr (atoms[·]!))
    let p := a.sub b |>.norm
    if p.isUnsatLe then
      let r := mkConst ``False
      let h := mkApp4 (mkConst ``Int.Linear.le_eq_false) (toContextExpr atoms) (toExpr a) (toExpr b) reflBoolTrue
      return some (r, ← mkExpectedTypeHint h (← mkEq e r))
    else if p.isValidLe then
      let r := mkConst ``True
      let h := mkApp4 (mkConst ``Int.Linear.le_eq_true) (toContextExpr atoms) (toExpr a) (toExpr b) reflBoolTrue
      return some (r, ← mkExpectedTypeHint h (← mkEq e r))
    else if p.toExpr == a && b == .num 0 then
      return none
    else
      let k := p.gcdCoeffs'
      if k == 1 then
        let r := mkIntLE (← p.denoteExpr (atoms[·]!)) (mkIntLit 0)
        let h := mkApp5 (mkConst ``Int.Linear.norm_le) (toContextExpr atoms) (toExpr a) (toExpr b) (toExpr p) reflBoolTrue
        return some (r, ← mkExpectedTypeHint h (← mkEq e r))
      else
        let tight := p.getConst % k != 0
        let p := p.div k
        let r := mkIntLE (← p.denoteExpr (atoms[·]!)) (mkIntLit 0)
        let h := if tight then
          mkApp6 (mkConst ``Int.Linear.norm_le_coeff_tight) (toContextExpr atoms) (toExpr a) (toExpr b) (toExpr p) (toExpr (Int.ofNat k)) reflBoolTrue
        else
          mkApp6 (mkConst ``Int.Linear.norm_le_coeff) (toContextExpr atoms) (toExpr a) (toExpr b) (toExpr p) (toExpr (Int.ofNat k)) reflBoolTrue
        return some (r, ← mkExpectedTypeHint h (← mkEq e r))

def simpRel? (e : Expr) : MetaM (Option (Expr × Expr)) := do
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
      if let some (eNew', h₂) ← simpLe? eNew then
        let h  := mkApp6 (mkConst ``Eq.trans [levelOne]) (mkSort levelZero) e eNew eNew' h₁ h₂
        return some (eNew', h)
      else
        return some (eNew, h₁)
    else
      return none
  else
    simpLe? e

def simpDvd? (e : Expr) : MetaM (Option (Expr × Expr)) := do
  let some (d, e, atoms) ← dvdCnstr? e | return none
  if d == 0 then return none
  withAbstractAtoms atoms ``Int fun atoms => do
    let lhs := mkIntDvd (toExpr d) (← e.denoteExpr (atoms[·]!))
    let p := e.norm
    let g := p.gcdCoeffs d
    if p.getConst % g == 0 then
      let p := p.div g
      let d' := d / g
      if e == p.toExpr then
        return none
      let rhs := mkIntDvd (toExpr d') (← p.denoteExpr (atoms[·]!))
      let h := if g == 1 then
        mkApp5 (mkConst ``Int.Linear.norm_dvd) (toContextExpr atoms) (toExpr d) (toExpr e) (toExpr p) reflBoolTrue
      else
        mkApp7 (mkConst ``Int.Linear.norm_dvd_gcd) (toContextExpr atoms) (toExpr d) (toExpr e) (toExpr d') (toExpr p) (toExpr g) reflBoolTrue
      return some (rhs, ← mkExpectedTypeHint h (← mkEq lhs rhs))
    else
      let rhs := mkConst ``False
      let h := mkApp4 (mkConst ``Int.Linear.dvd_eq_false) (toContextExpr atoms) (toExpr d) (toExpr e) reflBoolTrue
      return some (rhs, ← mkExpectedTypeHint h (← mkEq lhs rhs))

def simpExpr? (lhs : Expr) : MetaM (Option (Expr × Expr)) := do
  let (e, atoms) ← toLinearExpr lhs
  let p  := e.norm
  let e' := p.toExpr
  if e != e' then
    -- We only return some if monomials were fused
    let h := mkApp4 (mkConst ``Int.Linear.Expr.eq_of_norm_eq) (toContextExpr atoms) (toExpr e) (toExpr p) reflBoolTrue
    let rhs ← p.denoteExpr (atoms[·]!)
    return some (rhs, ← mkExpectedTypeHint h (← mkEq lhs rhs))
  else
    return none

end Lean.Meta.Simp.Arith.Int
