/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Sym.Simp.SimpM
public import Lean.Meta.Sym.Simp.Discharger
import Lean.Meta.Sym.Simp.Result
import Lean.Meta.Sym.Arith.Norm
import Lean.Meta.Sym.LitValues
import Init.Grind.Norm
public section
namespace Lean.Meta.Sym.Simp

private def isRelation (e : Expr) : Bool :=
  match_expr e with
  | Eq _ _ _ => true
  | LE.le _ _ _ _ => true
  | LT.lt _ _ _ _ => true
  | _ => false

/-- Caches `e` as a final result: it is a normal form, so a later visit costs a lookup. -/
private def cacheNormal (e : Expr) (cd : Bool) : SimpM Unit :=
  discard <| cacheResult e (mkRflResult (done := true) (contextDependent := cd))

/--
Given the normalized relation `e'` (with `h? : e = e'`, or `none` when `e'` is `e`), caches
its sides as normal forms, applies `post` to it, and chains the results.
-/
private def postRelation (e e' : Expr) (h? : Option Expr) (cd : Bool) : SimpM Result := do
  cacheNormal e'.appFn!.appArg! cd
  cacheNormal e'.appArg! cd
  match (← post e'), h? with
  | .rfl _ cd₂, none => return mkRflResult (done := true) (contextDependent := cd || cd₂)
  | .rfl _ cd₂, some h => return .step e' h (done := true) (contextDependent := cd || cd₂)
  | r₂, none => return if cd && !r₂.isContextDependent then r₂.withContextDependent else r₂
  | r₂, some h => mkEqTransResult e e' h r₂ cd

/--
Normalizes ring and semiring terms and relations into polynomial normal form
(`Sym.Arith.normalize?`), simplifying the atoms with `simp`. Intended as a `pre` simproc: it
sees the maximal arithmetic subtree first and reifies it once.

A normal form is final (`done := true`): `simp` does not re-enter it, so the normalizer never
runs on its own output, and it is cached so that reaching it again costs a lookup. Terms and
relations differ in what `post` sees:
* A normalized **term** is not visited by `post`. Rewrite rules on arithmetic operators are
  what the normalizer supersedes.
* A normalized **relation** (`=`, `≤`, `<`) is handed to `post` here, exactly once, and the
  result is chained in. This is how `t = t` and ground comparisons are closed
  (`evalGround`), and how rewrite rules on relations apply after normalization. Its two
  sides are cached as normal forms. If `post` rewrites the relation, that step is not final
  and `simp` continues on the result as usual.

The discharger `d` proves the side conditions `x ≠ 0` under which `x * x⁻¹` is cancelled in a
field. With `lhsOnly := true`, relations over rings are normalized to `p = 0`, `p ≤ 0`, `p < 0`
instead of being split by sign; see `Arith.normalize?`.
-/
def simpArith (d : Discharger := dischargeNone) (lhsOnly : Bool := false) : Simproc := fun e => do
  let r ← Arith.normalize? e simp (lhsOnly := lhsOnly) fun p => do
    match (← d p) with
    | .solved h _ => return some h
    | .failed _ => return none
  match r with
  | .rfl true cd =>
    if isRelation e then postRelation e e none cd else return r
  | .step e' h true cd =>
    if isRelation e then
      postRelation e e' (some h) cd
    else
      cacheNormal e' cd
      return r
  | _ => return r

/--
Returns `some k` if `e` is `a + (k + 1)` for a numeral `k + 1`, i.e., the normal form of a
`Nat` polynomial with a positive constant, which is nonzero for every value of its atoms.
-/
private def isNatAddSucc? (e : Expr) : Option (Expr × Nat) := do
  let_expr HAdd.hAdd _ _ _ _ a k := e | none
  let k ← (Sym.getNatValue? k).run
  if k == 0 then none else some (a, k - 1)

/-- Returns `true` if `e` is the numeral `0`. -/
private def isNatZero (e : Expr) : Bool :=
  match (Sym.getNatValue? e).run with
  | some 0 => true
  | _ => false

/--
Decides the `Nat` relations that are trivially unsatisfiable or valid after normalization by
`simpArith`, like `Nat.Linear` does in `simp +arith`: `a + k = 0`, `0 = a + k`, and
`a + k ≤ 0` become `False` for a positive numeral `k`, and `0 ≤ a` becomes `True`.
The other ground cases (`k = 0`, `0 ≤ k`) are handled by `evalGround`. Intended as a
`post` simproc, after `simpArith` has cancelled the common part of the two sides.
-/
def simpNatRel : Simproc := fun e => do
  match_expr e with
  | Eq α lhs rhs =>
    let .const ``Nat _ := α | return .rfl
    if isNatZero rhs then
      if let some (a, k) := isNatAddSucc? lhs then
        return .step (← getFalseExpr) (mkApp2 (mkConst ``Grind.Nat.add_succ_eq_zero_eq_false) a (mkRawNatLit k)) (done := true)
    else if isNatZero lhs then
      if let some (a, k) := isNatAddSucc? rhs then
        return .step (← getFalseExpr) (mkApp2 (mkConst ``Grind.Nat.zero_eq_add_succ_eq_false) a (mkRawNatLit k)) (done := true)
    return .rfl
  | LE.le α _ lhs rhs =>
    let .const ``Nat _ := α | return .rfl
    if isNatZero lhs then
      return .step (← getTrueExpr) (mkApp (mkConst ``Grind.Nat.zero_le_eq_true) rhs) (done := true)
    else if isNatZero rhs then
      if let some (a, k) := isNatAddSucc? lhs then
        return .step (← getFalseExpr) (mkApp2 (mkConst ``Grind.Nat.add_succ_le_zero_eq_false) a (mkRawNatLit k)) (done := true)
    return .rfl
  | _ => return .rfl

end Lean.Meta.Sym.Simp
