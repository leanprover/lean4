/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Arith.CommRing.RingM
public import Lean.Meta.Sym.Arith.Poly
public import Lean.Meta.Sym.Arith.SafePoly
import Init.Data.Nat.Internal.Linear
public section
namespace Lean.Meta.Grind.Arith.CommRing
open Sym.Arith
/-!
The polynomial functions at `Poly.lean` are used for constructing proofs-by-reflection,
but they do not provide mechanisms for aborting expensive computations.
The guarded versions live in `Sym.Arith.SafePoly`; the wrappers below run them with the
characteristic of the current ring and no budget.
-/

private abbrev runPoly (x : PolyM α) : RingM (Option α) := do
  x.run { char? := (← nonzeroChar?) }

private abbrev runPoly! (x : PolyM α) : RingM α := do
  let some r ← runPoly x
    | throwError "`grind` internal error, polynomial computation failed"
  return r

/--
Converts the given ring expression into a multivariate polynomial.
If the ring has a nonzero characteristic, it is used during normalization.
-/
def _root_.Lean.Grind.CommRing.Expr.toPolyM? (e : RingExpr) : RingM (Option Poly) :=
  runPoly (toPoly? e)

def _root_.Lean.Grind.CommRing.Poly.mulConstM (p : Poly) (k : Int) : RingM Poly :=
  runPoly! (SafePoly.mulConst k p)

def _root_.Lean.Grind.CommRing.Poly.mulMonM (p : Poly) (k : Int) (m : Mon) : RingM Poly :=
  runPoly! (SafePoly.mulMon k m p)

def _root_.Lean.Grind.CommRing.Poly.mulM (p₁ p₂ : Poly) : RingM Poly :=
  runPoly! (SafePoly.mul p₁ p₂)

def _root_.Lean.Grind.CommRing.Poly.combineM (p₁ p₂ : Poly) : RingM Poly :=
  runPoly! (SafePoly.combine p₁ p₂)

def _root_.Lean.Grind.CommRing.Poly.spolM (p₁ p₂ : Poly) : RingM Grind.CommRing.SPolResult := do
  match p₁, p₂ with
  | .add k₁ m₁ p₁, .add k₂ m₂ p₂ =>
    let m    := m₁.lcm m₂
    let m₁   := m.div m₁
    let m₂   := m.div m₂
    let g    := Nat.gcd k₁.natAbs k₂.natAbs
    let c₁   := k₂/g
    let c₂   := -k₁/g
    let p₁   ← p₁.mulMonM c₁ m₁
    let p₂   ← p₂.mulMonM c₂ m₂
    let spol ← p₁.combineM p₂
    return { spol, m₁, m₂, k₁ := c₁, k₂ := c₂ }
  | _, _ => return {}

/-- Returns `some (val, x)` if `m` contains a variable `x` whose the denotation is `val⁻¹`. -/
def _root_.Lean.Grind.CommRing.Mon.findInvNumeralVar? (m : Mon) : RingM (Option (Nat × Var)) := do
  match m with
  | .unit => return none
  | .mult pw m =>
    let e := (← getRingState).vars[pw.x]!
    let_expr Inv.inv _ _ a := e | m.findInvNumeralVar?
    let_expr OfNat.ofNat _ n _ := a | m.findInvNumeralVar?
    let some n ← getNatValue? n | m.findInvNumeralVar?
    return some (n, pw.x)

/-- Returns `some (val, x)` if `p` contains a variable `x` whose the denotation is `val⁻¹`. -/
def _root_.Lean.Grind.CommRing.Poly.findInvNumeralVar? (p : Poly) : RingM (Option (Nat × Var)) := do
  match p with
  | .num _ => return none
  | .add _ m p =>
    let some r ← m.findInvNumeralVar? | p.findInvNumeralVar?
    return some r

/--
Result of simplifying a polynomial `p₁` using a polynomial `p₂`.

The simplification rewrites the first monomial of `p₁` that can be divided
by the leading monomial of `p₂`.
-/
structure SimpResult where
  /-- The resulting simplified polynomial after rewriting. -/
  p  : Poly := .num 0
  /-- The integer coefficient multiplied with polynomial `p₁` in the rewriting step. -/
  k₁ : Int  := 0
  /-- The integer coefficient multiplied with polynomial `p₂` during rewriting. -/
  k₂ : Int  := 0
  /-- The monomial factor applied to polynomial `p₂`. -/
  m₂ : Mon  := .unit

/--
Simplifies polynomial `p₁` using polynomial `p₂` by rewriting.

This function attempts to rewrite `p₁` by eliminating the first occurrence of
the leading monomial of `p₂`.

If `checkCoeffDvd` is `true` (and the ring does not implement `NoNatZeroDivisors`),
a monomial is rewritten only if its coefficient is divisible by the leading
coefficient of `p₂`, i.e., only if the rewrite does not multiply `p₁` by a
constant `k₁ ≠ ±1`. See `RingM.Context.checkCoeffDvd`.
-/
def _root_.Lean.Grind.CommRing.Poly.simpM? (p₁ p₂ : Poly) : RingM (Option SimpResult) := do
  match p₂ with
  | .add k₂' m₂ p₂ =>
    let checkCoeff := (← checkCoeffDvd) && !(← noZeroDivisors)
    let rec go? (p₁ : Poly) : RingM (Option SimpResult) := do
      match p₁ with
      | .add k₁' m₁ p₁ =>
        if m₂.divides m₁ && (!checkCoeff || k₂' ∣ k₁') then
          let m₂ := m₁.div m₂
          let g  := Nat.gcd k₁'.natAbs k₂'.natAbs
          let k₁ := k₂'/g
          let k₂ := -k₁'/g
          let p  ← (← p₂.mulMonM k₂ m₂).combineM (← p₁.mulConstM k₁)
          return some { p, k₁, k₂, m₂ }
        else if let some r ← go? p₁ then
          if let some char ← nonzeroChar? then
            let k := (k₁'*r.k₁) % char
            if k == 0 then
              return some r
            else
              return some { r with p := .add k m₁ r.p }
          else
            return some { r with p := .add (k₁'*r.k₁) m₁ r.p }
        else
          return none
      | .num _ => return none
    go? p₁
  | _ => return none

end Lean.Meta.Grind.Arith.CommRing
