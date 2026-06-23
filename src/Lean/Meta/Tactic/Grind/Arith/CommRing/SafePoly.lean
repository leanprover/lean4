/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Arith.CommRing.RingM
public import Lean.Meta.Sym.Arith.Poly
import Lean.Meta.Tactic.Grind.Arith.EvalNum
import Init.Data.Nat.Linear
public section
namespace Lean.Meta.Grind.Arith.CommRing
/-!
The polynomial functions at `Poly.lean` are used for constructing proofs-by-reflection,
but they do not provide mechanisms for aborting expensive computations.
-/
private def applyChar (a : Int) : RingM Int := do
  if let some c ← nonzeroChar? then
    return a % c
  else
    return a

private def addConst (p : Poly) (k : Int) : RingM Poly := do
  if let some c ← nonzeroChar? then return .addConstC p k c else return .addConst p k

private def mulConst (k : Int) (p : Poly) : RingM Poly := do
  if let some c ← nonzeroChar? then return .mulConstC k p c else return .mulConst k p

private def mulMon (k : Int) (m : Mon) (p : Poly) : RingM Poly := do
  if let some c ← nonzeroChar? then return .mulMonC k m p c else return .mulMon k m p

private def combine (p₁ p₂ : Poly) : RingM Poly := withIncRecDepth do
  match p₁, p₂ with
  | .num k₁, .num k₂ => return .num (← applyChar (k₁ + k₂))
  | .num k₁, .add k₂ m₂ p₂ => addConst (.add k₂ m₂ p₂) k₁
  | .add k₁ m₁ p₁, .num k₂ => addConst (.add k₁ m₁ p₁) k₂
  | .add k₁ m₁ p₁, .add k₂ m₂ p₂ =>
    match m₁.grevlex m₂ with
    | .eq =>
      let k ← applyChar (k₁ + k₂)
      bif k == 0 then
        combine p₁ p₂
      else
        return .add k m₁ (← combine p₁ p₂)
    | .gt => return .add k₁ m₁ (← combine p₁ (.add k₂ m₂ p₂))
    | .lt => return .add k₂ m₂ (← combine (.add k₁ m₁ p₁) p₂)

private def mul (p₁ : Poly) (p₂ : Poly) : RingM Poly :=
  go p₁ (.num 0)
where
  go (p₁ : Poly) (acc : Poly) : RingM Poly :=  withIncRecDepth do
    match p₁ with
    | .num k => combine acc (← mulConst k p₂)
    | .add k m p₁ =>
      checkSystem "grind ring"
      go p₁ (← combine acc (← mulMon k m p₂))

private def pow (p : Poly) (k : Nat) : RingM Poly := withIncRecDepth do
  match k with
  | 0 => return .num 1
  | 1 => return p
  | 2 => mul p p
  | k+3 => mul p (← pow p (k+2))

private def toPoly (e : RingExpr) : OptionT RingM Poly := do
  match e with
  | .intCast n | .natCast n
  | .num n   => return .num (← applyChar n)
  | .var x   => return .ofVar x
  | .add a b => combine (← toPoly a) (← toPoly b)
  | .mul a b => mul (← toPoly a) (← toPoly b)
  | .neg a   => mulConst (-1) (← toPoly a)
  | .sub a b => combine (← toPoly a) (← mulConst (-1) (← toPoly b))
  | .pow a k =>
    if k == 0 then
      return .num 1
    else match a with
    | .num n =>
      guard (← checkExp k |>.run).isSome
      return .num (← applyChar (n^k))
    | .var x => return .ofMon (.mult {x, k} .unit)
    | _ => pow (← toPoly a) k

/--
Converts the given ring expression into a multivariate polynomial.
If the ring has a nonzero characteristic, it is used during normalization.
-/
@[inline] def _root_.Lean.Grind.CommRing.Expr.toPolyM? (e : RingExpr) : RingM (Option Poly) := do
  toPoly e

@[inline] def _root_.Lean.Grind.CommRing.Poly.mulConstM (p : Poly) (k : Int) : RingM Poly :=
  mulConst k p

@[inline] def _root_.Lean.Grind.CommRing.Poly.mulMonM (p : Poly) (k : Int) (m : Mon) : RingM Poly :=
  mulMon k m p

@[inline] def _root_.Lean.Grind.CommRing.Poly.mulM (p₁ p₂ : Poly) : RingM Poly := do
  mul p₁ p₂

@[inline] def _root_.Lean.Grind.CommRing.Poly.combineM (p₁ p₂ : Poly) : RingM Poly :=
  combine p₁ p₂

def _root_.Lean.Grind.CommRing.Poly.spolM (p₁ p₂ : Poly) : RingM Grind.CommRing.SPolResult := do
  match p₁, p₂ with
  | .add k₁ m₁ p₁, .add k₂ m₂ p₂ =>
    let m    := m₁.lcm m₂
    let m₁   := m.div m₁
    let m₂   := m.div m₂
    let g    := Nat.gcd k₁.natAbs k₂.natAbs
    let c₁   := k₂/g
    let c₂   := -k₁/g
    let p₁   ← mulMon c₁ m₁ p₁
    let p₂   ← mulMon c₂ m₂ p₂
    let spol ← combine p₁ p₂
    return { spol, m₁, m₂, k₁ := c₁, k₂ := c₂ }
  | _, _ => return {}

/-- Returns `some (val, x)` if `m` contains a variable `x` whose the denotation is `val⁻¹`. -/
def _root_.Lean.Grind.CommRing.Mon.findInvNumeralVar? (m : Mon) : RingM (Option (Nat × Var)) := do
  match m with
  | .unit => return none
  | .mult pw m =>
    let e := (← getRing).vars[pw.x]!
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
-/
def _root_.Lean.Grind.CommRing.Poly.simpM? (p₁ p₂ : Poly) : RingM (Option SimpResult) := do
  match p₂ with
  | .add k₂' m₂ p₂ =>
    let rec go? (p₁ : Poly) : RingM (Option SimpResult) := do
      match p₁ with
      | .add k₁' m₁ p₁ =>
        if m₂.divides m₁ then
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
