/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Sym.Arith.Types
public import Lean.Meta.Sym.Arith.Poly
public import Lean.Meta.Sym.SymM
import Lean.Meta.Sym.Arith.EvalNum
public section
namespace Lean.Meta.Sym.Arith

/-!
# Guarded polynomial computation

The polynomial functions in `Init` (`Expr.toPoly`, `Expr.toPolyC`, `Expr.toPolyS`, and the
operations they use) are pure and unbounded. The functions below compute the same results in
`SymM`, so that the computation can be interrupted (`checkSystem`, `withIncRecDepth`), refuses
exponents above the `exp` threshold (`checkExp`), and can be bounded by a budget on the number
of monomials and the degree.

They must be case-by-case mirrors of the `Init` functions: proofs by reflection compare the
kernel's evaluation of the `Init` function with the result computed here, so any divergence is
a proof failure.
-/

structure PolyConfig where
  /-- Nonzero characteristic. When `some c`, mirrors `Expr.toPolyC c` (or `toPolyS`, which has no characteristic support). -/
  char?     : Option Nat := none
  /-- When `true`, mirrors `Expr.toPolyS` (semiring: nonnegative coefficients, no subtraction). -/
  semiring  : Bool := false
  /-- When `false`, mirrors the non-commutative functions (`toPoly_nc`, `toPolyC_nc`, `toPolyS_nc`). -/
  commutative : Bool := true
  /-- Maximum number of monomials of any intermediate polynomial. -/
  maxTerms? : Option Nat := none
  /-- Maximum degree of any intermediate polynomial. -/
  maxDegree? : Option Nat := none

/-- Polynomial computations that may fail (budget, exponent threshold). -/
abbrev PolyM := ReaderT PolyConfig (OptionT SymM)

def PolyM.run (x : PolyM α) (cfg : PolyConfig := {}) : SymM (Option α) :=
  (x cfg).run

namespace SafePoly

private def applyChar (a : Int) : PolyM Int := do
  if let some c := (← read).char? then
    return a % c
  else
    return a

private def checkBudget (p : Poly) : PolyM Unit := do
  let cfg ← read
  if let some maxTerms := cfg.maxTerms? then
    let n := p.numTerms
    if n > maxTerms then
      reportIssue! "polynomial with {n} monomials exceeds threshold `(sym.arith.maxTerms := {maxTerms})`"
      failure
  if let some maxDegree := cfg.maxDegree? then
    let d := p.degree
    if d > maxDegree then
      reportIssue! "polynomial of degree {d} exceeds threshold `(sym.arith.maxDegree := {maxDegree})`"
      failure

def addConst (p : Poly) (k : Int) : PolyM Poly := do
  if let some c := (← read).char? then return .addConstC p k c else return .addConst p k

def mulConst (k : Int) (p : Poly) : PolyM Poly := do
  if let some c := (← read).char? then return .mulConstC k p c else return .mulConst k p

def mulMon (k : Int) (m : Mon) (p : Poly) : PolyM Poly := do
  let cfg ← read
  match cfg.commutative, cfg.char? with
  | true,  none   => return .mulMon k m p
  | true,  some c => return .mulMonC k m p c
  | false, none   => return .mulMon_nc k m p
  | false, some c => return .mulMonC_nc k m p c

private partial def combineCore (p₁ p₂ : Poly) : PolyM Poly := withIncRecDepth do
  match p₁, p₂ with
  | .num k₁, .num k₂ => return .num (← applyChar (k₁ + k₂))
  | .num k₁, .add k₂ m₂ p₂ => addConst (.add k₂ m₂ p₂) k₁
  | .add k₁ m₁ p₁, .num k₂ => addConst (.add k₁ m₁ p₁) k₂
  | .add k₁ m₁ p₁, .add k₂ m₂ p₂ =>
    match m₁.grevlex m₂ with
    | .eq =>
      let k ← applyChar (k₁ + k₂)
      bif k == 0 then
        combineCore p₁ p₂
      else
        return .add k m₁ (← combineCore p₁ p₂)
    | .gt => return .add k₁ m₁ (← combineCore p₁ (.add k₂ m₂ p₂))
    | .lt => return .add k₂ m₂ (← combineCore (.add k₁ m₁ p₁) p₂)

/-- Mirror of `Poly.combine` (`Poly.combineC` with a characteristic). -/
def combine (p₁ p₂ : Poly) : PolyM Poly := do
  let p ← combineCore p₁ p₂
  checkBudget p
  return p

/-- Mirror of `Poly.mul` (`Poly.mulC`, `Poly.mul_nc`, `Poly.mulC_nc`); `mulMon` selects the variant. -/
def mul (p₁ : Poly) (p₂ : Poly) : PolyM Poly :=
  go p₁ (.num 0)
where
  go (p₁ : Poly) (acc : Poly) : PolyM Poly := withIncRecDepth do
    match p₁ with
    | .num k => combine acc (← mulConst k p₂)
    | .add k m p₁ =>
      checkSystem "sym arith poly"
      go p₁ (← combine acc (← mulMon k m p₂))

/-- Mirror of `Poly.pow` (`Poly.powC`): `p * pow p k`. -/
private def powComm (p : Poly) (k : Nat) : PolyM Poly := withIncRecDepth do
  match k with
  | 0 => return .num 1
  | 1 => return p
  | 2 => mul p p
  | k+3 => mul p (← powComm p (k+2))

/-- Mirror of `Poly.pow_nc` (`Poly.powC_nc`): `pow_nc p k * p`. -/
private def powNC (p : Poly) (k : Nat) : PolyM Poly := withIncRecDepth do
  match k with
  | 0 => return .num 1
  | 1 => return p
  | k+2 => mul (← powNC p (k+1)) p

def pow (p : Poly) (k : Nat) : PolyM Poly := do
  if (← read).commutative then powComm p k else powNC p k

private def checkExp' (k : Nat) : PolyM Unit :=
  fun _ => checkExp k

private def mkPowVar (x : Var) (k : Nat) : PolyM Poly := do
  if let some maxDegree := (← read).maxDegree? then
    if k > maxDegree then
      reportIssue! "polynomial of degree {k} exceeds threshold `(sym.arith.maxDegree := {maxDegree})`"
      failure
  return .ofMon (.mult {x, k} .unit)

/-- Mirror of `Expr.toPoly`, `Expr.toPolyC`, `Expr.toPoly_nc`, `Expr.toPolyC_nc`. -/
private partial def toPolyRing (e : RingExpr) : PolyM Poly := do
  match e with
  | .intCast n | .natCast n
  | .num n   => return .num (← applyChar n)
  | .var x   => return .ofVar x
  | .add a b => combine (← toPolyRing a) (← toPolyRing b)
  | .mul a b => mul (← toPolyRing a) (← toPolyRing b)
  | .neg a   => mulConst (-1) (← toPolyRing a)
  | .sub a b => combine (← toPolyRing a) (← mulConst (-1) (← toPolyRing b))
  | .pow a k =>
    if k == 0 then
      return .num 1
    else match a with
    | .num n =>
      checkExp' k
      return .num (← applyChar (n^k))
    | .var x => mkPowVar x k
    | _ => pow (← toPolyRing a) k

/-- Mirror of `Expr.toPolyS` and `Expr.toPolyS_nc`. -/
private partial def toPolySemiring (e : SemiringExpr) : PolyM Poly := do
  match e with
  | .num n   => return .num n.natAbs
  | .natCast n => return .num n
  | .var x   => return .ofVar x
  | .add a b => combine (← toPolySemiring a) (← toPolySemiring b)
  | .mul a b => mul (← toPolySemiring a) (← toPolySemiring b)
  | .pow a k =>
    if k == 0 then
      return .num 1
    else match a with
    | .num n =>
      checkExp' k
      return .num (n.natAbs ^ k)
    | .var x => mkPowVar x k
    | _ => pow (← toPolySemiring a) k
  | .sub .. | .neg .. | .intCast .. => return .num 0

end SafePoly

/--
Converts `e` into a polynomial, mirroring `Expr.toPoly`, `Expr.toPolyC c`, `Expr.toPolyS`, or
their non-commutative variants, depending on the configuration. Returns `none` if the computation exceeds the budget or the
exponent threshold.
-/
def toPoly? (e : RingExpr) : PolyM Poly := do
  if (← read).semiring then
    SafePoly.toPolySemiring e
  else
    SafePoly.toPolyRing e

end Lean.Meta.Sym.Arith
