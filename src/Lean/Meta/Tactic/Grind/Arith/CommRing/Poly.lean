/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Init.Grind.Ring.CommSolver
import Init.Data.Nat.Gcd
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Linear
import Init.WFTactics
public section
namespace Lean.Grind.CommRing

/-- `sharesVar m₁ m₂` returns `true` if `m₁` and `m₂` shares at least one variable. -/
def Mon.sharesVar : Mon → Mon → Bool
  | .unit, _ => false
  | _, .unit => false
  | .mult pw₁ m₁, .mult pw₂ m₂ =>
    match compare pw₁.x pw₂.x with
    | .eq => true
    | .lt => sharesVar m₁ (.mult pw₂ m₂)
    | .gt => sharesVar (.mult pw₁ m₁) m₂

/-- `lcm m₁ m₂` returns the least common multiple of the given monomials. -/
def Mon.lcm : Mon → Mon → Mon
  | .unit, m₂ => m₂
  | m₁, .unit => m₁
  | .mult pw₁ m₁, .mult pw₂ m₂ =>
    match compare pw₁.x pw₂.x with
    | .eq => .mult { x := pw₁.x, k := max pw₁.k pw₂.k } (lcm m₁ m₂)
    | .lt => .mult pw₁ (lcm m₁ (.mult pw₂ m₂))
    | .gt => .mult pw₂ (lcm (.mult pw₁ m₁) m₂)

-- Remark: we expose `Mon.divides` and `Mon.div` because we use then to write tests using `rfl`

/--
`divides m₁ m₂` returns `true` if monomial `m₁` divides `m₂`
Example: `x^2.z` divides `w.x^3.y^2.z`
-/
@[expose] def Mon.divides : Mon → Mon → Bool
  | .unit, _ => true
  | _, .unit => false
  | .mult pw₁ m₁, .mult pw₂ m₂ =>
    match compare pw₁.x pw₂.x with
    | .eq => pw₁.k ≤ pw₂.k && divides m₁ m₂
    | .lt => false
    | .gt => divides (.mult pw₁ m₁) m₂

/--
Given `m₁` and `m₂` such that `m₂.divides m₁`, then
`m₁.div m₂` returns the result.
Example `w.x^3.y^2.z` div `x^2.z` returns `w.x.y^2`
-/
@[expose] def Mon.div : Mon → Mon → Mon
  | m₁, .unit => m₁
  | .unit, _  => .unit -- reachable only if pre-condition does not hold
  | .mult pw₁ m₁, .mult pw₂ m₂ =>
    match compare pw₁.x pw₂.x with
    | .eq =>
      let k := pw₁.k - pw₂.k
      if k == 0 then
        div m₁ m₂
      else
        .mult { x := pw₁.x, k } (div m₁ m₂)
    | .lt => .mult pw₁ (div m₁ (.mult pw₂ m₂))
    | .gt => .unit -- reachable only if pre-condition does not hold

/--
`coprime m₁ m₂` returns `true` if the given monomials
do not have any variable in common.
-/
def Mon.coprime : Mon → Mon → Bool
  | .unit, _ => true
  | _, .unit => true
  | .mult pw₁ m₁, .mult pw₂ m₂ =>
    match compare pw₁.x pw₂.x with
    | .eq => false
    | .lt => coprime m₁ (.mult pw₂ m₂)
    | .gt => coprime (.mult pw₁ m₁) m₂

/--
Contains the S-polynomial resulting from superposing two polynomials `p₁` and `p₂`,
along with coefficients and monomials used in their construction.
-/
structure SPolResult where
  /-- The computed S-polynomial. -/
  spol : Poly := .num 0
  /-- Coefficient applied to polynomial `p₁`. -/
  k₁   : Int  := 0
  /-- Monomial factor applied to polynomial `p₁`. -/
  m₁   : Mon  := .unit
  /-- Coefficient applied to polynomial `p₂`. -/
  k₂   : Int  := 0
  /-- Monomial factor applied to polynomial `p₂`. -/
  m₂   : Mon  := .unit

def Poly.mulConst' (p : Poly) (k : Int) (char? : Option Nat := none) : Poly :=
  if let some char := char? then p.mulConstC k char else p.mulConst k

def Poly.mulMon' (p : Poly) (k : Int) (m : Mon) (char? : Option Nat := none) : Poly :=
  if let some char := char? then p.mulMonC k m char else p.mulMon k m

def Poly.combine' (p₁ p₂ : Poly) (char? : Option Nat := none) : Poly :=
  if let some char := char? then p₁.combineC p₂ char else p₁.combine p₂

/--
Returns the S-polynomial of polynomials `p₁` and `p₂`, and coefficients&terms used to construct it.
Given polynomials with leading terms `k₁*m₁` and `k₂*m₂`, the S-polynomial is defined as:
```
S(p₁, p₂) = (k₂/gcd(k₁, k₂)) * (lcm(m₁, m₂)/m₁) * p₁ - (k₁/gcd(k₁, k₂)) * (lcm(m₁, m₂)/m₂) * p₂
```
Remark: if `char? = some c`, then `c` is the characteristic of the ring.
-/
def Poly.spol (p₁ p₂ : Poly) (char? : Option Nat := none) : SPolResult  :=
  match p₁, p₂ with
  | .add k₁ m₁ p₁, .add k₂ m₂ p₂ =>
    let m    := m₁.lcm m₂
    let m₁   := m.div m₁
    let m₂   := m.div m₂
    let g    := Nat.gcd k₁.natAbs k₂.natAbs
    let c₁   := k₂/g
    let c₂   := -k₁/g
    let p₁   := p₁.mulMon' c₁ m₁ char?
    let p₂   := p₂.mulMon' c₂ m₂ char?
    let spol := p₁.combine' p₂ char?
    { spol, m₁, m₂, k₁ := c₁, k₂ := c₂ }
  | _, _ => {}

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

Remark: if `char? = some c`, then `c` is the characteristic of the ring.
-/
def Poly.simp? (p₁ p₂ : Poly) (char? : Option Nat := none) : Option SimpResult :=
  match p₂ with
  | .add k₂' m₂ p₂ =>
    let rec go? (p₁ : Poly) : Option SimpResult :=
      match p₁ with
      | .add k₁' m₁ p₁ =>
        if m₂.divides m₁ then
          let m₂ := m₁.div m₂
          let g  := Nat.gcd k₁'.natAbs k₂'.natAbs
          let k₁ := k₂'/g
          let k₂ := -k₁'/g
          let p  := (p₂.mulMon' k₂ m₂ char?).combine' (p₁.mulConst' k₁ char?) char?
          some { p, k₁, k₂, m₂ }
        else if let some r := go? p₁ then
          if let some char := char? then
            let k := (k₁'*r.k₁) % char
            if k == 0 then
              some r
            else
              some { r with p := .add k m₁ r.p }
          else
            some { r with p := .add (k₁'*r.k₁) m₁ r.p }
        else
          none
      | .num _ => none
    go? p₁
  | _ => none

def Poly.degree : Poly → Nat
  | .num _ => 0
  | .add _ m _ => m.degree

/-- Returns `true` if the leading monomial of `p` divides `m`. -/
def Poly.divides (p : Poly) (m : Mon) : Bool :=
  match p with
  | .num _ => true -- should be unreachable
  | .add _ m' _ => m'.divides m

/-- Returns the leading coefficient of the given polynomial -/
def Poly.lc : Poly → Int
 | .num k => k
 | .add k _ _ => k

/-- Returns the leading monomial of the given polynomial. -/
def Poly.lm : Poly → Mon
 | .num _ => .unit
 | .add _ m _ => m

def Poly.isZero : Poly → Bool
  | .num 0 => true
  | _ => false

def Poly.getConst : Poly → Int
  | .num k => k
  | .add _ _ p => p.getConst

def Poly.checkCoeffs : Poly → Bool
  | .num _ => true
  | .add k _ p => k != 0 && checkCoeffs p

def Poly.checkNoUnitMon : Poly → Bool
  | .num _ => true
  | .add _ .unit _ => false
  | .add _ _ p => p.checkNoUnitMon

def Poly.gcdCoeffs : Poly → Nat
  | .num k => k.natAbs
  | .add k _ p => go p k.natAbs
where
  go (p : Poly) (acc : Nat) : Nat :=
    if acc == 1 then
      acc
    else match p with
      | .num k => Nat.gcd acc k.natAbs
      | .add k _ p => go p (Nat.gcd acc k.natAbs)

def Poly.divConst (p : Poly) (a : Int) : Poly :=
  match p with
  | .num k => .num (k / a)
  | .add k m p => .add (k / a) m (divConst p a)

def Mon.size : Mon → Nat
  | .unit => 0
  | .mult _ m => m.size + 1

def Poly.size : Poly → Nat
  | .num _ => 1
  | .add _ m p => m.size + 1 + p.size

def Poly.length : Poly → Nat
  | .num _ => 0
  | .add _ _ p => 1 + p.length

def Power.toExpr (pw : Power) : Expr :=
  if pw.k == 1 then
    .var pw.x
  else
    .pow (.var pw.x) pw.k

def Mon.toExpr (m : Mon) : Expr :=
  match m with
  | .unit => .num 1
  | .mult pw m => go m pw.toExpr
where
  go (m : Mon) (acc : Expr) : Expr :=
    match m with
    | .unit => acc
    | .mult pw m => go m (.mul acc pw.toExpr)

def Poly.toExpr (p : Poly) : Expr :=
  match p with
  | .num k => .num k
  | .add k m p => go p (goTerm k m)
where
  goTerm (k : Int) (m : Mon) : Expr :=
    if k == 1 then
      m.toExpr
    else
      .mul (.num k) m.toExpr

  go (p : Poly) (acc : Expr) : Expr :=
    match p with
    | .num 0 => acc
    | .num k => .add acc (.num k)
    | .add k m p => go p (.add acc (goTerm k m))

def Poly.maxDegreeOf (p : Poly) (x : Var) : Nat :=
  go p 0
where
  go (p : Poly) (max : Nat) : Nat :=
    match p with
    | .num _ => max
    | .add _ m p => go p (Nat.max max (m.degreeOf x))

end Lean.Grind.CommRing
