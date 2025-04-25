/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Grind.CommRing.Poly
namespace Lean.Grind.CommRing

/-- `lcm m₁ m₂` returns the least common multiple of the given monomials. -/
def Mon.lcm : Mon → Mon → Mon
  | .unit, m₂ => m₂
  | m₁, .unit => m₁
  | .mult pw₁ m₁, .mult pw₂ m₂ =>
    match compare pw₁.x pw₂.x with
    | .eq => .mult { x := pw₁.x, k := max pw₁.k pw₂.k } (lcm m₁ m₂)
    | .lt => .mult pw₁ (lcm m₁ (.mult pw₂ m₂))
    | .gt => .mult pw₂ (lcm (.mult pw₁ m₁) m₂)

/--
`divides m₁ m₂` returns `true` if monomial `m₁` divides `m₂`
Example: `x^2.z` divides `w.x^3.y^2.z`
-/
def Mon.divides : Mon → Mon → Bool
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
def Mon.div : Mon → Mon → Mon
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
  c₁   : Int  := 0
  /-- Monomial factor applied to polynomial `p₁`. -/
  m₁   : Mon  := .unit
  /-- Coefficient applied to polynomial `p₂`. -/
  c₂   : Int  := 0
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
    { spol, c₁, m₁, c₂, m₂ }
  | _, _ => {}

/--
Result of simplifying a polynomial `p₂` using a polynomial `p₁`.

The simplification rewrites the first monomial of `p₂` that can be divided
by the leading monomial of `p₁`.
-/
structure SimpResult where
  /-- The resulting simplified polynomial after rewriting. -/
  p  : Poly := .num 0
  /-- The integer coefficient multiplied with polynomial `p₁` in the rewriting step. -/
  k₁ : Int  := 0
  /-- The integer coefficient multiplied with polynomial `p₂` during rewriting. -/
  k₂ : Int  := 0
  /-- The monomial factor applied to polynomial `p₁`. -/
  m  : Mon  := .unit

/--
Simplifies polynomial `p₂` using polynomial `p₁` by rewriting.

This function attempts to rewrite `p₂` by eliminating the first occurrence of
the leading monomial of `p₁`.

Remark: if `char? = some c`, then `c` is the characteristic of the ring.
-/
def Poly.simp? (p₁ p₂ : Poly) (char? : Option Nat := none) : Option SimpResult :=
  match p₁ with
  | .add k₁' m₁ p₁ =>
    let rec go? (p₂ : Poly) : Option SimpResult :=
      match p₂ with
      | .add k₂' m₂ p₂ =>
        if m₁.divides m₂ then
          let m  := m₂.div m₁
          let g  := Nat.gcd k₁'.natAbs k₂'.natAbs
          let k₁ := -k₂'/g
          let k₂ := k₁'/g
          let p  := (p₁.mulMon' k₁ m char?).combine' (p₂.mulConst' k₂ char?) char?
          some { p, k₁, k₂, m }
        else if let some r := go? p₂ then
          if let some char := char? then
            let k := (k₂'*r.k₂) % char
            if k == 0 then
              some r
            else
              some { r with p := .add k m₂ r.p }
          else
            some { r with p := .add (k₂'*r.k₂) m₂ r.p }
        else
          none
      | .num _ => none
    go? p₂
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

end Lean.Grind.CommRing
