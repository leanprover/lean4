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

/-- Returns the S-polynomial for `p₁` and `p₂`. -/
def Poly.superpose (p₁ p₂ : Poly) : Poly :=
  match p₁, p₂ with
  | .add k₁ m₁ p₁, .add k₂ m₂ p₂ =>
    let m   := m₁.lcm m₂
    let g   := Nat.gcd k₁.natAbs k₂.natAbs
    let p₁  := p₁.mulMon (k₂/g) (m.div m₁)
    let p₂  := p₂.mulMon (-k₁/g) (m.div m₂)
    p₁.combine p₂
  | _, _ => .num 0

end Lean.Grind.CommRing
