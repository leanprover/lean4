/-!
Tests for the Euclidean remainder step in the `grind` ring solver. In rings without
`NoNatZeroDivisors`, an equation with leading term `k*m` now rewrites a monomial `k'*m`
with `|k| < |k'|` and `k ∤ k'` into `(k' % k)*m` instead of skipping it.
-/
open Lean.Grind

example {α} [CommRing α] (x y : α) (h₁ : 2*x = y) (h₂ : 3*x = y + 1) : x = 1 := by
  grobner

example {α} [CommRing α] (x y : α) (h₁ : 2*x^2 = y) (h₂ : 3*x^2 = y + x) : x^2 = x := by
  grobner

example {α} [CommRing α] (x : α) (h₁ : 4*x^2 = x) (h₂ : 6*x^2 = 1) : 2*x^2 = 1 - x := by
  grobner

example {α} [CommRing α] (x : α) (h₁ : 5*x = 1) (h₂ : 3*x = 2) : 2*x = -1 := by
  grobner
