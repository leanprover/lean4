/-!
Benchmarks for the kernel checking of the certificates that the `Sym.simp`-based `grind`
normalizer (`backward.grind.normalizer false`) produces with `Lean.Grind.CommRing`'s
`eq_norm_expr`, `le_norm_expr`, `lt_norm_expr`, `Expr.eq_of_toPoly_eq` and the `Int`
certificates of `Init.Grind.Ring.IntSolver`.
-/

set_option backward.grind.normalizer false
set_option linter.unusedVariables false

open Lean.Grind

example [CommRing α] (a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ : α) :
    (a₁^2 + a₂^2 + a₃^2 + a₄^2) * (b₁^2 + b₂^2 + b₃^2 + b₄^2) =
      (a₁*b₁ - a₂*b₂ - a₃*b₃ - a₄*b₄)^2 + (a₁*b₂ + a₂*b₁ + a₃*b₄ - a₄*b₃)^2 +
      (a₁*b₃ - a₂*b₄ + a₃*b₁ + a₄*b₂)^2 + (a₁*b₄ + a₂*b₃ - a₃*b₂ + a₄*b₁)^2 := by grind

example (a b c d : Int) :
    (b - a)*(c - a)*(d - a)*(c - b)*(d - b)*(d - c) =
      b*c^2*d^3 - b*c^3*d^2 - b^2*c*d^3 + b^2*c^3*d + b^3*c*d^2 - b^3*c^2*d - a*c^2*d^3 + a*c^3*d^2 + a*b^2*d^3 - a*b^2*c^3 - a*b^3*d^2 + a*b^3*c^2 + a^2*c*d^3 - a^2*c^3*d - a^2*b*d^3 + a^2*b*c^3 + a^2*b^3*d - a^2*b^3*c - a^3*c*d^2 + a^3*c^2*d + a^3*b*d^2 - a^3*b*c^2 - a^3*b^2*d + a^3*b^2*c := by
  grind

example (a b c : Int) :
    a + b + c = 3 → a^2 + b^2 + c^2 = 5 → a^3 + b^3 + c^3 = 7 → a^4 + b^4 + c^4 = 9 := by grind

example {α} [CommRing α] [IsCharP α 0] (d t c : α) (d_inv PSO3_inv : α)
    (Δ40 : d^2 * (d + t - d * t - 2) * (d + t + d * t) = 0)
    (Δ41 : -d^4 * (d + t - d * t - 2) *
      (2 * d + 2 * d * t - 4 * d * t^2 + 2 * d * t^4 + 2 * d^2 * t^4 - c * (d + t + d * t)) = 0)
    (_ : d * d_inv = 1)
    (_ : (d + t - d * t - 2) * PSO3_inv = 1) :
    t^2 = t + 1 := by grind

example (x y z w : Int) (h₁ : 2*x + 3*y - 4*z + w ≤ 10) (h₂ : -x + 2*y + 3*z - 2*w < 7)
    (h₃ : 3*x - y + z + 4*w ≥ -5) (h₄ : x + y + z + w = 6) (h₅ : 6*x - 4*y + 2*z ≤ 8 + 2*w)
    (h₆ : 0 ≤ x) (h₇ : 0 ≤ y) (h₈ : 0 ≤ z) (h₉ : 0 ≤ w) : x + 2*y + 3*z + 4*w ≤ 24 := by
  lia

example (x y z : Int) (h₁ : 6*x + 10*y + 15*z = 7) (h₂ : 2 ∣ x + y + z + 1) (h₃ : 0 ≤ x) (h₄ : x ≤ 10)
    (h₅ : 0 ≤ y) (h₆ : y ≤ 10) (h₇ : 0 ≤ z) (h₈ : z ≤ 10) : False := by
  lia

example (f : Int → Int) (x y : Int) (h₁ : f (2*x + 3*y) ≤ f (3*y + x + x) + 4*x - 4*x)
    (h₂ : f (x + x + y + 2*y) + 1 ≤ 0) : f (2*x + 3*y) < 0 := by
  grind

example (x y : Int) (h₁ : x * (y + 1) ≤ x * y + 5) (h₂ : (x + 1) * (x - 1) = x^2 - 1) : x ≤ 5 := by
  grind
