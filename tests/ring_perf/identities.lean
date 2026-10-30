/-!
Benchmarks for the kernel checking of the `grind` ring solver's certificates: polynomial
identities whose sides normalize to the same polynomial, exercising polynomial products and
powers in `Lean.Grind.CommRing.Expr.toPoly_k`.
-/

open Lean.Grind

-- Brahmagupta–Fibonacci
example [CommRing α] (a b c d : α) :
    (a^2 + b^2) * (c^2 + d^2) = (a*c - b*d)^2 + (a*d + b*c)^2 := by grind

-- Euler's four-square identity
example [CommRing α] (a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ : α) :
    (a₁^2 + a₂^2 + a₃^2 + a₄^2) * (b₁^2 + b₂^2 + b₃^2 + b₄^2) =
      (a₁*b₁ - a₂*b₂ - a₃*b₃ - a₄*b₄)^2 + (a₁*b₂ + a₂*b₁ + a₃*b₄ - a₄*b₃)^2 +
      (a₁*b₃ - a₂*b₄ + a₃*b₁ + a₄*b₂)^2 + (a₁*b₄ + a₂*b₃ - a₃*b₂ + a₄*b₁)^2 := by grind

-- Lagrange's identity
example [CommRing α] (a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ : α) :
    (a₁^2 + a₂^2 + a₃^2 + a₄^2) * (b₁^2 + b₂^2 + b₃^2 + b₄^2) - (a₁*b₁ + a₂*b₂ + a₃*b₃ + a₄*b₄)^2 =
      (a₁*b₂ - a₂*b₁)^2 + (a₁*b₃ - a₃*b₁)^2 + (a₁*b₄ - a₄*b₁)^2 +
      (a₂*b₃ - a₃*b₂)^2 + (a₂*b₄ - a₄*b₂)^2 + (a₃*b₄ - a₄*b₃)^2 := by grind

-- Binet–Cauchy: `(a·c)(b·d) - (a·d)(b·c) = (a×b)·(c×d)`
example [CommRing α] (a₁ a₂ a₃ b₁ b₂ b₃ c₁ c₂ c₃ d₁ d₂ d₃ : α) :
    (a₁*c₁ + a₂*c₂ + a₃*c₃) * (b₁*d₁ + b₂*d₂ + b₃*d₃) - (a₁*d₁ + a₂*d₂ + a₃*d₃) * (b₁*c₁ + b₂*c₂ + b₃*c₃) =
      (a₂*b₃ - a₃*b₂) * (c₂*d₃ - c₃*d₂) + (a₃*b₁ - a₁*b₃) * (c₃*d₁ - c₁*d₃) +
      (a₁*b₂ - a₂*b₁) * (c₁*d₂ - c₂*d₁) := by grind

example (x y : Int) :
    x^10 - y^10 = (x - y) * (x^9 + x^8*y + x^7*y^2 + x^6*y^3 + x^5*y^4 + x^4*y^5 + x^3*y^6 + x^2*y^7 + x*y^8 + y^9) := by
  grind

example [CommRing α] (a b c : α) :
    a^3 + b^3 + c^3 - 3*a*b*c = (a + b + c) * (a^2 + b^2 + c^2 - a*b - b*c - c*a) := by grind

example (a b : Int) :
    (a + b)^8 = a^8 + 8*a^7*b + 28*a^6*b^2 + 56*a^5*b^3 + 70*a^4*b^4 + 56*a^3*b^5 + 28*a^2*b^6 + 8*a*b^7 + b^8 := by
  grind

example [CommRing α] (a b c : α) :
    (a + b + c)^4 = a^4 + b^4 + c^4 + 4*(a^3*b + a^3*c + b^3*a + b^3*c + c^3*a + c^3*b)
      + 6*(a^2*b^2 + a^2*c^2 + b^2*c^2) + 12*(a^2*b*c + a*b^2*c + a*b*c^2) := by grind

example (a b c d : Int) :
    (a + b + c + d)^4 =
      24*a*b*c*d + 12*a*b*c^2 + 12*a*b*d^2 + 12*a*b^2*c + 12*a*b^2*d + 4*a*b^3 + 12*a*c*d^2 + 12*a*c^2*d + 4*a*c^3 + 4*a*d^3 + 12*a^2*b*c + 12*a^2*b*d + 6*a^2*b^2 + 12*a^2*c*d + 6*a^2*c^2 + 6*a^2*d^2 + 4*a^3*b + 4*a^3*c + 4*a^3*d + a^4 + 12*b*c*d^2 + 12*b*c^2*d + 4*b*c^3 + 4*b*d^3 + 12*b^2*c*d + 6*b^2*c^2 + 6*b^2*d^2 + 4*b^3*c + 4*b^3*d + b^4 + 4*c*d^3 + 6*c^2*d^2 + 4*c^3*d + c^4 + d^4 := by
  grind

-- Vandermonde determinant
example (a b c d : Int) :
    (b - a)*(c - a)*(d - a)*(c - b)*(d - b)*(d - c) =
      b*c^2*d^3 - b*c^3*d^2 - b^2*c*d^3 + b^2*c^3*d + b^3*c*d^2 - b^3*c^2*d - a*c^2*d^3 + a*c^3*d^2 + a*b^2*d^3 - a*b^2*c^3 - a*b^3*d^2 + a*b^3*c^2 + a^2*c*d^3 - a^2*c^3*d - a^2*b*d^3 + a^2*b*c^3 + a^2*b^3*d - a^2*b^3*c - a^3*c*d^2 + a^3*c^2*d + a^3*b*d^2 - a^3*b*c^2 - a^3*b^2*d + a^3*b^2*c := by
  grind
