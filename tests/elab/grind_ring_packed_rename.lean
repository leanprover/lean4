/-!
`grind`'s ring certificates for chains of simplification steps (`Stepwise.simpsK`,
`Stepwise.d_stepsK`, `Stepwise.d_stepsP`) when the proof does not use every variable of the ring:
the variables of the polynomials are renamed before the certificates are checked, and the packed
polynomials must be built after the renaming. With few variables the chains are checked by
Kronecker substitution; with many variables (here, the unused ones count), by packed sums.
-/

-- Kronecker substitution, with the unused variables `x` and `y`.
example [Lean.Grind.CommRing α] [Lean.Grind.NoNatZeroDivisors α] (x y a b c d : α) :
    x * y = 7 → a + b + c + d = 1 → a^2 + b^2 + c^2 + d^2 = -3 → a^3 + b^3 + c^3 + d^3 = 4 →
    a^4 + b^4 + c^4 + d^4 = -3 → a^5 + b^5 + c^5 + d^5 = -24 := by grind

example [Lean.Grind.CommRing α] [Lean.Grind.IsCharP α 11] [Lean.Grind.NoNatZeroDivisors α] (x y a b c d : α) :
    x * y = 7 → a + b + c + d = 1 → a^2 + b^2 + c^2 + d^2 = -3 → a^3 + b^3 + c^3 + d^3 = 4 →
    a^4 + b^4 + c^4 + d^4 = -3 → a^5 + b^5 + c^5 + d^5 = -24 := by grind

-- Packed sums: the unused variables make the values at the point too large.
example [Lean.Grind.CommRing α] [Lean.Grind.NoNatZeroDivisors α] (x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ a b c d : α) :
    x₁ * x₂ = 7 → x₃ * x₄ = 7 → x₅ * x₆ = 7 → x₇ * x₈ = 7 →
    a + b + c + d = 1 → a^2 + b^2 + c^2 + d^2 = -3 → a^3 + b^3 + c^3 + d^3 = 4 →
    a^4 + b^4 + c^4 + d^4 = -3 → a^5 + b^5 + c^5 + d^5 = -24 := by grind
