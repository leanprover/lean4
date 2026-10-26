/-!
Kronecker substitution in `grind`'s ring certificates: the final implications `lhs = rhs`
(`Stepwise.imp_1eqK`, `Stepwise.imp_keqK`, and `Stepwise.imp_1eqKC` with a quotient polynomial in
characteristic `c`) and the chains of simplification steps (`Stepwise.simpsK`,
`Stepwise.d_stepsK`). Each proof is checked by the kernel.
-/

example [Lean.Grind.CommRing α] [Lean.Grind.NoNatZeroDivisors α] (x y : α) :
    2 * x * y = 3 → 3 * x = 5 → 10 * y = 9 := by grind
example [Lean.Grind.CommRing α] [Lean.Grind.NoNatZeroDivisors α] (x y : α) :
    2 * x + 3 * y = 1 → 3 * x - 2 * y = 4 → 13 * x = 14 := by grind
example [Lean.Grind.CommRing α] [Lean.Grind.IsCharP α 7] [Lean.Grind.NoNatZeroDivisors α] (x y : α) :
    2 * x * y = 3 → 3 * x = 5 → 10 * y = 9 := by grind
example [Lean.Grind.CommRing α] [Lean.Grind.NoNatZeroDivisors α] (a b c : α) :
    a + b + c = 3 → a^2 + b^2 + c^2 = 5 → a^3 + b^3 + c^3 = 7 → 3 * (a^5 + b^5 + c^5) = 29 := by grind
example [Lean.Grind.CommRing α] [Lean.Grind.IsCharP α 11] [Lean.Grind.NoNatZeroDivisors α] (a b c d : α) :
    a + b + c + d = 1 → a^2 + b^2 + c^2 + d^2 = -3 → a^3 + b^3 + c^3 + d^3 = 4 →
    a^4 + b^4 + c^4 + d^4 = -3 → a^5 + b^5 + c^5 + d^5 = -24 := by grind
example (a b c : Int) : (a + b + c)^3 = a^3 + b^3 + c^3 + 3*(a + b)*(b + c)*(c + a) := by grind
