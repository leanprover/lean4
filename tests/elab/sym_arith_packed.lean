/-!
Certificates with packed monomials (`Grind.CommRing.PPoly`) in `Sym.simp`'s arithmetic
normalizer: identities (`=`, `≤`, `<`) and normal forms of commutative rings and of commutative
semirings with `AddRightCancel`, including sums that need the balanced additions of
`Expr.toPPB_k`. Each proof is checked by the kernel.
-/

set_option sym.arith.maxTerms 1000
set_option sym.arith.maxDegree 1000

register_sym_simp arithSimp where
  pre  := arith >> control >> arrow_telescope
  post := ground

example (a b c : Int) : (a + b + c)^4 = (a + b + c)^2 * (a + b + c)^2 := by sym => simp arithSimp
example (a b c : Int) : (a - b + 2 * c)^3 ≤ (a - b + 2 * c) * (a - b + 2 * c)^2 := by sym => simp arithSimp
example (a b c : Int) : ¬ (a - b + 2 * c)^3 < (a - b + 2 * c) * (a - b + 2 * c)^2 := by sym => simp arithSimp
example (a b c : Nat) : (a + b + c)^4 = (a + b + c)^2 * (a + b + c)^2 := by sym => simp arithSimp
example (a b c : Nat) : (a + 2 * b + c)^3 ≤ (a + 2 * b + c) * (a + 2 * b + c)^2 := by sym => simp arithSimp
example (a b c : Nat) : ¬ (a + 2 * b + c)^3 < (a + 2 * b + c) * (a + 2 * b + c)^2 := by sym => simp arithSimp
example [Lean.Grind.CommRing α] (a b c d : α) : (a + b + c + d)^3 = (a + b + c + d) * (a + b + c + d)^2 := by
  sym => simp arithSimp
example [Lean.Grind.CommSemiring α] [Lean.Grind.AddRightCancel α] (a b c d : α) :
    (a + b + c + d)^3 = (a + b + c + d) * (a + b + c + d)^2 := by
  sym => simp arithSimp

-- Normal forms: the rewritten term is checked against the input.
example (f : Int → Int) (a b c : Int) :
    f ((a + b + c)^3) = f (a^3 + 3*a^2*b + 3*a^2*c + 3*a*b^2 + 6*a*b*c + 3*a*c^2 + b^3 + 3*b^2*c + 3*b*c^2 + c^3) := by
  sym => simp arithSimp
example (f : Nat → Nat) (a b c : Nat) :
    f ((a + b + c)^3) = f (a^3 + 3*a^2*b + 3*a^2*c + 3*a*b^2 + 6*a*b*c + 3*a*c^2 + b^3 + 3*b^2*c + 3*b*c^2 + c^3) := by
  sym => simp arithSimp

-- Sums in increasing order use the balanced additions.
example (x₀ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ : Int) :
    x₀ * x₀ + x₁ * x₁ + x₂ * x₂ + x₃ * x₃ + x₄ * x₄ + x₅ * x₅ + x₆ * x₆ + x₇ * x₇ + x₈ * x₈ + x₉ * x₉ + x₁₀ * x₁₀ + x₁₁ * x₁₁ =
    x₁₁ * x₁₁ + x₁₀ * x₁₀ + x₉ * x₉ + x₈ * x₈ + x₇ * x₇ + x₆ * x₆ + x₅ * x₅ + x₄ * x₄ + x₃ * x₃ + x₂ * x₂ + x₁ * x₁ + x₀ * x₀ := by
  sym => simp arithSimp
