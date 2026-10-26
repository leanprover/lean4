/-!
Certificates by Kronecker substitution (`Grind.CommRing.Expr.eq_of_kron`) in `Sym.simp`'s
arithmetic normalizer: identities and normal forms over few variables are checked by evaluating
both sides at one point. Covers `=`, `≤`, `<`, commutative rings and semirings, large
coefficients, high powers, negative coefficients, and a nonzero characteristic. Each proof is
checked by the kernel.
-/

set_option sym.arith.maxTerms 1000
set_option sym.arith.maxDegree 1000

register_sym_simp arithSimp where
  pre  := arith >> control >> arrow_telescope
  post := ground

example (a b c : Int) : (a - b + c)^5 = (a - b + c)^2 * (c - b + a)^3 := by sym => simp arithSimp
example (a b : Int) : (a + b)^40 = (a + b)^20 * (b + a)^20 := by sym => simp arithSimp
example (a b c : Int) : (1000 * a - 999 * b + c)^6 = ((1000 * a - 999 * b + c)^2)^3 := by sym => simp arithSimp
example (a b c : Int) : (a + b + c)^3 ≤ (a + b + c) * (a + b + c)^2 := by sym => simp arithSimp
example (a b c : Int) : ¬ (a + b + c)^3 < (a + b + c) * (a + b + c)^2 := by sym => simp arithSimp
example (a b c : Nat) : (a + 2 * b + c)^5 = (a + 2 * b + c)^2 * (a + 2 * b + c)^3 := by sym => simp arithSimp
example (a b : Nat) : (a + b)^30 ≤ (a + b)^10 * (a + b)^20 := by sym => simp arithSimp
example [Lean.Grind.CommRing α] (a b c : α) : (a + b + c)^4 = (a + b + c)^2 * (a + b + c)^2 := by sym => simp arithSimp
example [Lean.Grind.CommSemiring α] [Lean.Grind.AddRightCancel α] (a b c : α) :
    (a + b + c)^4 = (a + b + c)^2 * (a + b + c)^2 := by
  sym => simp arithSimp
example (x y : UInt64) : (x + 3 * y)^9 = (x + 3 * y)^4 * (x + 3 * y)^5 := by sym => simp arithSimp

-- Normal forms: the rewritten term is checked against the input.
example (f : Int → Int) (a b : Int) : f ((a - b)^4) = f (a^4 - 4*a^3*b + 6*a^2*b^2 - 4*a*b^3 + b^4) := by
  sym => simp arithSimp
example (f : Nat → Nat) (a b : Nat) : f ((a + b)^4) = f (a^4 + 4*a^3*b + 6*a^2*b^2 + 4*a*b^3 + b^4) := by
  sym => simp arithSimp
