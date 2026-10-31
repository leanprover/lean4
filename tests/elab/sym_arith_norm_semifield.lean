module

/-! Tests for semifield division, inverse traversal, and rational coefficients in `Sym.Arith`. -/

open Lean.Grind

register_sym_simp semifieldSimp where
  pre := arith >> control >> arrow_telescope
  post := ground

section
variable {F : Type} [Semifield F] [IsCharP F 0]

example (a : F) : a / 2 + a / 2 = a := by sym => simp semifieldSimp
example (a b : F) : a / 2 + b / 3 = (3*a + 2*b) / 6 := by sym => simp semifieldSimp
example (a : F) : a / 6 + a / 3 + a / 2 = a := by sym => simp semifieldSimp
example (a : F) : (a / 2)^2 = a^2 / 4 := by sym => simp semifieldSimp
example (a b : F) : (a/2 + b/3)^2 = a^2/4 + a*b/3 + b^2/9 := by
  sym => simp semifieldSimp
example (a : F) : a / 100 + 99*a / 100 = a := by sym => simp semifieldSimp
example : (1 : F) / 2 + 1 / 3 = 5 / 6 := by sym => simp semifieldSimp
example (a : F) : a / 0 + a / 2 + a / 2 = a := by sym => simp semifieldSimp
example (a b : F) : a/(b*2) + a/(b*2) = a/b := by sym => simp semifieldSimp
example (a b : F) : (a+b)⁻¹ = (b+a)⁻¹ := by sym => simp semifieldSimp
example : (1/2 + 1/3 : F)⁻¹ = 6/5 := by sym => simp semifieldSimp
example (f : F → F) (a b : F) : f (a/2 + b/3) = f ((3*a + 2*b)/6) := by
  sym => simp semifieldSimp
example (a b : F) : a/2 + b + b = a/2 + 2*b := by sym => simp semifieldSimp

-- A second normalization pass should leave the normal form unchanged.
/-- error: `Sym.simp` made no progress -/
#guard_msgs in
example (f : F → F) (a b c : F) : f (a/2 + b/3) = c := by
  sym =>
    simp semifieldSimp
    simp semifieldSimp

example (_a : F) : True := by
  fail_if_success have : _a / 2 = _a := by sym => simp semifieldSimp
  fail_if_success have : _a / 0 = _a := by sym => simp semifieldSimp
  fail_if_success have : _a*_a⁻¹ = 1 := by sym => simp semifieldSimp
  fail_if_success have : (_a+1)⁻¹ = _a⁻¹+1 := by sym => simp semifieldSimp
  trivial

end

section
variable {F : Type} [Semifield F]

example (a : F) : a / 0 = 0 := by sym => simp semifieldSimp
example (a : F) : a / 1 = a := by sym => simp semifieldSimp
example (a : F) : a / (0*a) = 0 := by sym => simp semifieldSimp
example (a b : F) : (a*b)⁻¹ = a⁻¹*b⁻¹ := by sym => simp semifieldSimp
example (a : F) : (a^3)⁻¹ = a⁻¹^3 := by sym => simp semifieldSimp
example (a : F) : a⁻¹⁻¹ = a := by sym => simp semifieldSimp
example (a b : F) : a / b + a / b = 2*a / b := by sym => simp semifieldSimp
example (a b : F) : (a*b)⁻¹ + a⁻¹*b⁻¹ = 2*a⁻¹*b⁻¹ := by sym => simp semifieldSimp
example (a : F) : a/2 + a/2 = 2*(a*2⁻¹) := by sym => simp semifieldSimp

end

section
variable {F : Type} [Semifield F] [IsCharP F 0] [AddRightCancel F]

-- Combine rational coefficients before cancelling common terms.
example (a b c : F) (h : b = c) : a/2 + a/2 + b = a + c := by
  sym => simp semifieldSimp; tactic => exact h
example (a b c : F) (h : b = c) : a/2 + b = a/2 + c := by
  sym => simp semifieldSimp; tactic => exact h
example (a b c : F) (h : b = c) : a/2 + a/3 + b = 5*a/6 + c := by
  sym => simp semifieldSimp; tactic => exact h

/-- error: `Sym.simp` made no progress -/
#guard_msgs in
example (a b c : F) : a/2 + a/2 + b = a + c := by
  sym =>
    simp semifieldSimp
    simp semifieldSimp

end

section
variable {F : Type} [Semifield F] [IsCharP F 0]
  [LE F] [LT F] [Std.IsPreorder F] [Std.LawfulOrderLT F] [OrderedRing F]

example (a b c : F) (h : b ≤ c) : a/2 + a/2 + b ≤ a + c := by
  sym => simp semifieldSimp; tactic => exact h
example (a b c : F) (h : b < c) : a/2 + a/2 + b < a + c := by
  sym => simp semifieldSimp; tactic => exact h

end
