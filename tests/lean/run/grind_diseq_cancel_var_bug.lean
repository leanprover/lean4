-- Test for fix: grind diseq_cancel_var was using wrong variable index after renaming
-- Previously this would produce a kernel type mismatch error
-- The unused variable `hr` is intentional - it triggers the variable renaming that exposed the bug
set_option linter.unusedVariables false in
example (r : Rat) (hr : r ≤ r) : 2⁻¹ * 2 = (1 : Rat) := by grind

-- Leo's test cases for diseq_cancel_var (from Zulip)
-- These should still work after the fix
open Std Lean.Grind

variable {α : Type} [Field α] [LE α] [LT α] [LawfulOrderLT α] [IsLinearOrder α] [OrderedRing α] [NoNatZeroDivisors α]
example (a b : α) (h : a = b / 2) : a + a ≤ b := by grind
example (a : α) (h : a ≠ 1/2) : 2*a > 1 ∨ 2*a < 1 := by grind
example (a : α) (h : a ≠ (1/2)^3) : 8*a > 1 ∨ 8*a < 1 := by grind
example (a : α) (h : a ≠ (1/2)^3) : 8*a > 1 ∨ 8*a < 1 := by grind
example (a : α) (h : a ≠ (1/3)*(1/2)^3) : 24*a > 1 ∨ 24*a < 1 := by grind
example (a : α) (h : a ≠ b*(2⁻¹)^3) : 8*a > b ∨ 8*a < b := by grind
example (a : α) (h : a ≠ (2⁻¹)^3*b) : 8*a > b ∨ 8*a < b := by grind
example (a : α) (h : 5*(2⁻¹)^3*b ≠ a) : 8*a > 5*b ∨ 8*a < 5*b := by grind
example (a : α) (h : 5*(2⁻¹)*(2⁻¹)^3*b + (3/2)*c ≠ a) : 16*a > 5*b + 24*c ∨ 16*a < 5*b + 24*c := by grind
example (x : α) : x ≥ 1/3 → x ≥ 0 := by grind
example (a : α) (h : a ≠ 1/2 + 1/3) : 6*a > 5 ∨ 6*a < 5 := by grind
example (a : α) (h : 1/2 + 1/3 ≠ a) : 6*a > 5 ∨ 6*a < 5 := by grind
example (h : (1/4:α) ≠ (1/2)*(1/2)) : False := by grind
example (h : (1/4:α) + 1/4 ≠ (1/2)) : False := by grind
example (h : (1/2:α) + 1/3 ≠ (5/6)) : False := by grind
