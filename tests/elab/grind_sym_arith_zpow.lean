/-!
Tests for `zpow` with a literal exponent in the `Sym.simp`-based `grind` normalizer: in a field,
`a ^ (k : Int)` is `a ^ k` for `k ≥ 0` and `(a ^ (-k))⁻¹` for `k < 0`, so it takes part in the
polynomial normal form (issue 15 of the `Sym` normalizer migration).
-/

open Lean.Grind

set_option warn.sorry false

section
variable {α : Type} [Field α] [IsCharP α 0]

/--
trace: α : Type
inst✝¹ : Field α
inst✝ : IsCharP α 0
a : α
f : α → Nat
⊢ f (2 * a ^ 2) = 0
-/
#guard_msgs in
example (a : α) (f : α → Nat) : f (a ^ (2 : Int) + a * a) = 0 := by grind_norm sym; trace_state; sorry

/--
trace: α : Type
inst✝¹ : Field α
inst✝ : IsCharP α 0
a : α
f : α → Nat
⊢ f a⁻¹ = 0
-/
#guard_msgs in
example (a : α) (f : α → Nat) : f (a ^ (-1 : Int)) = 0 := by grind_norm sym; trace_state; sorry

/--
trace: α : Type
inst✝¹ : Field α
inst✝ : IsCharP α 0
a : α
f : α → Nat
⊢ f (a ^ 2)⁻¹ = 0
-/
#guard_msgs in
example (a : α) (f : α → Nat) : f (a ^ (-2 : Int)) = 0 := by grind_norm sym; trace_state; sorry

/--
trace: α : Type
inst✝¹ : Field α
inst✝ : IsCharP α 0
a : α
f : α → Nat
⊢ f (a + 1) = 0
-/
#guard_msgs in
example (a : α) (f : α → Nat) : f (a ^ (0 : Int) + a ^ (1 : Int)) = 0 := by
  grind_norm sym; trace_state; sorry

-- Numeral bases evaluate.
/--
trace: α : Type
inst✝¹ : Field α
inst✝ : IsCharP α 0
a : α
f : α → Nat
⊢ f (33 * 4⁻¹) = 0
-/
#guard_msgs in
example (a : α) (f : α → Nat) : f ((2 : α) ^ (3 : Int) + (2 : α) ^ (-2 : Int)) = 0 := by
  grind_norm sym; trace_state; sorry

/--
trace: α : Type
inst✝¹ : Field α
inst✝ : IsCharP α 0
a b : α
f : α → Nat
⊢ f (3 * a) = 0
-/
#guard_msgs in
example (a b : α) (f : α → Nat) : f (a / (1 / (2 + 2⁻¹ + 2 ^ (-1 : Int)))) = 0 := by
  grind_norm sym; trace_state; sorry

-- A variable exponent is an atom.
/--
trace: α : Type
inst✝¹ : Field α
inst✝ : IsCharP α 0
a : α
n : Int
f : α → Nat
⊢ f (a ^ n) = 0
-/
#guard_msgs in
example (a : α) (n : Int) (f : α → Nat) : f (a ^ n) = 0 := by grind_norm sym; trace_state; sorry

end

-- Without a characteristic.
/--
trace: α : Type
inst✝ : Field α
a : α
f : α → Nat
⊢ f a⁻¹ = 0
-/
#guard_msgs in
example {α : Type} [Field α] (a : α) (f : α → Nat) : f (a ^ (-1 : Int)) = 0 := by
  grind_norm sym; trace_state; sorry

set_option backward.grind.normalizer false

example {α : Type} [Field α] (a : α) : a ^ (-1 : Int) = a⁻¹ := by grind

example {α : Type} [Field α] (a : α) (h : a ≠ 0) : a ^ (-1 : Int) * a = 1 := by grind

example {α : Type} [Field α] (a b : α) (h : a ^ (2 : Int) = b) : a * a = b := by grind

example (a : Rat) (h : a ≠ 0) : a ^ (-2 : Int) * a ^ 2 = 1 := by grind

example {α : Type} [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsLinearOrder α] [Field α] [IsCharP α 0]
    [OrderedRing α] (a : α) : a / (1 / (2 + 3*2 + (-3) - 2^3 + 6 + 2⁻¹ + 2^(-1) + (-1))) ≥ 3 * a := by
  grind
