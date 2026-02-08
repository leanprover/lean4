universe u

@[match_pattern] def bit0 {α : Type u} [Add α] (a : α) : α := a + a

@[match_pattern] def bit1 {α : Type u} [One α] [Add α] (a : α) : α := bit0 a + 1

class AddZeroClass (M : Type u) extends Zero M, Add M where
  zero_add : ∀ a : M, 0 + a = a
  add_zero : ∀ a : M, a + 0 = a

open AddZeroClass

theorem bit0_zero {M} [AddZeroClass M] : bit0 (0 : M) = 0 :=
  add_zero _

def bit (b : Bool) : Nat → Nat :=
  cond b bit1 bit0

-- This is `Nat.bit_mod_two` from `Mathlib.Data.Nat.Bitwise`.
-- Here it works fine:
example (a : Bool) (x : Nat) :
    bit a x % 2 = if a then 1 else 0 := by
  simp (config := { unfoldPartialApp := true }) only [bit, bit1, bit0, ← Nat.mul_two, Bool.cond_eq_ite]
  split <;> simp [Nat.add_mod]

-- Now prove one more theorem
theorem bit1_zero {M} [AddZeroClass M] [One M] : bit1 (0 : M) = 1 := by rw [bit1, bit0_zero, zero_add]

-- Now try again:
example (a : Bool) (x : Nat) :
    bit a x % 2 = if a then 1 else 0 := by
  simp (config := { unfoldPartialApp := true }) only [bit, bit1, bit0, ← Nat.mul_two, Bool.cond_eq_ite]
  split <;> simp [Nat.add_mod] -- fails
