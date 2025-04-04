/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Data.Nat.Linear

namespace Nat

theorem nextPowerOfTwo_dec {n power : Nat} (h₁ : power > 0) (h₂ : power < n) : n - power * 2 < n - power := by
  have : power * 2 = power + power := by simp +arith
  rw [this, Nat.sub_add_eq]
  exact Nat.sub_lt (Nat.zero_lt_sub_of_lt h₂) h₁

/--
Returns the least power of two that's greater than or equal to `n`.

Examples:
 * `Nat.nextPowerOfTwo 0 = 1`
 * `Nat.nextPowerOfTwo 1 = 1`
 * `Nat.nextPowerOfTwo 2 = 2`
 * `Nat.nextPowerOfTwo 3 = 4`
 * `Nat.nextPowerOfTwo 5 = 8`
-/
def nextPowerOfTwo (n : Nat) : Nat :=
  go 1 (by decide)
where
  go (power : Nat) (h : power > 0) : Nat :=
    if power < n then
      go (power * 2) (Nat.mul_pos h (by decide))
    else
      power
  termination_by n - power
  decreasing_by simp_wf; apply nextPowerOfTwo_dec <;> assumption

/--
A natural number `n` is a power of two if there exists some `k : Nat` such that `n = 2 ^ k`.
-/
def isPowerOfTwo (n : Nat) := ∃ k, n = 2 ^ k

theorem isPowerOfTwo_one : isPowerOfTwo 1 :=
  ⟨0, by decide⟩

@[deprecated isPowerOfTwo_one (since := "2025-03-18")]
abbrev one_isPowerOfTwo := isPowerOfTwo_one

theorem isPowerOfTwo_mul_two_of_isPowerOfTwo (h : isPowerOfTwo n) : isPowerOfTwo (n * 2) :=
  have ⟨k, h⟩ := h
  ⟨k+1, by simp [h, Nat.pow_succ]⟩

@[deprecated isPowerOfTwo_mul_two_of_isPowerOfTwo (since := "2025-04-04")]
abbrev mul2_isPowerOfTwo_of_isPowerOfTwo := @isPowerOfTwo_mul_two_of_isPowerOfTwo

theorem pos_of_isPowerOfTwo (h : isPowerOfTwo n) : n > 0 := by
  have ⟨k, h⟩ := h
  rw [h]
  apply Nat.pow_pos
  decide

theorem isPowerOfTwo_nextPowerOfTwo (n : Nat) : n.nextPowerOfTwo.isPowerOfTwo := by
  apply isPowerOfTwo_go
  apply isPowerOfTwo_one
where
  isPowerOfTwo_go (power : Nat) (h₁ : power > 0) (h₂ : power.isPowerOfTwo) : (nextPowerOfTwo.go n power h₁).isPowerOfTwo := by
    unfold nextPowerOfTwo.go
    split
    . exact isPowerOfTwo_go (power*2) (Nat.mul_pos h₁ (by decide)) (Nat.isPowerOfTwo_mul_two_of_isPowerOfTwo h₂)
    . assumption
  termination_by n - power
  decreasing_by simp_wf; apply nextPowerOfTwo_dec <;> assumption

end Nat
