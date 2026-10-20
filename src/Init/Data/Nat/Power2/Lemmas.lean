/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julia M. Himmel, Adomas Baliuka
-/
module

prelude
public import Init.Data.Nat.Power2.Basic
import all Init.Data.Nat.Power2.Basic
import Init.ByCases
import Init.Data.Nat.Lemmas
import Init.Omega
import Init.RCases

public section

namespace Nat

@[simp]
theorem not_isPowerOfTwo_zero : ¬isPowerOfTwo 0 := by
  rw [isPowerOfTwo, not_exists]
  intro x
  have := one_le_pow x 2 (by decide)
  omega

private theorem ne_zero_of_isPowerOfTwo {n : Nat} (h : n.isPowerOfTwo) : n ≠ 0 := by
  rintro rfl
  simp at h

private theorem le_of_isPowerOfTwo_of_lt_two_mul {k n m : Nat} (hn : n.isPowerOfTwo)
    (hm : m.isPowerOfTwo) (hn₂ : n < 2 * k) (hm₁ : k ≤ m) : n ≤ m := by
  obtain ⟨n, rfl⟩ := hn
  obtain ⟨m, rfl⟩ := hm
  rw [Nat.pow_le_pow_iff_right (by omega), Nat.le_iff_lt_add_one,
    ← Nat.pow_lt_pow_iff_right (by decide : 1 < 2), Nat.pow_add_one']
  exact Nat.lt_of_lt_of_le hn₂ (Nat.mul_le_mul_left _ hm₁)

theorem nextPowerOfTwo_eq_iff {n m : Nat} :
    n.nextPowerOfTwo = m ↔ n ≤ m ∧ m.isPowerOfTwo ∧ ∀ k, n ≤ k → k.isPowerOfTwo → m ≤ k := by
  rw [nextPowerOfTwo]
  suffices ∀ l h, l.isPowerOfTwo → l < 2 * n →
      (nextPowerOfTwo.go n l h = m ↔
        n ≤ m ∧ m.isPowerOfTwo ∧ ∀ k, n ≤ k → k.isPowerOfTwo → m ≤ k) by
    obtain (rfl|hn) := Nat.eq_zero_or_pos n
    · simp only [nextPowerOfTwo.go, not_lt_zero, ↓reduceIte, zero_le, forall_const, true_and]
      refine ⟨fun h => ?_, fun ⟨h₁, h₂⟩ => ?_⟩
      · simp +contextual [← h, ← Nat.not_lt, ne_zero_of_isPowerOfTwo]
      · exact Nat.le_antisymm (by simp [← Nat.not_lt, ne_zero_of_isPowerOfTwo, h₁]) (h₂ _ (by simp))
    · exact this _ _ (by simp) (by omega)
  intro l hl₁ hl₂ hln
  fun_induction nextPowerOfTwo.go with
  | case1 p hp₁ hp₂ ih =>
    apply ih
    · exact isPowerOfTwo_mul_two_of_isPowerOfTwo hl₂
    · rw [Nat.mul_comm]
      exact Nat.mul_lt_mul_of_pos_left hp₂ (by omega)
  | case2 p hp₁ hp₂ =>
    refine ⟨?_, fun ⟨h₁, h₂, h₃⟩ => ?_⟩
    · rintro rfl
      exact ⟨by omega, hl₂, fun k hk₁ hk₂ => le_of_isPowerOfTwo_of_lt_two_mul hl₂ hk₂ hln hk₁⟩
    · exact Nat.le_antisymm (le_of_isPowerOfTwo_of_lt_two_mul hl₂ h₂ hln h₁) (h₃ _ (by omega) hl₂)

@[simp]
theorem le_nextPowerOfTwo (n : Nat) : n ≤ n.nextPowerOfTwo :=
  (nextPowerOfTwo_eq_iff.1 rfl).1

theorem nextPowerOfTwo_le {n m : Nat} (hn : n ≤ m) (hm : m.isPowerOfTwo) : n.nextPowerOfTwo ≤ m :=
  (nextPowerOfTwo_eq_iff.1 rfl).2.2 _ hn hm

theorem nextPowerOfTwo_eq_self {n : Nat} (h : n.isPowerOfTwo) : n.nextPowerOfTwo = n :=
 nextPowerOfTwo_eq_iff.2 (by simp +contextual [h])

@[simp]
theorem isPowerOfTwo_nextPowerOfTwo (n : Nat) : n.nextPowerOfTwo.isPowerOfTwo :=
  (nextPowerOfTwo_eq_iff.1 rfl).2.1

end Nat
