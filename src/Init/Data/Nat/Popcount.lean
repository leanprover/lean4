/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

prelude
public import Init.Data.Nat.Bitwise.Lemmas
import Init.Data.Nat.Lemmas
import Init.Data.Int.Pow
import Init.ByCases
import Init.Omega
import Init.WFTactics

public section
namespace Nat

/-- The number of set bits in the binary representation of a natural number.
The runtime and kernel evaluate numeral arguments by scanning machine limbs. -/
@[expose, extern "lean_nat_popcount"]
def popcount (n : @& Nat) : Nat :=
  if h : n = 0 then 0 else popcount (n / 2) + n % 2
termination_by n
decreasing_by exact Nat.div_lt_self (Nat.zero_lt_of_ne_zero h) (by decide)

@[simp] theorem popcount_zero : popcount 0 = 0 := by rw [popcount]; rfl

theorem popcount_div_two (n : Nat) : popcount n = popcount (n / 2) + n % 2 := by
  rw [popcount]
  split
  · next h => subst n; simp
  · rfl

@[simp] theorem popcount_one : popcount 1 = 1 := by
  rw [popcount_div_two]
  simp

@[simp] theorem popcount_bool (b : Bool) : popcount b.toNat = b.toNat := by
  cases b <;> simp

@[simp] theorem popcount_two_mul_add (n : Nat) (b : Bool) :
    popcount (2 * n + b.toNat) = popcount n + b.toNat := by
  rw [popcount_div_two]
  have hb := b.toNat_lt
  rw [show (2 * n + b.toNat) / 2 = n by omega,
    show (2 * n + b.toNat) % 2 = b.toNat by omega]

theorem popcount_le (n : Nat) : popcount n ≤ n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hn : n = 0
    · subst n; simp
    · rw [popcount_div_two]
      have := ih (n / 2) (Nat.div_lt_self (by omega) (by decide))
      omega

/-- Splitting at any binary digit adds the counts of the two parts. -/
theorem popcount_mul_two_pow_add (a k b : Nat) (hb : b < 2 ^ k) :
    popcount (a * 2 ^ k + b) = popcount a + popcount b := by
  induction k generalizing b with
  | zero =>
    have : b = 0 := by simpa using hb
    subst b
    simp
  | succ k ih =>
    rw [popcount_div_two (a * 2 ^ (k + 1) + b), popcount_div_two b]
    rw [Nat.pow_succ] at hb ⊢
    rw [show a * (2 ^ k * 2) = 2 * (a * 2 ^ k) by simp only [Nat.mul_comm, Nat.mul_left_comm],
      Nat.mul_add_div (by decide), Nat.mul_add_mod]
    rw [ih (b / 2) (by omega), Nat.add_assoc]

theorem popcount_mod_add_div (n k : Nat) :
    popcount (n % 2 ^ k) + popcount (n / 2 ^ k) = popcount n := by
  have h := popcount_mul_two_pow_add (n / 2 ^ k) k (n % 2 ^ k)
    (Nat.mod_lt _ (Nat.two_pow_pos _))
  rw [Nat.mul_comm (n / 2 ^ k), Nat.div_add_mod] at h
  omega

theorem popcount_le_of_lt_two_pow {n k : Nat} (h : n < 2 ^ k) : popcount n ≤ k := by
  induction k generalizing n with
  | zero =>
    have : n = 0 := by simpa using h
    subst n
    simp
  | succ k ih =>
    rw [popcount_div_two]
    have hh := ih (n := n / 2) (by rw [Nat.pow_succ] at h; omega)
    omega

end Nat
