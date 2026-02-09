/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Deniz Aydin, Floris van Doorn, Mario Carneiro
-/
module

prelude
public import Init.Data.Int.Basic
import Init.ByCases
import Init.Data.Nat.Lemmas
import Init.Omega
import Init.RCases

public section

namespace Int

/-! # pow -/

@[simp, norm_cast]
theorem natCast_pow (m n : Nat) : (m ^ n : Nat) = (m : Int) ^ n := rfl

theorem negSucc_pow (m n : Nat) : (-[m+1] : Int) ^ n = if n % 2 = 0 then Int.ofNat (m.succ ^ n) else Int.negOfNat (m.succ ^ n) := rfl

@[simp] protected theorem pow_zero (m : Int) : m ^ 0 = 1 := by cases m <;> simp [← natCast_pow, negSucc_pow]

protected theorem pow_succ (m : Int) (n : Nat) : m ^ n.succ = m ^ n * m := by
  rcases m with _ | a
  · rfl
  · simp only [negSucc_pow, Nat.succ_mod_succ_eq_zero_iff, Nat.reduceAdd, ← Nat.mod_two_ne_zero,
      Nat.pow_succ, ofNat_eq_natCast, @negOfNat_eq (_ * _), ite_not, apply_ite (· * -[a+1]),
      ofNat_mul_negSucc, negOfNat_mul_negSucc]

protected theorem pow_succ' (b : Int) (e : Nat) : b ^ (e+1) = b * (b ^ e) := by
  rw [Int.mul_comm, Int.pow_succ]

protected theorem pow_add (a : Int) (m n : Nat) : a ^ (m + n) = a ^ m * a ^ n := by
  induction n with
  | zero => rw [Nat.add_zero, Int.pow_zero, Int.mul_one]
  | succ _ ih => rw [Nat.add_succ, Int.pow_succ, Int.pow_succ, ih, Int.mul_assoc]

protected theorem zero_pow {n : Nat} (h : n ≠ 0) : (0 : Int) ^ n = 0 := by
  match n, h with
  | n + 1, _ => simp [Int.pow_succ]

protected theorem one_pow {n : Nat} : (1 : Int) ^ n = 1 := by
  induction n with simp_all [Int.pow_succ]

protected theorem mul_pow {a b : Int} {n : Nat} : (a * b) ^ n = a ^ n * b ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Int.pow_succ, Int.pow_succ, Int.pow_succ, ih, Int.mul_assoc, Int.mul_assoc,
      Int.mul_left_comm (b^n)]

protected theorem pow_one (a : Int) : a ^ 1 = a := by
  rw [Int.pow_succ, Int.pow_zero, Int.one_mul]

protected theorem pow_mul {a : Int} {n m : Nat} : a ^ (n * m) = (a ^ n) ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Int.pow_succ, Nat.mul_add_one, Int.pow_add, ih]

protected theorem pow_pos {n : Int} {m : Nat} : 0 < n → 0 < n ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    simp only [Int.pow_succ]
    exact fun h => Int.mul_pos (ih h) h

protected theorem pow_nonneg {n : Int} {m : Nat} : 0 ≤ n → 0 ≤ n ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    simp only [Int.pow_succ]
    exact fun h => Int.mul_nonneg (ih h) h

protected theorem pow_ne_zero {n : Int} {m : Nat} : n ≠ 0 → n ^ m ≠ 0 := by
  induction m with
  | zero => simp
  | succ m ih =>
    simp only [Int.pow_succ]
    exact fun h => Int.mul_ne_zero (ih h) h

instance {n : Int} {m : Nat} [NeZero n] : NeZero (n ^ m) := ⟨Int.pow_ne_zero (NeZero.ne _)⟩

instance {n : Int} : NeZero (n^0) := ⟨by simp⟩

@[simp]
protected theorem two_pow_pred_sub_two_pow {w : Nat} (h : 0 < w) :
    ((2 ^ (w - 1) : Nat) - (2 ^ w : Nat) : Int) = - ((2 ^ (w - 1) : Nat) : Int) := by
  rw [← Nat.two_pow_pred_add_two_pow_pred h]
  omega

@[simp]
protected theorem two_pow_pred_sub_two_pow' {w : Nat} (h : 0 < w) :
    (2 : Int) ^ (w - 1) - (2 : Int) ^ w = - (2 : Int) ^ (w - 1) := by
  norm_cast
  rw [← Nat.two_pow_pred_add_two_pow_pred h]
  simp [h, -Int.natCast_pow]

theorem pow_lt_pow_of_lt {a : Int} {b c : Nat} (ha : 1 < a) (hbc : b < c):
    a ^ b < a ^ c := by
  rw [← Int.toNat_of_nonneg (a := a) (by omega), ← Int.natCast_pow, ← Int.natCast_pow]
  have := Nat.pow_lt_pow_of_lt (a := a.toNat) (m := c) (n := b)
  simp only [Int.ofNat_lt]
  omega

@[simp] theorem natAbs_pow (n : Int) : (k : Nat) → (n ^ k).natAbs = n.natAbs ^ k
  | 0 => by simp
  | k + 1 => by rw [Int.pow_succ, natAbs_mul, natAbs_pow, Nat.pow_succ]

theorem toNat_pow_of_nonneg {x : Int} (h : 0 ≤ x) (k : Nat) : (x ^ k).toNat = x.toNat ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Int.pow_succ, Int.toNat_mul (Int.pow_nonneg h) h, ih, Nat.pow_succ]

protected theorem sq_nonnneg (m : Int) : 0 ≤ m ^ 2 := by
  rw [Int.pow_succ, Int.pow_one]
  cases m
  · apply Int.mul_nonneg <;> simp
  · apply Int.mul_nonneg_of_nonpos_of_nonpos <;> exact negSucc_le_zero _

protected theorem pow_nonneg_of_even {m : Int} {n : Nat} (h : n % 2 = 0) : 0 ≤ m ^ n := by
  rw [← Nat.mod_add_div n 2, h, Nat.zero_add, Int.pow_mul]
  apply Int.pow_nonneg
  exact Int.sq_nonnneg m

protected theorem neg_pow {m : Int} {n : Nat} : (-m)^n = (-1)^(n % 2) * m^n := by
  rw [Int.neg_eq_neg_one_mul, Int.mul_pow]
  rw (occs := [1]) [← Nat.mod_add_div n 2]
  rw [Int.pow_add, Int.pow_mul]
  simp [Int.one_pow]

end Int
