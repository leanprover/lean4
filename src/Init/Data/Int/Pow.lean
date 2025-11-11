/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Deniz Aydin, Floris van Doorn, Mario Carneiro
-/
module

prelude
public import Init.Data.Nat.Lemmas

public section

namespace Int

/-! # pow -/

@[simp] protected theorem pow_zero (b : Int) : b^0 = 1 := by simp [Int.pow_def]

protected theorem pow_succ (b : Int) (e : Nat) : b ^ (e+1) = (b ^ e) * b := by
  simp only [Int.pow_def]
  by_cases h : 0 ≤ b
  · simp [h, Nat.pow_add_one, ofNat_natAbs_of_nonneg]
  · simp [h]
    split <;> rename_i h
    · rw [if_neg (by omega), Nat.pow_add_one, natCast_mul, ofNat_natAbs_of_nonpos (by omega)]
      simp [Int.neg_mul, Int.mul_neg]
    · rw [if_pos (by omega), Nat.pow_add_one, natCast_mul, ofNat_natAbs_of_nonpos (by omega)]
      simp [Int.mul_neg]

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

@[simp, norm_cast]
protected theorem natCast_pow (b n : Nat) : ((b^n : Nat) : Int) = (b : Int) ^ n := by
  match n with
  | 0 => rfl
  | n + 1 =>
    simp only [Nat.pow_succ, Int.pow_succ, Int.natCast_mul, Int.natCast_pow _ n]

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

/-- The runtime behaviour of `Int.pow` is slow, so we replace it via a `@[csimp]` lemma. -/
def powImp (m : Int) (n : Nat) : Int :=
  if m ≥ 0 ∨ n % 2 = 0 then
    Int.ofNat <| m.natAbs ^ n
  else
    - (Int.ofNat <| m.natAbs ^ n)

@[csimp]
theorem pow_eq_powImp : @Int.pow = @powImp := by
  funext m n
  change m^n = _
  dsimp [powImp]
  split <;> rename_i h
  · rcases h with (h | h)
    · simp [ofNat_natAbs_of_nonneg h]
    · rw [← natAbs_pow, ofNat_natAbs_of_nonneg (Int.pow_nonneg_of_even h)]
  · simp at h
    obtain ⟨h₁, h₂⟩ := h
    rw [Int.natCast_pow, ofNat_natAbs_of_nonpos (by omega), Int.neg_pow, h₂]
    simp

end Int
