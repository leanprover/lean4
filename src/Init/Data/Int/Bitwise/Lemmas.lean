/-
Copyright (c) 2023 Siddharth Bhat. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Siddharth Bhat, Jeremy Avigad
-/
module

prelude
public import Init.Data.Int.Bitwise.Basic
import all Init.Data.Int.Bitwise.Basic
public import Init.Data.Int.DivMod.Basic
import Init.ByCases
import Init.Data.Int.DivMod.Lemmas
import Init.Data.Int.Pow
import Init.Data.Nat.Bitwise.Lemmas
import Init.Data.Nat.Lemmas
import Init.Omega
import Init.RCases

public section

namespace Int

theorem shiftRight_eq (n : Int) (s : Nat) : n >>> s = Int.shiftRight n s := rfl

@[simp, norm_cast]
theorem natCast_shiftRight (n s : Nat) : n >>> s = (n : Int) >>> s := rfl

@[simp]
theorem negSucc_shiftRight (m n : Nat) :
    -[m+1] >>> n = -[m >>>n +1] := rfl

theorem shiftRight_add (i : Int) (m n : Nat) :
    i >>> (m + n) = i >>> m >>> n := by
  simp only [shiftRight_eq, Int.shiftRight]
  cases i <;> simp [Nat.shiftRight_add]

grind_pattern shiftRight_add => i >>> (m + n) where
  i =/= 0

grind_pattern shiftRight_add => i >>> m >>> n where
  i =/= 0

theorem shiftRight_eq_div_pow (m : Int) (n : Nat) :
    m >>> n = m / ((2 ^ n) : Nat) := by
  simp only [shiftRight_eq, Int.shiftRight, Nat.shiftRight_eq_div_pow]
  split
  · simp
  · rw [negSucc_ediv _ (by norm_cast; exact Nat.pow_pos (Nat.zero_lt_two))]
    rfl

@[simp, grind =]
theorem zero_shiftRight (n : Nat) : (0 : Int) >>> n = 0 := by
  simp [Int.shiftRight_eq_div_pow]

@[simp, grind =]
theorem shiftRight_zero (n : Int) : n >>> 0 = n := by
  simp [Int.shiftRight_eq_div_pow]

theorem le_shiftRight_of_nonpos {n : Int} {s : Nat} (h : n ≤ 0) : n ≤ n >>> s := by
  simp only [Int.shiftRight_eq, Int.shiftRight, Int.ofNat_eq_natCast]
  split
  case _ _ _ m =>
    simp only [ofNat_eq_natCast] at h
    by_cases hm : m = 0
    · simp [hm]
    · omega
  case _ _ _ m =>
    by_cases hm : m = 0
    · simp [hm]
    · have := Nat.shiftRight_le m s
      omega

theorem shiftRight_le_of_nonneg {n : Int} {s : Nat} (h : 0 ≤ n) : n >>> s ≤ n := by
  simp only [Int.shiftRight_eq, Int.shiftRight, Int.ofNat_eq_natCast]
  split
  case _ _ _ m =>
    simp only [Int.ofNat_eq_natCast] at h
    by_cases hm : m = 0
    · simp [hm]
    · have := Nat.shiftRight_le m s
      rw [ofNat_eq_natCast]
      omega
  case _ _ _ m =>
    omega

theorem le_shiftRight_of_nonneg {n : Int} {s : Nat} (h : 0 ≤ n) : 0 ≤ (n >>> s) := by
  rw [Int.shiftRight_eq_div_pow]
  by_cases h' : s = 0
  · simp [h', h]
  · have := @Nat.pow_pos 2 s (by omega)
    have := @Int.ediv_nonneg n (2^s) h (by norm_cast at *; omega)
    norm_cast at *

theorem shiftRight_le_of_nonpos {n : Int} {s : Nat} (h : n ≤ 0) : (n >>> s) ≤ 0 := by
  rw [Int.shiftRight_eq_div_pow]
  by_cases h' : s = 0
  · simp [h', h]
  · have : 1 < 2 ^ s := Nat.one_lt_two_pow (by omega)
    have rl : n / 2 ^ s ≤ 0 := Int.ediv_nonpos_of_nonpos_of_neg (by omega) (by norm_cast at *; omega)
    norm_cast at *

@[simp, norm_cast]
theorem natCast_shiftLeft (n s : Nat) : n <<< s = (n : Int) <<< s := rfl

@[simp, grind =]
theorem zero_shiftLeft (n : Nat) : (0 : Int) <<< n = 0 := by
  change ((0 <<< n : Nat) : Int) = 0
  simp

@[simp, grind =]
theorem shiftLeft_zero (n : Int) : n <<< 0 = n := by
  change Int.shiftLeft _ _ = _
  match n with
  | Int.ofNat n
  | Int.negSucc n => simp [Int.shiftLeft]

theorem shiftLeft_succ (m : Int) (n : Nat) : m <<< (n + 1) = (m <<< n) * 2 := by
  change Int.shiftLeft _ _ = Int.shiftLeft _ _ * 2
  match m with
  | (m : Nat) =>
    dsimp only [Int.shiftLeft, Int.ofNat_eq_natCast]
    rw [Nat.shiftLeft_succ, Nat.mul_comm, natCast_mul, ofNat_two]
  | Int.negSucc m =>
    dsimp only [Int.shiftLeft]
    rw [Nat.shiftLeft_succ, Nat.mul_comm, Int.negSucc_eq]
    have := Nat.le_shiftLeft (a := m + 1) (b := n)
    omega

theorem shiftLeft_succ' (m : Int) (n : Nat) : m <<< (n + 1) = 2 * (m <<< n) := by
  rw [shiftLeft_succ, Int.mul_comm]

theorem shiftLeft_eq (a : Int) (b : Nat) : a <<< b = a * 2 ^ b := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [shiftLeft_succ, ih, Int.pow_succ, Int.mul_assoc]

theorem shiftLeft_eq' (a : Int) (b : Nat) : a <<< b = a * (2 ^ b : Nat) := by
  simp [shiftLeft_eq]

theorem shiftLeft_add (a : Int) (b c : Nat) : a <<< (b + c) = a <<< b <<< c := by
  simp [shiftLeft_eq, Int.pow_add, Int.mul_assoc]

@[simp]
theorem shiftLeft_shiftRight_cancel (a : Int) (b : Nat) : a <<< b >>> b = a := by
  simp [shiftLeft_eq, shiftRight_eq_div_pow, mul_ediv_cancel _ (NeZero.ne _)]

theorem shiftLeft_shiftRight_eq_shiftLeft_of_le {b c : Nat} (h : c ≤ b) (a : Int) :
    a <<< b >>> c = a <<< (b - c) := by
  obtain ⟨b, rfl⟩ := h.dest
  simp [shiftLeft_eq, Int.pow_add, shiftRight_eq_div_pow, Int.mul_left_comm a,
    Int.mul_ediv_cancel_left _ (NeZero.ne _)]

theorem shiftLeft_shiftRight_eq_shiftRight_of_le {b c : Nat} (h : b ≤ c) (a : Int) :
    a <<< b >>> c = a >>> (c - b) := by
  obtain ⟨c, rfl⟩ := h.dest
  simp [shiftRight_add]

theorem shiftLeft_shiftRight_eq (a : Int) (b c : Nat) :
    a <<< b >>> c = a <<< (b - c) >>> (c - b) := by
  rcases Nat.le_total b c with h | h
  · simp [shiftLeft_shiftRight_eq_shiftRight_of_le h, Nat.sub_eq_zero_of_le h]
  · simp [shiftLeft_shiftRight_eq_shiftLeft_of_le h, Nat.sub_eq_zero_of_le h]

@[simp]
theorem shiftRight_shiftLeft_cancel {a : Int} {b : Nat} (h : 2 ^ b ∣ a) : a >>> b <<< b = a := by
  simp [shiftLeft_eq, shiftRight_eq_div_pow, Int.ediv_mul_cancel h]

theorem add_shiftLeft (a b : Int) (n : Nat) : (a + b) <<< n = a <<< n + b <<< n := by
  simp [shiftLeft_eq, Int.add_mul]

theorem neg_shiftLeft (a : Int) (n : Nat) : (-a) <<< n = -a <<< n := by
  simp [Int.shiftLeft_eq, Int.neg_mul]

theorem shiftLeft_mul (a b : Int) (n : Nat) : a <<< n * b = (a * b) <<< n := by
  simp [shiftLeft_eq, Int.mul_right_comm]

theorem mul_shiftLeft (a b : Int) (n : Nat) : a * b <<< n = (a * b) <<< n := by
  simp [shiftLeft_eq, Int.mul_assoc]

theorem shiftLeft_mul_shiftLeft (a b : Int) (m n : Nat) :
    a <<< m * b <<< n = (a * b) <<< (m + n) := by
  simp [shiftLeft_mul, mul_shiftLeft, shiftLeft_add]

@[simp]
theorem shiftLeft_eq_zero_iff {a : Int} {n : Nat} : a <<< n = 0 ↔ a = 0 := by
  simp [shiftLeft_eq, Int.mul_eq_zero, NeZero.ne]

instance {a : Int} {n : Nat} [NeZero a] : NeZero (a <<< n) :=
  ⟨mt shiftLeft_eq_zero_iff.mp (NeZero.ne _)⟩

end Int
