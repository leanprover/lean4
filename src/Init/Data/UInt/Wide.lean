/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

prelude
public import Init.Data.UInt.Lemmas
import all Init.Data.UInt.Lemmas

public section

namespace UInt64

@[simp] theorem toNat_mulHi (a b : UInt64) : (a.mulHi b).toNat = a.toNat * b.toNat / 2 ^ 64 := by
  apply UInt64.toNat_ofNat_of_lt'
  exact (Nat.div_lt_iff_lt_mul (by decide)).mpr (Nat.mul_lt_mul'' a.toNat_lt_size b.toNat_lt_size)

@[simp] theorem mulHi_zero (a : UInt64) : a.mulHi 0 = 0 := by
  apply UInt64.toNat.inj; simp

@[simp] theorem zero_mulHi (a : UInt64) : (0 : UInt64).mulHi a = 0 := by
  apply UInt64.toNat.inj; simp

@[simp] theorem mulHi_one (a : UInt64) : a.mulHi 1 = 0 := by
  apply UInt64.toNat.inj
  simp [Nat.div_eq_of_lt a.toNat_lt_size]

@[simp] theorem one_mulHi (a : UInt64) : (1 : UInt64).mulHi a = 0 := by
  apply UInt64.toNat.inj
  simp [Nat.div_eq_of_lt a.toNat_lt_size]

theorem mulHi_comm (a b : UInt64) : a.mulHi b = b.mulHi a := by
  apply UInt64.toNat.inj; simp [Nat.mul_comm]

@[simp] theorem mulFull_eq (a b : UInt64) : a.mulFull b = (a * b, a.mulHi b) := by
  simp only [mulFull, mulHi, Prod.mk.injEq, and_true]
  apply UInt64.toNat.inj
  simp

theorem fst_mulFull (a b : UInt64) : (a.mulFull b).1 = a * b := by simp

theorem snd_mulFull (a b : UInt64) : (a.mulFull b).2 = a.mulHi b := by simp

theorem toNat_mulFull (a b : UInt64) :
    (a.mulFull b).1.toNat + 2 ^ 64 * (a.mulFull b).2.toNat = a.toNat * b.toNat := by
  simp only [mulFull_eq, UInt64.toNat_mul, toNat_mulHi]
  omega

@[simp] theorem fst_addCarry (a b : UInt64) (c : Bool) :
    (a.addCarry b c).1 = a + b + c.toUInt64 := by
  apply UInt64.toNat.inj
  simp only [addCarry, UInt64.toNat_ofNat', UInt64.toNat_add, Bool.toNat_toUInt64]
  omega

@[simp] theorem snd_addCarry (a b : UInt64) (c : Bool) :
    (a.addCarry b c).2 = decide (2 ^ 64 ≤ a.toNat + b.toNat + c.toNat) := rfl

theorem toNat_addCarry (a b : UInt64) (c : Bool) :
    (a.addCarry b c).1.toNat + 2 ^ 64 * (a.addCarry b c).2.toNat = a.toNat + b.toNat + c.toNat := by
  have ha : a.toNat < 2 ^ 64 := a.toNat_lt_size
  have hb : b.toNat < 2 ^ 64 := b.toNat_lt_size
  have hc := c.toNat_le
  simp only [fst_addCarry, snd_addCarry, UInt64.toNat_add, Bool.toNat_toUInt64]
  by_cases h : 2 ^ 64 ≤ a.toNat + b.toNat + c.toNat <;> simp [h] <;> omega

@[simp] theorem fst_subBorrow (a b : UInt64) (c : Bool) :
    (a.subBorrow b c).1 = a - b - c.toUInt64 := by
  have ha : a.toNat < 2 ^ 64 := a.toNat_lt_size
  have hb : b.toNat < 2 ^ 64 := b.toNat_lt_size
  have hc := c.toNat_le
  apply UInt64.toNat.inj
  simp only [subBorrow, UInt64.toNat_sub, Bool.toNat_toUInt64, UInt64.size]
  split <;> simp only [UInt64.toNat_ofNat'] <;> omega

@[simp] theorem snd_subBorrow (a b : UInt64) (c : Bool) :
    (a.subBorrow b c).2 = decide (a.toNat < b.toNat + c.toNat) := by
  simp only [subBorrow]
  split <;> simp <;> omega

theorem toNat_subBorrow (a b : UInt64) (c : Bool) :
    (a.subBorrow b c).1.toNat + b.toNat + c.toNat = a.toNat + 2 ^ 64 * (a.subBorrow b c).2.toNat := by
  have ha : a.toNat < 2 ^ 64 := a.toNat_lt_size
  have hb : b.toNat < 2 ^ 64 := b.toNat_lt_size
  have hc := c.toNat_le
  simp only [fst_subBorrow, snd_subBorrow, UInt64.toNat_sub, Bool.toNat_toUInt64]
  by_cases h : a.toNat < b.toNat + c.toNat <;> simp [h] <;> omega

@[csimp] theorem mulFull_eq_mulFullImpl : @mulFull = @mulFullImpl := by
  funext a b
  rw [mulFull_eq]
  rfl

@[csimp] theorem addCarry_eq_addCarryImpl : @addCarry = @addCarryImpl := by
  funext a b c
  have ha : a.toNat < 2 ^ 64 := a.toNat_lt_size
  have hb : b.toNat < 2 ^ 64 := b.toNat_lt_size
  have hc := c.toNat_le
  simp only [addCarryImpl]
  ext
  · simp
  · rw [snd_addCarry, Bool.eq_iff_iff]
    simp only [decide_eq_true_iff, Bool.or_eq_true, UInt64.lt_iff_toNat_lt, UInt64.toNat_add,
      Bool.toNat_toUInt64]
    omega

@[csimp] theorem subBorrow_eq_subBorrowImpl : @subBorrow = @subBorrowImpl := by
  funext a b c
  have ha : a.toNat < 2 ^ 64 := a.toNat_lt_size
  have hb : b.toNat < 2 ^ 64 := b.toNat_lt_size
  have hc := c.toNat_le
  simp only [subBorrowImpl]
  ext
  · simp
  · rw [snd_subBorrow, Bool.eq_iff_iff]
    simp only [decide_eq_true_iff, Bool.or_eq_true, UInt64.lt_iff_toNat_lt, UInt64.toNat_sub,
      Bool.toNat_toUInt64]
    omega

end UInt64
