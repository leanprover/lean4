/-
Copyright (c) 2025 Lean FRO, LLC. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
prelude
import Init.Grind.CommRing.Basic
import Init.Data.UInt.Lemmas

namespace Int

theorem toNat_emod {x y : Int} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (x % y).toNat = x.toNat % y.toNat :=
  match x, y, eq_ofNat_of_zero_le hx, eq_ofNat_of_zero_le hy with
  | _, _, ⟨_, rfl⟩, ⟨_, rfl⟩ => rfl

end Int

namespace UInt8

theorem ofNat_mod_size : ofNat (x % 2 ^ 8) = ofNat x := by
  simp [ofNat, BitVec.ofNat, Fin.ofNat']
/-- Variant of `UInt8.ofNat_mod_size` replacing `2 ^ 8` with `256`.-/
theorem ofNat_mod_size' : ofNat (x % 256) = ofNat x := ofNat_mod_size

def ofInt (x : Int) : UInt8 := ofNat (x % 2 ^ 8).toNat

theorem ofInt_add (x y : Int) : ofInt (x + y) = ofInt x + ofInt y := by
  dsimp only [UInt8.ofInt]
  rw [Int.add_emod]
  have h₁ : 0 ≤ x % 2 ^ 8 := Int.emod_nonneg _ (by decide)
  have h₂ : 0 ≤ y % 2 ^ 8 := Int.emod_nonneg _ (by decide)
  have h₃ : 0 ≤ x % 2 ^ 8 + y % 2 ^ 8 := Int.add_nonneg h₁ h₂
  rw [Int.toNat_emod h₃ (by decide), Int.toNat_add h₁ h₂]
  have : (2 ^ 8 : Int).toNat = 2 ^ 8 := rfl
  rw [this, UInt8.ofNat_mod_size, UInt8.ofNat_add]

theorem ofInt_mul (x y : Int) : ofInt (x * y) = ofInt x * ofInt y := by
  dsimp only [UInt8.ofInt]
  rw [Int.mul_emod]
  have h₁ : 0 ≤ x % 2 ^ 8 := Int.emod_nonneg _ (by decide)
  have h₂ : 0 ≤ y % 2 ^ 8 := Int.emod_nonneg _ (by decide)
  have h₃ : 0 ≤ (x % 2 ^ 8) * (y % 2 ^ 8) := Int.mul_nonneg h₁ h₂
  rw [Int.toNat_emod h₃ (by decide), Int.toNat_mul h₁ h₂]
  have : (2 ^ 8 : Int).toNat = 2 ^ 8 := rfl
  rw [this, UInt8.ofNat_mod_size, UInt8.ofNat_mul]

theorem ofInt_neg_one : ofInt (-1) = -1 := rfl

theorem ofInt_neg (x : Int) : ofInt (-x) = -ofInt x := by
  rw [Int.neg_eq_neg_one_mul, ofInt_mul, ofInt_neg_one, ← UInt8.neg_eq_neg_one_mul]

-- TODO: this should be replaced via an `@[extern]` with a native implementation
def pow (x : UInt8) (n : Nat) : UInt8 :=
  match n with
  | 0 => 1
  | n + 1 => pow x n * x

instance : Pow UInt8 Nat where
  pow x n := pow x n

theorem pow_zero (x : UInt8) : x ^ 0 = 1 := rfl
theorem pow_succ (x : UInt8) (n : Nat) : x ^ (n + 1) = x ^ n * x := rfl

end UInt8

namespace UInt16

theorem ofNat_mod_size : ofNat (x % 2 ^ 16) = ofNat x := by
  simp [ofNat, BitVec.ofNat, Fin.ofNat']
/-- Variant of `UInt16.ofNat_mod_size` replacing `2 ^ 16` with `65536`.-/
theorem ofNat_mod_size' : ofNat (x % 65536) = ofNat x := ofNat_mod_size

def ofInt (x : Int) : UInt16 := ofNat (x % 2 ^ 16).toNat

theorem ofInt_add (x y : Int) : ofInt (x + y) = ofInt x + ofInt y := by
  dsimp only [UInt16.ofInt]
  rw [Int.add_emod]
  have h₁ : 0 ≤ x % 2 ^ 16 := Int.emod_nonneg _ (by decide)
  have h₂ : 0 ≤ y % 2 ^ 16 := Int.emod_nonneg _ (by decide)
  have h₃ : 0 ≤ x % 2 ^ 16 + y % 2 ^ 16 := Int.add_nonneg h₁ h₂
  rw [Int.toNat_emod h₃ (by decide), Int.toNat_add h₁ h₂]
  have : (2 ^ 16 : Int).toNat = 2 ^ 16 := rfl
  rw [this, UInt16.ofNat_mod_size, UInt16.ofNat_add]

theorem ofInt_mul (x y : Int) : ofInt (x * y) = ofInt x * ofInt y := by
  dsimp only [UInt16.ofInt]
  rw [Int.mul_emod]
  have h₁ : 0 ≤ x % 2 ^ 16 := Int.emod_nonneg _ (by decide)
  have h₂ : 0 ≤ y % 2 ^ 16 := Int.emod_nonneg _ (by decide)
  have h₃ : 0 ≤ (x % 2 ^ 16) * (y % 2 ^ 16) := Int.mul_nonneg h₁ h₂
  rw [Int.toNat_emod h₃ (by decide), Int.toNat_mul h₁ h₂]
  have : (2 ^ 16 : Int).toNat = 2 ^ 16 := rfl
  rw [this, UInt16.ofNat_mod_size, UInt16.ofNat_mul]

theorem ofInt_neg_one : ofInt (-1) = -1 := rfl

theorem ofInt_neg (x : Int) : ofInt (-x) = -ofInt x := by
  rw [Int.neg_eq_neg_one_mul, ofInt_mul, ofInt_neg_one, ← UInt16.neg_eq_neg_one_mul]

-- TODO: this should be replaced via an `@[extern]` with a native implementation
def pow (x : UInt16) (n : Nat) : UInt16 :=
  match n with
  | 0 => 1
  | n + 1 => pow x n * x

instance : Pow UInt16 Nat where
  pow x n := pow x n

theorem pow_zero (x : UInt16) : x ^ 0 = 1 := rfl
theorem pow_succ (x : UInt16) (n : Nat) : x ^ (n + 1) = x ^ n * x := rfl

end UInt16

namespace UInt32

theorem ofNat_mod_size : ofNat (x % 2 ^ 32) = ofNat x := by
  simp [ofNat, BitVec.ofNat, Fin.ofNat']
/-- Variant of `UInt32.ofNat_mod_size` replacing `2 ^ 32` with `4294967296`.-/
theorem ofNat_mod_size' : ofNat (x % 4294967296) = ofNat x := ofNat_mod_size

def ofInt (x : Int) : UInt32 := ofNat (x % 2 ^ 32).toNat

theorem ofInt_add (x y : Int) : ofInt (x + y) = ofInt x + ofInt y := by
  dsimp only [UInt32.ofInt]
  rw [Int.add_emod]
  have h₁ : 0 ≤ x % 2 ^ 32 := Int.emod_nonneg _ (by decide)
  have h₂ : 0 ≤ y % 2 ^ 32 := Int.emod_nonneg _ (by decide)
  have h₃ : 0 ≤ x % 2 ^ 32 + y % 2 ^ 32 := Int.add_nonneg h₁ h₂
  rw [Int.toNat_emod h₃ (by decide), Int.toNat_add h₁ h₂]
  have : (2 ^ 32 : Int).toNat = 2 ^ 32 := rfl
  rw [this, UInt32.ofNat_mod_size, UInt32.ofNat_add]

theorem ofInt_mul (x y : Int) : ofInt (x * y) = ofInt x * ofInt y := by
  dsimp only [UInt32.ofInt]
  rw [Int.mul_emod]
  have h₁ : 0 ≤ x % 2 ^ 32 := Int.emod_nonneg _ (by decide)
  have h₂ : 0 ≤ y % 2 ^ 32 := Int.emod_nonneg _ (by decide)
  have h₃ : 0 ≤ (x % 2 ^ 32) * (y % 2 ^ 32) := Int.mul_nonneg h₁ h₂
  rw [Int.toNat_emod h₃ (by decide), Int.toNat_mul h₁ h₂]
  have : (2 ^ 32 : Int).toNat = 2 ^ 32 := rfl
  rw [this, UInt32.ofNat_mod_size, UInt32.ofNat_mul]

theorem ofInt_neg_one : ofInt (-1) = -1 := rfl

theorem ofInt_neg (x : Int) : ofInt (-x) = -ofInt x := by
  rw [Int.neg_eq_neg_one_mul, ofInt_mul, ofInt_neg_one, ← UInt32.neg_eq_neg_one_mul]

-- TODO: this should be replaced via an `@[extern]` with a native implementation
def pow (x : UInt32) (n : Nat) : UInt32 :=
  match n with
  | 0 => 1
  | n + 1 => pow x n * x

instance : Pow UInt32 Nat where
  pow x n := pow x n

theorem pow_zero (x : UInt32) : x ^ 0 = 1 := rfl
theorem pow_succ (x : UInt32) (n : Nat) : x ^ (n + 1) = x ^ n * x := rfl

end UInt32

namespace UInt64

theorem ofNat_mod_size : ofNat (x % 2 ^ 64) = ofNat x := by
  simp [ofNat, BitVec.ofNat, Fin.ofNat']
/-- Variant of `UInt64.ofNat_mod_size` replacing `2 ^ 64` with `18446744073709551616`.-/
theorem ofNat_mod_size' : ofNat (x % 18446744073709551616) = ofNat x := ofNat_mod_size

def ofInt (x : Int) : UInt64 := ofNat (x % 2 ^ 64).toNat

theorem ofInt_add (x y : Int) : ofInt (x + y) = ofInt x + ofInt y := by
  dsimp only [UInt64.ofInt]
  rw [Int.add_emod]
  have h₁ : 0 ≤ x % 2 ^ 64 := Int.emod_nonneg _ (by decide)
  have h₂ : 0 ≤ y % 2 ^ 64 := Int.emod_nonneg _ (by decide)
  have h₃ : 0 ≤ x % 2 ^ 64 + y % 2 ^ 64 := Int.add_nonneg h₁ h₂
  rw [Int.toNat_emod h₃ (by decide), Int.toNat_add h₁ h₂]
  have : (2 ^ 64 : Int).toNat = 2 ^ 64 := rfl
  rw [this, UInt64.ofNat_mod_size, UInt64.ofNat_add]

theorem ofInt_mul (x y : Int) : ofInt (x * y) = ofInt x * ofInt y := by
  dsimp only [UInt64.ofInt]
  rw [Int.mul_emod]
  have h₁ : 0 ≤ x % 2 ^ 64 := Int.emod_nonneg _ (by decide)
  have h₂ : 0 ≤ y % 2 ^ 64 := Int.emod_nonneg _ (by decide)
  have h₃ : 0 ≤ (x % 2 ^ 64) * (y % 2 ^ 64) := Int.mul_nonneg h₁ h₂
  rw [Int.toNat_emod h₃ (by decide), Int.toNat_mul h₁ h₂]
  have : (2 ^ 64 : Int).toNat = 2 ^ 64 := rfl
  rw [this, UInt64.ofNat_mod_size, UInt64.ofNat_mul]

theorem ofInt_neg_one : ofInt (-1) = -1 := rfl

theorem ofInt_neg (x : Int) : ofInt (-x) = -ofInt x := by
  rw [Int.neg_eq_neg_one_mul, ofInt_mul, ofInt_neg_one, ← UInt64.neg_eq_neg_one_mul]

-- TODO: this should be replaced via an `@[extern]` with a native implementation
def pow (x : UInt64) (n : Nat) : UInt64 :=
  match n with
  | 0 => 1
  | n + 1 => pow x n * x

instance : Pow UInt64 Nat where
  pow x n := pow x n

theorem pow_zero (x : UInt64) : x ^ 0 = 1 := rfl
theorem pow_succ (x : UInt64) (n : Nat) : x ^ (n + 1) = x ^ n * x := rfl

end UInt64

namespace System.Platform

theorem two_pow_numBits_nonneg : 0 ≤ (2 ^ System.Platform.numBits : Int) := by
  rcases System.Platform.numBits_eq with h | h <;>
  · rw [h]
    decide
theorem two_pow_numBits_ne_zero : (2 ^ System.Platform.numBits : Int) ≠ 0 := by
  rcases System.Platform.numBits_eq with h | h <;>
  · rw [h]
    decide

end System.Platform

namespace USize

open System.Platform (numBits two_pow_numBits_nonneg two_pow_numBits_ne_zero)

theorem ofNat_mod_size : ofNat (x % 2 ^ numBits) = ofNat x := by
  simp [ofNat, BitVec.ofNat, Fin.ofNat']

def ofInt (x : Int) : USize := ofNat (x % 2 ^ numBits).toNat

theorem ofInt_add (x y : Int) : ofInt (x + y) = ofInt x + ofInt y := by
  dsimp only [USize.ofInt]
  rw [Int.add_emod]
  have h₁ : 0 ≤ x % 2 ^ numBits := Int.emod_nonneg _ two_pow_numBits_ne_zero
  have h₂ : 0 ≤ y % 2 ^ numBits := Int.emod_nonneg _ two_pow_numBits_ne_zero
  have h₃ : 0 ≤ x % 2 ^ numBits + y % 2 ^ numBits := Int.add_nonneg h₁ h₂
  rw [Int.toNat_emod h₃ two_pow_numBits_nonneg, Int.toNat_add h₁ h₂]
  have : (2 ^ numBits : Int).toNat = 2 ^ numBits := by
    rcases System.Platform.numBits_eq with h | h <;>
    · rw [h]
      decide
  rw [this, USize.ofNat_mod_size, USize.ofNat_add]

theorem ofInt_mul (x y : Int) : ofInt (x * y) = ofInt x * ofInt y := by
  dsimp only [USize.ofInt]
  rw [Int.mul_emod]
  have h₁ : 0 ≤ x % 2 ^ numBits := Int.emod_nonneg _ two_pow_numBits_ne_zero
  have h₂ : 0 ≤ y % 2 ^ numBits := Int.emod_nonneg _ two_pow_numBits_ne_zero
  have h₃ : 0 ≤ (x % 2 ^ numBits) * (y % 2 ^ numBits) := Int.mul_nonneg h₁ h₂
  rw [Int.toNat_emod h₃ two_pow_numBits_nonneg, Int.toNat_mul h₁ h₂]
  have : (2 ^ numBits : Int).toNat = 2 ^ numBits := by
    rcases System.Platform.numBits_eq with h | h <;>
    · rw [h]
      decide
  rw [this, USize.ofNat_mod_size, USize.ofNat_mul]

theorem ofInt_one : ofInt 1 = 1 := by
  rcases System.Platform.numBits_eq with h | h <;>
  · apply USize.toNat_inj.mp
    simp_all [USize.ofInt, USize.ofNat, size, toNat]

theorem ofInt_neg_one : ofInt (-1) = -1 := by
  rcases System.Platform.numBits_eq with h | h <;>
  · apply USize.toNat_inj.mp
    simp_all [USize.ofInt, USize.ofNat, size, toNat]

theorem ofInt_neg (x : Int) : ofInt (-x) = -ofInt x := by
  rw [Int.neg_eq_neg_one_mul, ofInt_mul, ofInt_neg_one, ← USize.neg_eq_neg_one_mul]

-- TODO: this should be replaced via an `@[extern]` with a native implementation
def pow (x : USize) (n : Nat) : USize :=
  match n with
  | 0 => 1
  | n + 1 => pow x n * x

instance : Pow USize Nat where
  pow x n := pow x n

theorem pow_zero (x : USize) : x ^ 0 = 1 := rfl
theorem pow_succ (x : USize) (n : Nat) : x ^ (n + 1) = x ^ n * x := rfl

end USize

namespace Lean.Grind

instance : IntCast UInt8 where
  intCast x := UInt8.ofInt x

instance : CommRing UInt8 where
  add_assoc := UInt8.add_assoc
  add_comm := UInt8.add_comm
  add_zero := UInt8.add_zero
  neg_add_cancel := UInt8.add_left_neg
  mul_assoc := UInt8.mul_assoc
  mul_comm := UInt8.mul_comm
  mul_one := UInt8.mul_one
  left_distrib _ _ _ := UInt8.mul_add
  zero_mul _ := UInt8.zero_mul
  sub_eq_add_neg := UInt8.sub_eq_add_neg
  pow_zero := UInt8.pow_zero
  pow_succ := UInt8.pow_succ
  ofNat_add := UInt8.ofNat_add
  ofNat_mul := UInt8.ofNat_mul

instance : IsCharP UInt8 (2 ^ 8) where
  ofNat_eq_zero_iff {x} := by
    have : OfNat.ofNat x = UInt8.ofNat x := rfl
    simp [this, UInt8.ofNat_eq_iff_mod_eq_toNat]

instance : IntCast UInt16 where
  intCast x := UInt16.ofInt x

instance : CommRing UInt16 where
  add_assoc := UInt16.add_assoc
  add_comm := UInt16.add_comm
  add_zero := UInt16.add_zero
  neg_add_cancel := UInt16.add_left_neg
  mul_assoc := UInt16.mul_assoc
  mul_comm := UInt16.mul_comm
  mul_one := UInt16.mul_one
  left_distrib _ _ _ := UInt16.mul_add
  zero_mul _ := UInt16.zero_mul
  sub_eq_add_neg := UInt16.sub_eq_add_neg
  pow_zero := UInt16.pow_zero
  pow_succ := UInt16.pow_succ
  ofNat_add := UInt16.ofNat_add
  ofNat_mul := UInt16.ofNat_mul

instance : IsCharP UInt16 (2 ^ 16) where
  ofNat_eq_zero_iff {x} := by
    have : OfNat.ofNat x = UInt16.ofNat x := rfl
    simp [this, UInt16.ofNat_eq_iff_mod_eq_toNat]

instance : IntCast UInt32 where
  intCast x := UInt32.ofInt x

instance : CommRing UInt32 where
  add_assoc := UInt32.add_assoc
  add_comm := UInt32.add_comm
  add_zero := UInt32.add_zero
  neg_add_cancel := UInt32.add_left_neg
  mul_assoc := UInt32.mul_assoc
  mul_comm := UInt32.mul_comm
  mul_one := UInt32.mul_one
  left_distrib _ _ _ := UInt32.mul_add
  zero_mul _ := UInt32.zero_mul
  sub_eq_add_neg := UInt32.sub_eq_add_neg
  pow_zero := UInt32.pow_zero
  pow_succ := UInt32.pow_succ
  ofNat_add := UInt32.ofNat_add
  ofNat_mul := UInt32.ofNat_mul

instance : IsCharP UInt32 (2 ^ 32) where
  ofNat_eq_zero_iff {x} := by
    have : OfNat.ofNat x = UInt32.ofNat x := rfl
    simp [this, UInt32.ofNat_eq_iff_mod_eq_toNat]

instance : IntCast UInt64 where
  intCast x := UInt64.ofInt x

instance : CommRing UInt64 where
  add_assoc := UInt64.add_assoc
  add_comm := UInt64.add_comm
  add_zero := UInt64.add_zero
  neg_add_cancel := UInt64.add_left_neg
  mul_assoc := UInt64.mul_assoc
  mul_comm := UInt64.mul_comm
  mul_one := UInt64.mul_one
  left_distrib _ _ _ := UInt64.mul_add
  zero_mul _ := UInt64.zero_mul
  sub_eq_add_neg := UInt64.sub_eq_add_neg
  pow_zero := UInt64.pow_zero
  pow_succ := UInt64.pow_succ
  ofNat_add := UInt64.ofNat_add
  ofNat_mul := UInt64.ofNat_mul

instance : IsCharP UInt64 (2 ^ 64) where
  ofNat_eq_zero_iff {x} := by
    have : OfNat.ofNat x = UInt64.ofNat x := rfl
    simp [this, UInt64.ofNat_eq_iff_mod_eq_toNat]

instance : IntCast USize where
  intCast x := USize.ofInt x

instance : CommRing USize where
  add_assoc := USize.add_assoc
  add_comm := USize.add_comm
  add_zero := USize.add_zero
  neg_add_cancel := USize.add_left_neg
  mul_assoc := USize.mul_assoc
  mul_comm := USize.mul_comm
  mul_one := USize.mul_one
  left_distrib _ _ _ := USize.mul_add
  zero_mul _ := USize.zero_mul
  sub_eq_add_neg := USize.sub_eq_add_neg
  pow_zero := USize.pow_zero
  pow_succ := USize.pow_succ
  ofNat_add := USize.ofNat_add
  ofNat_mul := USize.ofNat_mul

open System.Platform

instance : IsCharP USize (2 ^ numBits) where
  ofNat_eq_zero_iff {x} := by
    have : OfNat.ofNat x = USize.ofNat x := rfl
    simp [this, USize.ofNat_eq_iff_mod_eq_toNat]

end Lean.Grind
