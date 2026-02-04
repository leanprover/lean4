/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
import Init.Data.BitVec.Bootstrap
import Init.Data.BitVec.Lemmas
import Init.Data.Int.DivMod.Lemmas
import Init.Data.Int.Pow
import Init.Data.Nat.Div.Lemmas
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Mod
import Init.Data.Option.Lemmas
import Init.Data.Range.Polymorphic.BitVec
import Init.Omega

/-!
# Ranges on signed bit vectors

This is an internal library implementing an alternative, signed notion of ranges
on bit vectors. It is only used internally for the construction of ranges on signed number types
(see `Init.Data.Range.Polymorphic.SInt`).
-/

open Std Std.PRange

namespace BitVec.Signed

/-
The elaborator tends to recurse too deeply when working with large numbers in `Int*`
and `BitVec`. Therefore, we define sealed versions of `BitVec.intMin` and `BitVec.intMax`.
-/
def intMinSealed n : BitVec n := ↑(2 ^ (n - 1) : Nat)
def intMaxSealed n : BitVec n := ↑(2 ^ (n - 1) - 1 : Nat)
theorem intMinSealed_def : intMinSealed n = ↑(2 ^ (n - 1) : Nat) := (rfl)
theorem intMaxSealed_def : intMaxSealed n = ↑(2 ^ (n - 1) - 1 : Nat) := (rfl)
seal intMinSealed intMaxSealed

def rotate (x : BitVec n) : BitVec n := x + intMinSealed n

theorem intMaxSealed_eq_intMinSealed_add :
    intMaxSealed n = intMinSealed n + ↑(2 ^ n - 1 : Nat) := by
  match n with
  | 0 => simp [eq_nil (intMaxSealed 0), eq_nil (intMinSealed 0)]
  | n + 1 =>
    simp only [intMaxSealed_def, Nat.add_one_sub_one, natCast_eq_ofNat, intMinSealed_def,
      ← ofNat_add, ← toNat_inj, toNat_ofNat, Nat.mod_eq_mod_iff]
    exact ⟨1, 0, by omega⟩

theorem intMinSealed_add_intMinSealed :
    intMinSealed n + intMinSealed n = 0 := by
  match n with
  | 0 => simp [eq_nil (intMinSealed 0)]
  | n + 1 =>
    simp [intMinSealed_def, ← BitVec.ofNat_add, show 2 ^ n + 2 ^ n = 2 ^ (n + 1) by omega,
      ← BitVec.toNat_inj]

theorem rotate_neg_eq_intMinSealed_sub {x : BitVec n} :
    rotate (-x) = intMinSealed n - x := by
  simp only [rotate, intMinSealed_def, natCast_eq_ofNat]
  rw [eq_sub_iff_add_eq, BitVec.add_comm, ← BitVec.add_assoc, BitVec.add_neg_eq_sub,
    BitVec.sub_self, BitVec.zero_add]

theorem rotate_add {x y : BitVec n} : rotate (x + y) = rotate x + y := by
  simp [rotate, BitVec.add_assoc, BitVec.add_comm y]

theorem rotate_sub {x y : BitVec n} : rotate (x - y) = rotate x - y := by
  simp [BitVec.sub_eq_add_neg, rotate_add]

theorem rotate_intMinSealed : rotate (intMinSealed n) = ↑(0 : Nat) := by
  simp [rotate, intMinSealed_add_intMinSealed]

theorem rotate_intMaxSealed : rotate (intMaxSealed n) = ↑(2 ^ n - 1 : Nat) := by
  simp [intMaxSealed_eq_intMinSealed_add, rotate_add, rotate_intMinSealed]

theorem rotate_rotate {x : BitVec n} : rotate (rotate x) = x := by
  match n with
  | 0 => simp [eq_nil x, rotate, intMinSealed_def]
  | n + 1 =>
    simp only [rotate, BitVec.add_assoc]
    simp [← BitVec.toNat_inj, ← Nat.two_mul, intMinSealed_def, show 2 * 2 ^ n = 2 ^ (n + 1) by omega]

theorem rotate_map_eq_iff {x y : Option (BitVec n)} :
    rotate <$> x = y ↔ x = rotate <$> y := by
  suffices h : ∀ x y : Option (BitVec n), rotate <$> x = y → x = rotate <$> y by
    exact ⟨h x y, fun h' => (h y x h'.symm).symm⟩
  intro x y h
  replace h := congrArg (rotate <$> ·) h
  simpa [Function.comp_def, rotate_rotate] using h

scoped instance instUpwardEnumerable : UpwardEnumerable (BitVec n) where
  succ? x := rotate <$> UpwardEnumerable.succ? (rotate x)
  succMany? n x := rotate <$> UpwardEnumerable.succMany? n (rotate x)

theorem succ?_rotate {x : BitVec n} :
    succ? (rotate x) = (haveI := BitVec.instUpwardEnumerable (n := n); rotate <$> succ? x) := by
  simp [succ?, rotate_rotate]

theorem succMany?_rotate {x : BitVec n} :
    succMany? m (rotate x) =
      (haveI := BitVec.instUpwardEnumerable (n := n); rotate <$> succMany? m x) := by
  simp [succMany?, rotate_rotate]

theorem sle_iff_rotate_le_rotate {x y : BitVec n} :
    x.sle y ↔ rotate x ≤ rotate y := by
  match n with
  | 0 => simp [eq_nil x, eq_nil y]
  | n + 1 =>
    simp only [sle_iff_toInt_le, BitVec.toInt, Nat.pow_add, Nat.pow_one, Nat.mul_comm _ 2,
      Nat.zero_lt_succ, Nat.mul_lt_mul_left, Int.natCast_mul, Int.cast_ofNat_Int, Int.natCast_pow,
      rotate, intMinSealed_def, Nat.add_one_sub_one, natCast_eq_ofNat, le_def, toNat_add,
      toNat_ofNat, Nat.add_mod_mod]
    split <;> split
    · simp only [Int.ofNat_le]
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
    · have : (↑y.toNat : Int) - 2 * 2 ^ n < 0 := by
        have := BitVec.toNat_lt_twoPow_of_le (x := y) (Nat.le_refl _)
        simp [Nat.pow_add, Nat.mul_comm _ 2] at this
        simp only [← Int.ofNat_lt, Int.natCast_mul, Int.cast_ofNat_Int, Int.natCast_pow] at this
        omega
      have : ¬ (↑x.toNat ≤ (↑y.toNat : Int) - 2 * 2 ^ n) := by
        apply Int.not_le_of_gt
        calc _ < 0 := this
             _ ≤ _ := by omega
      simp only [this, false_iff, Nat.not_le, gt_iff_lt]
      rw [Nat.mod_eq_mod_iff (x := y.toNat + 2 ^ n) (y := y.toNat - 2 ^ n) (z := 2 * 2 ^ n) |>.mpr]
      · rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        omega
      · exact ⟨0, 1, by omega⟩
    · have : (↑x.toNat : Int) - 2 * 2 ^ n ≤ ↑y.toNat := by
        have : x.toNat < 2 * 2 ^ n := by omega
        have : (↑x.toNat : Int) < 2 * 2 ^ n := by simpa [← Int.ofNat_lt] using this
        omega
      simp only [this, true_iff, ge_iff_le]
      rw [Nat.mod_eq_mod_iff (x := x.toNat + 2 ^ n) (y := x.toNat - 2 ^ n) (z := 2 * 2 ^ n) |>.mpr]
      · rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        omega
      · exact ⟨0, 1, by omega⟩
    · simp only [Int.sub_le_sub_right_iff, Int.ofNat_le]
      rw [Nat.mod_eq_mod_iff (x := x.toNat + 2 ^ n) (y := x.toNat - 2 ^ n) (z := 2 * 2 ^ n)
          |>.mpr ⟨0, 1, by omega⟩,
        Nat.mod_eq_mod_iff (x := y.toNat + 2 ^ n) (y := y.toNat - 2 ^ n) (z := 2 * 2 ^ n)
          |>.mpr ⟨0, 1, by omega⟩,
        Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      omega

theorem rotate_inj {x y : BitVec n} :
    rotate x = rotate y ↔ x = y := by
  apply Iff.intro
  all_goals
    intro h
    simpa [rotate_rotate] using congrArg rotate h

theorem rotate_eq_iff {x y : BitVec n} : rotate x = y ↔ x = rotate y := by
  rw [← rotate_rotate (x := y), rotate_inj, rotate_rotate]

theorem toInt_eq_ofNat_toNat_rotate_sub {x : BitVec n} (h : n > 0) :
    x.toInt = (↑(rotate x).toNat : Int) - ↑(intMinSealed n).toNat := by
  match n with
  | 0 => omega
  | n + 1 =>
    simp only [BitVec.toInt, Int.natCast_pow, Int.cast_ofNat_Int, rotate, intMinSealed_def,
      Nat.add_one_sub_one, natCast_eq_ofNat, toNat_add, toNat_ofNat, Nat.add_mod_mod,
      Int.natCast_emod, Int.natCast_add]
    rw [Int.emod_eq_of_lt (a := 2 ^ n)]; rotate_left
    · exact Int.le_of_lt (Int.pow_pos (by omega))
    · rw [Int.pow_add, Int.pow_succ, Int.pow_zero, Int.one_mul, Int.mul_comm, Int.two_mul]
      exact Int.lt_add_of_pos_right _ (Int.pow_pos (by omega))
    have : (2 : Int) ^ n > 0 := Int.pow_pos (by omega)
    split <;> rename_i h
    · rw [Nat.pow_add, Nat.pow_one, Nat.mul_comm _ 2, Nat.mul_lt_mul_left (by omega),
        ← Int.ofNat_lt, Int.natCast_pow, Int.cast_ofNat_Int] at h
      rw [Int.emod_eq_of_lt (by omega) (by omega)]
      omega
    · rw [Nat.pow_add, Nat.pow_one, Nat.mul_comm _ 2, Nat.mul_lt_mul_left (by omega),
        ← Int.ofNat_lt, Int.natCast_pow, Int.cast_ofNat_Int] at h
      simp only [Int.pow_add, Int.reducePow, Int.mul_comm _ 2, Int.two_mul, ← Int.sub_sub,
        Int.sub_left_inj]
      rw [eq_comm, Int.emod_eq_iff (by omega)]
      refine ⟨by omega, ?_, ?_⟩
      · have := BitVec.toNat_lt_twoPow_of_le (x := x) (Nat.le_refl _)
        rw [Int.ofNat_natAbs_of_nonneg (by omega)]
        simp only [Nat.pow_add, Nat.pow_one, ← Int.ofNat_lt, Int.natCast_mul, Int.natCast_pow,
          Int.cast_ofNat_Int] at this
        omega
      · conv => rhs; rw [← Int.sub_sub, Int.sub_sub (b := 2 ^ n), Int.add_comm, ← Int.sub_sub]
        exact ⟨-1, by omega⟩

theorem ofNat_eq_rotate_ofInt_sub {n k : Nat} :
    BitVec.ofNat n k = rotate (BitVec.ofInt n (↑k - ↑(intMinSealed n).toNat)) := by
  match n with
  | 0 => simp only [eq_nil (BitVec.ofNat _ _), eq_nil (rotate _)]
  | n + 1 =>
    simp only [intMinSealed, natCast_eq_ofNat, toNat_ofNat, Int.natCast_emod, Int.natCast_pow]
    rw [Int.emod_eq_of_lt]
    · simp [rotate, ← toInt_inj, intMinSealed, toInt_ofNat']
    · exact Int.le_of_lt (Int.pow_pos (by omega))
    · exact Int.pow_lt_pow_of_lt (by omega) (by omega)

scoped instance instLE : LE (BitVec n) where le x y := x.sle y
scoped instance instLT : LT (BitVec n) where lt x y := x.slt y
scoped instance instDecidableLE : DecidableLE (BitVec n) :=
  fun x y => inferInstanceAs (Decidable <| x.sle y)
scoped instance instDecidableLT : DecidableLT (BitVec n) :=
  fun x y => inferInstanceAs (Decidable <| x.slt y)

scoped instance : LawfulOrderLT (BitVec n) where
  lt_iff x y := by
    simp only [LE.le, LT.lt]
    simpa [BitVec.slt_iff_toInt_lt, BitVec.sle_iff_toInt_le] using Int.le_of_lt

scoped instance : IsPartialOrder (BitVec n) where
  le_refl x := by simp only [LE.le]; simp [BitVec.sle_iff_toInt_le]
  le_trans := by
    simp only [LE.le]
    simpa [BitVec.sle_iff_toInt_le] using fun _ _ _ => Int.le_trans
  le_antisymm := by
    simp only [LE.le, ← BitVec.toInt_inj]
    simpa [BitVec.sle_iff_toInt_le] using fun _ _ => Int.le_antisymm

scoped instance : LawfulUpwardEnumerableLE (BitVec n) where
  le_iff x y := by
    rw [← rotate_rotate (x := x), ← rotate_rotate (x := y)]
    generalize (rotate x) = x; generalize (rotate y) = y
    letI := BitVec.instUpwardEnumerable (n := n)
    letI := instLEBitVec (w := n)
    simp only [LE.le]
    simp [sle_iff_rotate_le_rotate, UpwardEnumerable.le_iff, rotate_rotate,
      UpwardEnumerable.le_iff_exists, succMany?_rotate, rotate_inj]

scoped instance :
    LawfulUpwardEnumerable (BitVec n) where
  ne_of_lt x y h := by
    rw [← rotate_rotate (x := x), ← rotate_rotate (x := y)] at h ⊢
    generalize rotate x = x at h ⊢
    generalize rotate y = y at h ⊢
    letI : UpwardEnumerable (BitVec n) := BitVec.instUpwardEnumerable
    have : x ≠ y := by
      apply UpwardEnumerable.ne_of_lt
      obtain ⟨n, hn⟩ := h
      refine ⟨n, ?_⟩
      rwa [succMany?_rotate, rotate_map_eq_iff, Option.map_eq_map, Option.map_some, rotate_rotate] at hn
    apply this.imp; intro heq
    simpa [rotate_rotate] using congrArg rotate heq
  succMany?_zero x := by
    rw [← rotate_rotate (x := x)]
    generalize rotate x = x
    letI : UpwardEnumerable (BitVec n) := BitVec.instUpwardEnumerable
    simp [succMany?_rotate, succMany?_zero]
  succMany?_add_one m x := by
    rw [← rotate_rotate (x := x)]
    generalize rotate x = x
    letI : UpwardEnumerable (BitVec n) := BitVec.instUpwardEnumerable
    simp [succMany?_rotate, succMany?_add_one, Option.bind_map, Function.comp_def, succ?_rotate]

scoped instance : LawfulUpwardEnumerableLT (BitVec n) := inferInstance

scoped instance instRxcHasSize : Rxc.HasSize (BitVec n) where
  size lo hi :=
    haveI := BitVec.instRxcHasSize (n := n)
    Rxc.HasSize.size (rotate lo) (rotate hi)

scoped instance instRxcLawfulHasSize : Rxc.LawfulHasSize (BitVec n) where
  size_eq_zero_of_not_le bound x := by
    simp only [LE.le]
    match n with
    | 0 => simp [eq_nil x, eq_nil bound]
    | n + 1 =>
      simp [BitVec.sle_iff_toInt_le, Rxc.HasSize.size,
        toInt_eq_ofNat_toNat_rotate_sub (show n + 1 > 0 by omega)]
      omega
  size_eq_one_of_succ?_eq_none lo hi := by
    rw [← rotate_rotate (x := lo)]
    generalize rotate lo = lo
    simp only [LE.le]
    match n with
    | 0 => simp [eq_nil lo, eq_nil hi, succ?, rotate, Rxc.HasSize.size, intMinSealed_def]
    | n + 1 =>
      simp [BitVec.sle_iff_toInt_le, toInt_eq_ofNat_toNat_rotate_sub,
        Rxc.HasSize.size, rotate_rotate, succ?_rotate, Option.map_eq_map, Option.map_eq_none_iff,
        succ?_eq_none]
      omega
  size_eq_succ_of_succ?_eq_some lo hi x := by
    rw [← rotate_rotate (x := lo)]
    generalize rotate lo = lo
    simp only [LE.le]
    match n with
    | 0 => simp [eq_nil lo, eq_nil hi, succ?, rotate, Rxc.HasSize.size, intMinSealed_def]
    | n + 1 =>
      simp only [sle_iff_toInt_le, Nat.zero_lt_succ, toInt_eq_ofNat_toNat_rotate_sub,
        rotate_rotate, succ?_rotate, Option.map_eq_map, Option.map_eq_some_iff, succ?_eq_some,
        Rxc.HasSize.size, forall_exists_index, and_imp]
      rintro h y h' hy rfl
      simp only [rotate_rotate]
      omega

scoped instance instRxcIsAlwaysFinite : Rxc.IsAlwaysFinite (BitVec n) := inferInstance

scoped instance instRxoHasSize : Rxo.HasSize (BitVec n) := .ofClosed
scoped instance instRxoLawfulHasSize : Rxo.LawfulHasSize (BitVec n) := .of_closed
scoped instance instRxoIsAlwaysFinite : Rxo.IsAlwaysFinite (BitVec n) := inferInstance

scoped instance instRxiHasSize : Rxi.HasSize (BitVec n) where
  size lo := 2 ^ n - (rotate lo).toNat

scoped instance instRxiLawfulHasSize : Rxi.LawfulHasSize (BitVec n) where
  size_eq_one_of_succ?_eq_none x := by
    rw [← rotate_rotate (x := x)]
    generalize rotate x = x
    simp only [succ?_rotate, Option.map_eq_map, Option.map_eq_none_iff, Rxi.HasSize.size,
      rotate_rotate]
    letI := BitVec.instRxiHasSize (n := n)
    exact Rxi.size_eq_one_of_succ?_eq_none x
  size_eq_succ_of_succ?_eq_some lo lo' := by
    rw [← rotate_rotate (x := lo), ← rotate_rotate (x := lo')]
    generalize rotate lo = lo
    generalize rotate lo' = lo'
    simp only [succ?_rotate, Option.map_eq_map, Option.map_eq_some_iff, rotate_inj, exists_eq_right,
      instRxiHasSize, rotate_rotate]
    letI := BitVec.instRxiHasSize (n := n)
    exact Rxi.size_eq_succ_of_succ?_eq_some lo lo'

scoped instance instRxiIsAlwaysFinite : Rxi.IsAlwaysFinite (BitVec n) := inferInstance

end BitVec.Signed
