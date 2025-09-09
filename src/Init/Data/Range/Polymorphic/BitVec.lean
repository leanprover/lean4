/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Range.Polymorphic.Instances
public import Init.Data.Order.Lemmas
public import Init.Data.UInt
import Init.Omega

public section

open Std Std.PRange

namespace BitVec

variable {n : Nat}

instance : UpwardEnumerable (BitVec n) where
  succ? i := if i + 1 = 0 then none else some (i + 1)
  succMany? m i := if h : i.toNat + m < 2 ^ n then some (.ofNatLT _ h) else none

instance : LawfulUpwardEnumerable (BitVec n) where
  ne_of_lt := by
    simp +contextual [UpwardEnumerable.LT, ← BitVec.toNat_inj, succMany?] at ⊢
    omega
  succMany?_zero := by simp [UpwardEnumerable.succMany?, BitVec.toNat_lt_twoPow_of_le]
  succMany?_succ? a b := by
    simp +contextual [← BitVec.toNat_inj, succMany?, succ?]
    split <;> split
    · rename_i h
      simp [← BitVec.toNat_inj, Nat.mod_eq_of_lt (a := b.toNat + a + 1) ‹_›]
      all_goals omega
    · omega
    · have : b.toNat + a + 1 = 2 ^ n := by omega
      simp [this]
    · simp

instance : LawfulUpwardEnumerableLE (BitVec n) where
  le_iff x y := by
    simp [UpwardEnumerable.LE, UpwardEnumerable.succMany?, BitVec.le_def]
    apply Iff.intro
    · intro hle
      refine ⟨y.toNat - x.toNat, ?_⟩
      apply Exists.intro <;> simp [Nat.add_sub_cancel' hle, BitVec.toNat_lt_twoPow_of_le]
    · rintro ⟨n, hn, rfl⟩
      simp [BitVec.ofNatLT]

instance : LawfulOrderLT (BitVec n) := inferInstance
instance : LawfulUpwardEnumerableLT (BitVec n) := inferInstance
instance : LawfulUpwardEnumerableLT (BitVec n) := inferInstance
instance : LawfulUpwardEnumerableLowerBound .closed (BitVec n) := inferInstance
instance : LawfulUpwardEnumerableUpperBound .closed (BitVec n) := inferInstance
instance : LawfulUpwardEnumerableLowerBound .open (BitVec n) := inferInstance
instance : LawfulUpwardEnumerableUpperBound .open (BitVec n) := inferInstance

instance : RangeSize .closed (BitVec n) where
  size bound a := bound.toNat + 1 - a.toNat

instance : RangeSize .open (BitVec n) := RangeSize.openOfClosed

instance : LawfulRangeSize .closed (BitVec n) where
  size_eq_zero_of_not_isSatisfied bound x := by
    simp [SupportsUpperBound.IsSatisfied, BitVec.not_le, RangeSize.size, BitVec.lt_def]
    omega
  size_eq_one_of_succ?_eq_none bound x := by
    have := BitVec.toNat_lt_twoPow_of_le (Nat.le_refl _) (x := bound)
    have (h : (x.toNat + 1) % 2 ^ n = 0) : x.toNat = 2 ^ n - 1 := by
      apply Classical.not_not.mp
      intro _
      simp [Nat.mod_eq_of_lt (a := x.toNat + 1) (b := 2 ^ n) (by omega)] at h
    simp [RangeSize.size, BitVec.le_def, ← BitVec.toNat_inj, succ?]
    omega
  size_eq_succ_of_succ?_eq_some bound init x := by
    have (h : ¬ (init.toNat + 1) % 2 ^ n = 0) : ¬ (init.toNat + 1 ≥ 2 ^ n) := by
      intro _
      have : init.toNat + 1 = 2 ^ n := by omega
      simp_all
    simp_all +contextual [RangeSize.size, BitVec.le_def, ← BitVec.toNat_inj,
      Nat.mod_eq_of_lt (a := init.toNat + 1) (b := 2 ^ n), succ?]
    omega

instance : LawfulRangeSize .open (BitVec n) := inferInstance

end BitVec
