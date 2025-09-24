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

instance : LawfulUpwardEnumerableLT (BitVec n) := inferInstance
instance : LawfulUpwardEnumerableLT (BitVec n) := inferInstance

instance : Rxc.HasSize (BitVec n) where
  size lo hi := hi.toNat + 1 - lo.toNat

instance : Rxc.LawfulHasSize (BitVec n) where
  size_eq_zero_of_not_le bound x := by
    simp [BitVec.not_le, Rxc.HasSize.size, BitVec.lt_def]
    omega
  size_eq_one_of_succ?_eq_none lo hi := by
    have := BitVec.toNat_lt_twoPow_of_le (Nat.le_refl _) (x := hi)
    have (h : (lo.toNat + 1) % 2 ^ n = 0) : lo.toNat = 2 ^ n - 1 := by
      apply Classical.not_not.mp
      intro _
      simp [Nat.mod_eq_of_lt (a := lo.toNat + 1) (b := 2 ^ n) (by omega)] at h
    simp [Rxc.HasSize.size, BitVec.le_def, ← BitVec.toNat_inj, succ?]
    omega
  size_eq_succ_of_succ?_eq_some lo hi x := by
    have (h : ¬ (lo.toNat + 1) % 2 ^ n = 0) : ¬ (lo.toNat + 1 ≥ 2 ^ n) := by
      intro _
      have : lo.toNat + 1 = 2 ^ n := by omega
      simp_all
    simp_all +contextual [Rxc.HasSize.size, BitVec.le_def, ← BitVec.toNat_inj,
      Nat.mod_eq_of_lt (a := lo.toNat + 1) (b := 2 ^ n), succ?]
    omega

instance : Rxc.IsAlwaysFinite (BitVec n) := inferInstance

instance : Rxo.HasSize (BitVec n) := .ofClosed
instance : Rxo.LawfulHasSize (BitVec n) := inferInstance
instance : Rxo.IsAlwaysFinite (BitVec n) := inferInstance

-- TODO: Rxi.LawfulHasSize

end BitVec
