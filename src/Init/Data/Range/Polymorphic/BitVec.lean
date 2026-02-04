/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Range.Polymorphic.Instances
import Init.Omega
import Init.Data.BitVec.Bootstrap
import Init.Data.BitVec.Lemmas
import Init.Data.Int.Lemmas
import Init.Data.Int.Order
import Init.Data.Nat.Lemmas
import Init.Data.Option.Lemmas

open Std Std.PRange

namespace BitVec

public section

variable {n : Nat}

instance : UpwardEnumerable (BitVec n) where
  succ? i := if i + 1 = 0 then none else some (i + 1)
  succMany? m i := if h : i.toNat + m < 2 ^ n then some (.ofNatLT _ h) else none

theorem succ?_eq_none {x : BitVec n} :
    UpwardEnumerable.succ? x = none ↔ x.toNat = 2 ^ n - 1 := by
  simp [succ?, ← BitVec.toNat_inj]
  apply Iff.intro
  · refine fun h => Classical.not_not.mp fun _ => ?_
    simp [Nat.mod_eq_of_lt (a := x.toNat + 1) (b := 2 ^ n) (by omega)] at h
  · have := Nat.two_pow_pos n
    simp +contextual [show 2 ^ n - 1 + 1 = 2 ^ n by omega]

theorem succ?_eq_some {x y : BitVec n} :
    succ? x = some y ↔ x.toNat < 2 ^ n - 1 ∧ y.toNat = x.toNat + 1 := by
  match h : succ? x with
  | none => simp_all [succ?_eq_none]
  | some y' =>
    simp only [Option.some.injEq]
    apply Iff.intro
    · rintro rfl
      have : ¬ succ? x = none := fun _ => by simp_all
      simp only [succ?_eq_none] at this
      simp only [succ?, ofNat_eq_ofNat, Option.ite_none_left_eq_some, Option.some.injEq] at h
      apply And.intro
      · omega
      · simp only [← toNat_inj, toNat_add, toNat_ofNat, Nat.add_mod_mod, Nat.zero_mod] at h
        rw [Nat.mod_eq_of_lt (by omega)] at h
        exact h.2.symm
    · simp only [succ?, ofNat_eq_ofNat, ← toNat_inj, toNat_add, toNat_ofNat, Nat.add_mod_mod,
        Nat.zero_mod, Option.ite_none_left_eq_some, Option.some.injEq] at h
      intro h'
      rw [Nat.mod_eq_of_lt (by omega)] at h
      simp [← BitVec.toNat_inj, *]

instance : LawfulUpwardEnumerable (BitVec n) where
  ne_of_lt := by
    simp +contextual [UpwardEnumerable.LT, ← BitVec.toNat_inj, succMany?] at ⊢
    omega
  succMany?_zero := by simp [UpwardEnumerable.succMany?, BitVec.toNat_lt_twoPow_of_le]
  succMany?_add_one a b := by
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

instance instRxcHasSize : Rxc.HasSize (BitVec n) where
  size lo hi := hi.toNat + 1 - lo.toNat

instance instRxcLawfulHasSize : Rxc.LawfulHasSize (BitVec n) where
  size_eq_zero_of_not_le bound x := by
    simp only [BitVec.not_le, Rxc.HasSize.size, BitVec.lt_def]
    omega
  size_eq_one_of_succ?_eq_none lo hi := by
    have := BitVec.toNat_lt_twoPow_of_le (Nat.le_refl _) (x := hi)
    simp only [succ?_eq_none, Rxc.HasSize.size, BitVec.le_def]
    omega
  size_eq_succ_of_succ?_eq_some lo hi x := by
    simp only [succ?_eq_some, Rxc.HasSize.size, BitVec.le_def]
    omega

instance instRxcIsAlwaysFinite : Rxc.IsAlwaysFinite (BitVec n) := inferInstance

instance instRxoHasSize : Rxo.HasSize (BitVec n) := .ofClosed
instance instRxoLawfulHasSize : Rxo.LawfulHasSize (BitVec n) := inferInstance
instance instRxoIsAlwaysFinite : Rxo.IsAlwaysFinite (BitVec n) := inferInstance

instance instRxiHasSize : Rxi.HasSize (BitVec n) where
  size lo := 2 ^ n - lo.toNat

instance instRxiLawfulHasSize : Rxi.LawfulHasSize (BitVec n) where
  size_eq_one_of_succ?_eq_none x := by
    simp only [succ?_eq_none, Rxi.HasSize.size]
    omega
  size_eq_succ_of_succ?_eq_some lo lo' := by
    simp only [succ?_eq_some, Rxi.HasSize.size]
    omega

instance instRxiIsAlwaysFinite : Rxi.IsAlwaysFinite (BitVec n) := inferInstance

end
end BitVec
