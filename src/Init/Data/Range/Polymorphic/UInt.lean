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

namespace Std.PRange

instance : UpwardEnumerable UInt8 where
  succ? x := Option.guard (· ≠ 0) (x + 1)
  succMany? n x := let s := x.toNat + n; if s < UInt8.size then some (.ofNat s) else none

instance : LawfulUpwardEnumerable UInt8 where
  ne_of_lt := by
    simp only [UpwardEnumerable.LT, UpwardEnumerable.succMany?]
    rintro ⟨n, hn⟩ b ⟨m, hm⟩
    simp only [Nat.reducePow, UInt8.ofBitVec_ofFin, UInt8.ofFin_mk, ne_eq]
    split at hm
    · rename_i h
      simp at hm
      intro h'
      cases hm
      rw [← UInt8.toNat_inj] at h'
      simp at h'
      simp at h
      simp [UInt8.size] at h
      rw [Nat.mod_eq_of_lt h] at h'
      omega
    · nomatch hm
  succMany?_zero := by simp [UpwardEnumerable.succMany?, UInt8.toNat_lt_size]
  succMany?_succ := by
    simp only [UpwardEnumerable.succMany?, UpwardEnumerable.succ?]
    intro n b
    apply Eq.symm
    split <;> split
    · rename_i h
      simp [UInt8.ofNat_add, UInt8.add_assoc]
      intro h'
      replace h' := congrArg UInt8.toNat h'
      simp at h'
      simp [UInt8.size] at h
      omega
    · have : b.toNat + n + 1 = UInt8.size := by omega
      simp
      replace this := congrArg UInt8.ofNat this
      simpa [UInt8.ofNat_size] using this
    · omega
    · simp

instance : LawfulUpwardEnumerableLE UInt8 where
  le_iff x y := by
    simp [UpwardEnumerable.LE, UpwardEnumerable.succMany?, UInt8.le_iff_toNat_le]
    apply Iff.intro
    · intro hle
      refine ⟨y.toNat - x.toNat, ?_⟩
      apply And.intro
      · have : x.toNat < UInt8.size := UInt8.toNat_lt_size _
        have : y.toNat < UInt8.size := UInt8.toNat_lt_size _
        omega
      · rw [UInt8.ofNat_sub hle, UInt8.ofNat_toNat, UInt8.ofNat_toNat, UInt8.add_comm,
          UInt8.sub_add_cancel]
    · rintro ⟨n, hn, rfl⟩
      rw [UInt8.size] at hn
      rw [UInt8.toNat_add, UInt8.toNat_ofNat', Nat.mod_eq_of_lt (a := n), Nat.mod_eq_of_lt]
      all_goals omega

instance : LawfulOrderLT UInt8 := inferInstance
instance : LawfulUpwardEnumerableLT UInt8 := inferInstance
instance : LawfulUpwardEnumerableLT UInt8 := inferInstance
instance : LawfulUpwardEnumerableLowerBound .closed UInt8 := inferInstance
instance : LawfulUpwardEnumerableUpperBound .closed UInt8 := inferInstance
instance : LawfulUpwardEnumerableLowerBound .open UInt8 := inferInstance
instance : LawfulUpwardEnumerableUpperBound .open UInt8 := inferInstance

instance : RangeSize .closed UInt8 where
  size bound a := bound.toNat + 1 - a.toNat

instance : RangeSize .open UInt8 := RangeSize.openOfClosed

instance : LawfulRangeSize .closed UInt8 where
  size_eq_zero_of_not_isSatisfied bound x := by
    simp? [SupportsUpperBound.IsSatisfied, RangeSize.size]
    intro h
    rw [← UInt8.toNat_lt_toNat] at h
    omega
  size_eq_one_of_succ?_eq_none bound x := by
    simp [SupportsUpperBound.IsSatisfied, RangeSize.size, UpwardEnumerable.succ?]
    intro hle hz
    rw [← UInt8.toNat_le_toNat] at hle
    replace hz := congrArg UInt8.toNat hz
    simp only [UInt8.toNat_add, UInt8.reduceToNat, Nat.reducePow, UInt8.toNat_zero] at hz
    have := UInt8.toNat_lt bound
    omega
  size_eq_succ_of_succ?_eq_some bound init x := by
    simp only [SupportsUpperBound.IsSatisfied, succ?, ne_eq, decide_not, Option.guard_eq_some_iff,
      Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, RangeSize.size, and_imp]
    rintro hi rfl  hi'
    have := UInt8.toNat_lt bound
    rw [← UInt8.toNat_le_toNat] at hi
    rw [← UInt8.toNat_inj] at hi'
    rw [UInt8.toNat_add, UInt8.toNat_zero, UInt8.toNat_one] at hi'
    have : init.toNat < 2 ^ 8 - 1 := by omega
    rw [UInt8.toNat_add, UInt8.toNat_one, Nat.mod_eq_of_lt]
    all_goals omega

end Std.PRange
