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

namespace UInt8

instance : UpwardEnumerable UInt8 where
  succ? x := Option.guard (· ≠ 0) (x + 1)
  succMany? n x := let s := x.toNat + n; if s < 2 ^ 8 then some (.ofNat s) else none

instance : LawfulUpwardEnumerable UInt8 where
  ne_of_lt := by
    simp only [UpwardEnumerable.LT, UpwardEnumerable.succMany?]
    rintro ⟨n, hn⟩ b ⟨m, hm⟩
    simp only [UInt8.ofBitVec_ofFin]
    split at hm
    · rename_i h
      cases hm
      intro h'
      simp only [UInt8.ofBitVec_ofFin, UInt8.ofFin_mk, UInt8.toNat_ofNatLT] at h
      simp [← UInt8.toNat_inj, Nat.mod_eq_of_lt h] at h'
    · nomatch hm
  succMany?_zero := by simp [UpwardEnumerable.succMany?, UInt8.toNat_lt_size]
  succMany?_succ := by
    simp only [UpwardEnumerable.succMany?, UpwardEnumerable.succ?]
    intro n b
    apply Eq.symm
    split <;> split
    · rename_i h
      simp only [UInt8.ofNat_add, ← UInt8.toNat_ne_toNat,
        decide_not, Option.bind_some, UInt8.add_assoc, UInt8.ofNat_one,
        Option.guard_eq_some_iff, UInt8.toNat_add, UInt8.toNat_ofNat',
        UInt8.reduceToNat, Bool.not_eq_eq_eq_not, Bool.not_true,
        decide_eq_false_iff_not, true_and]
      omega
    · have : b.toNat + n + 1 = 2 ^ 8 := by omega
      simpa [UInt8.ofNat_size] using congrArg UInt8.ofNat this
    · omega
    · simp

instance : LawfulUpwardEnumerableLE UInt8 where
  le_iff x y := by
    simp [UpwardEnumerable.LE, UpwardEnumerable.succMany?, UInt8.le_iff_toNat_le]
    apply Iff.intro
    · intro hle
      refine ⟨y.toNat - x.toNat, ?_⟩
      apply And.intro
      · have := UInt8.toNat_lt x
        have := UInt8.toNat_lt y
        omega
      · rw [UInt8.ofNat_sub hle, UInt8.ofNat_toNat, UInt8.ofNat_toNat, UInt8.add_comm,
          UInt8.sub_add_cancel]
    · rintro ⟨n, hn, rfl⟩
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
    simp only [SupportsUpperBound.IsSatisfied, UInt8.not_le, RangeSize.size, ← UInt8.toNat_lt_toNat]
    omega
  size_eq_one_of_succ?_eq_none bound x := by
    simp only [SupportsUpperBound.IsSatisfied, succ?, ne_eq, decide_not, Option.guard_eq_none_iff,
      Bool.not_eq_eq_eq_not, Bool.not_false, decide_eq_true_eq, RangeSize.size]
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
    rw [← UInt8.toNat_le_toNat] at hi
    rw [← UInt8.toNat_inj, UInt8.toNat_add, UInt8.toNat_zero, UInt8.toNat_one] at hi'
    have := UInt8.toNat_lt bound
    have : init.toNat < 2 ^ 8 - 1 := by omega
    rw [UInt8.toNat_add, UInt8.toNat_one, Nat.mod_eq_of_lt]
    all_goals omega

instance : LawfulRangeSize .open UInt8 := inferInstance

end UInt8

namespace UInt16

instance : UpwardEnumerable UInt16 where
  succ? x := Option.guard (· ≠ 0) (x + 1)
  succMany? n x := let s := x.toNat + n; if s < 2 ^ 16 then some (.ofNat s) else none

instance : LawfulUpwardEnumerable UInt16 where
  ne_of_lt := by
    simp only [UpwardEnumerable.LT, UpwardEnumerable.succMany?]
    rintro ⟨n, hn⟩ b ⟨m, hm⟩
    simp only [UInt16.ofBitVec_ofFin]
    split at hm
    · rename_i h
      cases hm
      intro h'
      simp only [UInt16.ofBitVec_ofFin, UInt16.ofFin_mk, UInt16.toNat_ofNatLT] at h
      simp [← UInt16.toNat_inj, Nat.mod_eq_of_lt h] at h'
    · nomatch hm
  succMany?_zero := by simp [UpwardEnumerable.succMany?, UInt16.toNat_lt_size]
  succMany?_succ := by
    simp only [UpwardEnumerable.succMany?, UpwardEnumerable.succ?]
    intro n b
    apply Eq.symm
    split <;> split
    · rename_i h
      simp only [UInt16.ofNat_add, ← UInt16.toNat_ne_toNat,
        decide_not, Option.bind_some, UInt16.add_assoc, UInt16.ofNat_one,
        Option.guard_eq_some_iff, UInt16.toNat_add, UInt16.toNat_ofNat',
        UInt16.reduceToNat, Bool.not_eq_eq_eq_not, Bool.not_true,
        decide_eq_false_iff_not, true_and]
      omega
    · have : b.toNat + n + 1 = 2 ^ 16 := by omega
      simpa [UInt16.ofNat_size] using congrArg UInt16.ofNat this
    · omega
    · simp

instance : LawfulUpwardEnumerableLE UInt16 where
  le_iff x y := by
    simp [UpwardEnumerable.LE, UpwardEnumerable.succMany?, UInt16.le_iff_toNat_le]
    apply Iff.intro
    · intro hle
      refine ⟨y.toNat - x.toNat, ?_⟩
      apply And.intro
      · have := UInt16.toNat_lt x
        have := UInt16.toNat_lt y
        omega
      · rw [UInt16.ofNat_sub hle, UInt16.ofNat_toNat, UInt16.ofNat_toNat, UInt16.add_comm,
          UInt16.sub_add_cancel]
    · rintro ⟨n, hn, rfl⟩
      rw [UInt16.toNat_add, UInt16.toNat_ofNat', Nat.mod_eq_of_lt (a := n), Nat.mod_eq_of_lt]
      all_goals omega

instance : LawfulOrderLT UInt16 := inferInstance
instance : LawfulUpwardEnumerableLT UInt16 := inferInstance
instance : LawfulUpwardEnumerableLT UInt16 := inferInstance
instance : LawfulUpwardEnumerableLowerBound .closed UInt16 := inferInstance
instance : LawfulUpwardEnumerableUpperBound .closed UInt16 := inferInstance
instance : LawfulUpwardEnumerableLowerBound .open UInt16 := inferInstance
instance : LawfulUpwardEnumerableUpperBound .open UInt16 := inferInstance

instance : RangeSize .closed UInt16 where
  size bound a := bound.toNat + 1 - a.toNat

instance : RangeSize .open UInt16 := RangeSize.openOfClosed

instance : LawfulRangeSize .closed UInt16 where
  size_eq_zero_of_not_isSatisfied bound x := by
    simp only [SupportsUpperBound.IsSatisfied, UInt16.not_le, RangeSize.size, ← UInt16.toNat_lt_toNat]
    omega
  size_eq_one_of_succ?_eq_none bound x := by
    simp only [SupportsUpperBound.IsSatisfied, succ?, ne_eq, decide_not, Option.guard_eq_none_iff,
      Bool.not_eq_eq_eq_not, Bool.not_false, decide_eq_true_eq, RangeSize.size]
    intro hle hz
    rw [← UInt16.toNat_le_toNat] at hle
    replace hz := congrArg UInt16.toNat hz
    simp only [UInt16.toNat_add, UInt16.reduceToNat, Nat.reducePow, UInt16.toNat_zero] at hz
    have := UInt16.toNat_lt bound
    omega
  size_eq_succ_of_succ?_eq_some bound init x := by
    simp only [SupportsUpperBound.IsSatisfied, succ?, ne_eq, decide_not, Option.guard_eq_some_iff,
      Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, RangeSize.size, and_imp]
    rintro hi rfl  hi'
    rw [← UInt16.toNat_le_toNat] at hi
    rw [← UInt16.toNat_inj, UInt16.toNat_add, UInt16.toNat_zero, UInt16.toNat_one] at hi'
    have := UInt16.toNat_lt bound
    have : init.toNat < 2 ^ 16 - 1 := by omega
    rw [UInt16.toNat_add, UInt16.toNat_one, Nat.mod_eq_of_lt]
    all_goals omega

instance : LawfulRangeSize .open UInt16 := inferInstance

end UInt16

namespace UInt32

instance : UpwardEnumerable UInt32 where
  succ? x := Option.guard (· ≠ 0) (x + 1)
  succMany? n x := let s := x.toNat + n; if s < 2 ^ 32 then some (.ofNat s) else none

instance : LawfulUpwardEnumerable UInt32 where
  ne_of_lt := by
    simp only [UpwardEnumerable.LT, UpwardEnumerable.succMany?]
    rintro ⟨n, hn⟩ b ⟨m, hm⟩
    simp only [UInt32.ofBitVec_ofFin]
    split at hm
    · rename_i h
      cases hm
      intro h'
      simp only [UInt32.ofBitVec_ofFin, UInt32.ofFin_mk, UInt32.toNat_ofNatLT] at h
      simp [← UInt32.toNat_inj, Nat.mod_eq_of_lt h] at h'
    · nomatch hm
  succMany?_zero := by simp [UpwardEnumerable.succMany?, UInt32.toNat_lt_size]
  succMany?_succ := by
    simp only [UpwardEnumerable.succMany?, UpwardEnumerable.succ?]
    intro n b
    apply Eq.symm
    split <;> split
    · rename_i h
      simp only [UInt32.ofNat_add, ← UInt32.toNat_ne_toNat,
        decide_not, Option.bind_some, UInt32.add_assoc, UInt32.ofNat_one,
        Option.guard_eq_some_iff, UInt32.toNat_add, UInt32.toNat_ofNat',
        UInt32.reduceToNat, Bool.not_eq_eq_eq_not, Bool.not_true,
        decide_eq_false_iff_not, true_and]
      omega
    · have : b.toNat + n + 1 = 2 ^ 32 := by omega
      simpa [UInt32.ofNat_size] using congrArg UInt32.ofNat this
    · omega
    · simp

instance : LawfulUpwardEnumerableLE UInt32 where
  le_iff x y := by
    simp [UpwardEnumerable.LE, UpwardEnumerable.succMany?, UInt32.le_iff_toNat_le]
    apply Iff.intro
    · intro hle
      refine ⟨y.toNat - x.toNat, ?_⟩
      apply And.intro
      · have := UInt32.toNat_lt x
        have := UInt32.toNat_lt y
        omega
      · rw [UInt32.ofNat_sub hle, UInt32.ofNat_toNat, UInt32.ofNat_toNat, UInt32.add_comm,
          UInt32.sub_add_cancel]
    · rintro ⟨n, hn, rfl⟩
      rw [UInt32.toNat_add, UInt32.toNat_ofNat', Nat.mod_eq_of_lt (a := n), Nat.mod_eq_of_lt]
      all_goals omega

instance : LawfulOrderLT UInt32 := inferInstance
instance : LawfulUpwardEnumerableLT UInt32 := inferInstance
instance : LawfulUpwardEnumerableLT UInt32 := inferInstance
instance : LawfulUpwardEnumerableLowerBound .closed UInt32 := inferInstance
instance : LawfulUpwardEnumerableUpperBound .closed UInt32 := inferInstance
instance : LawfulUpwardEnumerableLowerBound .open UInt32 := inferInstance
instance : LawfulUpwardEnumerableUpperBound .open UInt32 := inferInstance

instance : RangeSize .closed UInt32 where
  size bound a := bound.toNat + 1 - a.toNat

instance : RangeSize .open UInt32 := RangeSize.openOfClosed

instance : LawfulRangeSize .closed UInt32 where
  size_eq_zero_of_not_isSatisfied bound x := by
    simp only [SupportsUpperBound.IsSatisfied, UInt32.not_le, RangeSize.size, ← UInt32.toNat_lt_toNat]
    omega
  size_eq_one_of_succ?_eq_none bound x := by
    simp only [SupportsUpperBound.IsSatisfied, succ?, ne_eq, decide_not, Option.guard_eq_none_iff,
      Bool.not_eq_eq_eq_not, Bool.not_false, decide_eq_true_eq, RangeSize.size]
    intro hle hz
    rw [← UInt32.toNat_le_toNat] at hle
    replace hz := congrArg UInt32.toNat hz
    simp only [UInt32.toNat_add, UInt32.reduceToNat, Nat.reducePow, UInt32.toNat_zero] at hz
    have := UInt32.toNat_lt bound
    omega
  size_eq_succ_of_succ?_eq_some bound init x := by
    simp only [SupportsUpperBound.IsSatisfied, succ?, ne_eq, decide_not, Option.guard_eq_some_iff,
      Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, RangeSize.size, and_imp]
    rintro hi rfl  hi'
    rw [← UInt32.toNat_le_toNat] at hi
    rw [← UInt32.toNat_inj, UInt32.toNat_add, UInt32.toNat_zero, UInt32.toNat_one] at hi'
    have := UInt32.toNat_lt bound
    have : init.toNat < 2 ^ 32 - 1 := by omega
    rw [UInt32.toNat_add, UInt32.toNat_one, Nat.mod_eq_of_lt]
    all_goals omega

instance : LawfulRangeSize .open UInt32 := inferInstance

end UInt32

namespace UInt64

instance : UpwardEnumerable UInt64 where
  succ? x := Option.guard (· ≠ 0) (x + 1)
  succMany? n x := let s := x.toNat + n; if s < 2 ^ 64 then some (.ofNat s) else none

instance : LawfulUpwardEnumerable UInt64 where
  ne_of_lt := by
    simp only [UpwardEnumerable.LT, UpwardEnumerable.succMany?]
    rintro ⟨n, hn⟩ b ⟨m, hm⟩
    simp only [UInt64.ofBitVec_ofFin]
    split at hm
    · rename_i h
      cases hm
      intro h'
      simp only [UInt64.ofBitVec_ofFin, UInt64.ofFin_mk, UInt64.toNat_ofNatLT] at h
      simp [← UInt64.toNat_inj, Nat.mod_eq_of_lt h] at h'
    · nomatch hm
  succMany?_zero := by simp [UpwardEnumerable.succMany?, UInt64.toNat_lt_size]
  succMany?_succ := by
    simp only [UpwardEnumerable.succMany?, UpwardEnumerable.succ?]
    intro n b
    apply Eq.symm
    split <;> split
    · rename_i h
      simp only [UInt64.ofNat_add, ← UInt64.toNat_ne_toNat,
        decide_not, Option.bind_some, UInt64.add_assoc, UInt64.ofNat_one,
        Option.guard_eq_some_iff, UInt64.toNat_add, UInt64.toNat_ofNat',
        UInt64.reduceToNat, Bool.not_eq_eq_eq_not, Bool.not_true,
        decide_eq_false_iff_not, true_and]
      omega
    · have : b.toNat + n + 1 = 2 ^ 64 := by omega
      simpa [UInt64.ofNat_size] using congrArg UInt64.ofNat this
    · omega
    · simp

instance : LawfulUpwardEnumerableLE UInt64 where
  le_iff x y := by
    simp [UpwardEnumerable.LE, UpwardEnumerable.succMany?, UInt64.le_iff_toNat_le]
    apply Iff.intro
    · intro hle
      refine ⟨y.toNat - x.toNat, ?_⟩
      apply And.intro
      · have := UInt64.toNat_lt x
        have := UInt64.toNat_lt y
        omega
      · rw [UInt64.ofNat_sub hle, UInt64.ofNat_toNat, UInt64.ofNat_toNat, UInt64.add_comm,
          UInt64.sub_add_cancel]
    · rintro ⟨n, hn, rfl⟩
      rw [UInt64.toNat_add, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (a := n), Nat.mod_eq_of_lt]
      all_goals omega

instance : LawfulOrderLT UInt64 := inferInstance
instance : LawfulUpwardEnumerableLT UInt64 := inferInstance
instance : LawfulUpwardEnumerableLT UInt64 := inferInstance
instance : LawfulUpwardEnumerableLowerBound .closed UInt64 := inferInstance
instance : LawfulUpwardEnumerableUpperBound .closed UInt64 := inferInstance
instance : LawfulUpwardEnumerableLowerBound .open UInt64 := inferInstance
instance : LawfulUpwardEnumerableUpperBound .open UInt64 := inferInstance

instance : RangeSize .closed UInt64 where
  size bound a := bound.toNat + 1 - a.toNat

instance : RangeSize .open UInt64 := RangeSize.openOfClosed

instance : LawfulRangeSize .closed UInt64 where
  size_eq_zero_of_not_isSatisfied bound x := by
    simp only [SupportsUpperBound.IsSatisfied, UInt64.not_le, RangeSize.size, ← UInt64.toNat_lt_toNat]
    omega
  size_eq_one_of_succ?_eq_none bound x := by
    simp only [SupportsUpperBound.IsSatisfied, succ?, ne_eq, decide_not, Option.guard_eq_none_iff,
      Bool.not_eq_eq_eq_not, Bool.not_false, decide_eq_true_eq, RangeSize.size]
    intro hle hz
    rw [← UInt64.toNat_le_toNat] at hle
    replace hz := congrArg UInt64.toNat hz
    simp only [UInt64.toNat_add, UInt64.reduceToNat, Nat.reducePow, UInt64.toNat_zero] at hz
    have := UInt64.toNat_lt bound
    omega
  size_eq_succ_of_succ?_eq_some bound init x := by
    simp only [SupportsUpperBound.IsSatisfied, succ?, ne_eq, decide_not, Option.guard_eq_some_iff,
      Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, RangeSize.size, and_imp]
    rintro hi rfl  hi'
    rw [← UInt64.toNat_le_toNat] at hi
    rw [← UInt64.toNat_inj, UInt64.toNat_add, UInt64.toNat_zero, UInt64.toNat_one] at hi'
    have := UInt64.toNat_lt bound
    have : init.toNat < 2 ^ 64 - 1 := by omega
    rw [UInt64.toNat_add, UInt64.toNat_one, Nat.mod_eq_of_lt]
    all_goals omega

instance : LawfulRangeSize .open UInt64 := inferInstance

end UInt64

namespace USize

instance : UpwardEnumerable USize where
  succ? x := Option.guard (· ≠ 0) (x + 1)
  succMany? n x :=
    let s := x.toNat + n
    if s < 2 ^ System.Platform.numBits then
      some (.ofNat s)
    else
      none

instance : LawfulUpwardEnumerable USize where
  ne_of_lt := by
    simp only [UpwardEnumerable.LT, UpwardEnumerable.succMany?]
    rintro ⟨n, hn⟩ b ⟨m, hm⟩
    simp only [USize.ofBitVec_ofFin]
    split at hm
    · rename_i h
      cases hm
      intro h'
      simp only [USize.ofBitVec_ofFin, USize.ofFin_mk, USize.toNat_ofNatLT] at h
      simp [← USize.toNat_inj, Nat.mod_eq_of_lt h] at h'
    · nomatch hm
  succMany?_zero := by simp [UpwardEnumerable.succMany?, USize.toNat_lt_size]
  succMany?_succ := by
    simp only [UpwardEnumerable.succMany?, UpwardEnumerable.succ?]
    intro n b
    apply Eq.symm
    split <;> split
    · rename_i h
      simp only [USize.ofNat_add, ← USize.toNat_ne_toNat,
        decide_not, Option.bind_some, USize.add_assoc, USize.ofNat_one,
        Option.guard_eq_some_iff, USize.toNat_add, USize.toNat_ofNat',
        USize.reduceToNat, Bool.not_eq_eq_eq_not, Bool.not_true,
        decide_eq_false_iff_not, true_and]
      rw [Nat.mod_eq_of_lt (a := b.toNat), Nat.mod_eq_of_lt (a := n), Nat.mod_eq_of_lt (a := n + 1),
        Nat.mod_eq_of_lt]
      all_goals omega
    · have : b.toNat + n + 1 = 2 ^ System.Platform.numBits := by omega
      simpa [USize.ofNat_size] using congrArg USize.ofNat this
    · omega
    · simp

instance : LawfulUpwardEnumerableLE USize where
  le_iff x y := by
    simp [UpwardEnumerable.LE, UpwardEnumerable.succMany?, USize.le_iff_toNat_le]
    apply Iff.intro
    · intro hle
      refine ⟨y.toNat - x.toNat, ?_⟩
      apply And.intro
      · have := USize.toNat_lt_two_pow_numBits x
        have := USize.toNat_lt_two_pow_numBits y
        omega
      · rw [USize.ofNat_sub hle, USize.ofNat_toNat, USize.ofNat_toNat, USize.add_comm,
          USize.sub_add_cancel]
    · rintro ⟨n, hn, rfl⟩
      rw [USize.toNat_add, USize.toNat_ofNat', Nat.mod_eq_of_lt (a := n), Nat.mod_eq_of_lt]
      all_goals omega

instance : LawfulOrderLT USize := inferInstance
instance : LawfulUpwardEnumerableLT USize := inferInstance
instance : LawfulUpwardEnumerableLT USize := inferInstance
instance : LawfulUpwardEnumerableLowerBound .closed USize := inferInstance
instance : LawfulUpwardEnumerableUpperBound .closed USize := inferInstance
instance : LawfulUpwardEnumerableLowerBound .open USize := inferInstance
instance : LawfulUpwardEnumerableUpperBound .open USize := inferInstance

instance : RangeSize .closed USize where
  size bound a := bound.toNat + 1 - a.toNat

instance : RangeSize .open USize := RangeSize.openOfClosed

instance : LawfulRangeSize .closed USize where
  size_eq_zero_of_not_isSatisfied bound x := by
    simp only [SupportsUpperBound.IsSatisfied, USize.not_le, RangeSize.size, ← USize.toNat_lt_toNat]
    omega
  size_eq_one_of_succ?_eq_none bound x := by
    simp only [SupportsUpperBound.IsSatisfied, succ?, ne_eq, decide_not, Option.guard_eq_none_iff,
      Bool.not_eq_eq_eq_not, Bool.not_false, decide_eq_true_eq, RangeSize.size]
    intro hle hz
    rw [← USize.toNat_le_toNat] at hle
    replace hz := congrArg USize.toNat hz
    simp only [USize.toNat_add, USize.reduceToNat, USize.toNat_zero] at hz
    have := USize.toNat_lt_two_pow_numBits bound
    have : ¬ (x.toNat + 1 < 2 ^ System.Platform.numBits) := by
      intro h
      rw [Nat.mod_eq_of_lt h] at hz
      omega
    omega
  size_eq_succ_of_succ?_eq_some bound init x := by
    simp only [SupportsUpperBound.IsSatisfied, succ?, ne_eq, decide_not, Option.guard_eq_some_iff,
      Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, RangeSize.size, and_imp]
    rintro hi rfl  hi'
    rw [← USize.toNat_le_toNat] at hi
    rw [← USize.toNat_inj, USize.toNat_add, USize.toNat_zero, USize.toNat_one] at hi'
    have := USize.toNat_lt_two_pow_numBits bound
    have : ¬ (init.toNat + 1 ≥ 2 ^ System.Platform.numBits) := by
      intro h
      have : init.toNat + 1 = 2 ^ System.Platform.numBits := by omega
      simp [this] at hi'
    rw [USize.toNat_add, USize.toNat_one, Nat.mod_eq_of_lt]
    all_goals omega

instance : LawfulRangeSize .open USize := inferInstance

end USize
