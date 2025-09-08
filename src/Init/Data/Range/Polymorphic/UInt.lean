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
  succ? i := if i + 1 = 0 then none else some (i + 1)
  succMany? n i := if h : i.toNat + n < UInt8.size then some (.ofNatLT _ h) else none

instance : LawfulUpwardEnumerable UInt8 where
  ne_of_lt a b h := by
    obtain ⟨c, hc⟩ := h
    simp [UpwardEnumerable.succMany?, ← UInt8.toNat_inj, UInt8.size] at hc ⊢
    omega
  succMany?_zero x := by simp [UpwardEnumerable.succMany?, x.toNat_lt_size]
  succMany?_succ a b := by
    simp only [UpwardEnumerable.succMany?, UInt8.size, UpwardEnumerable.succ?]
    split <;> split <;> simp [← UInt8.toNat_inj] <;> omega

instance : LawfulUpwardEnumerableLE UInt8 where
  le_iff x y := by
    simp [UpwardEnumerable.LE, UpwardEnumerable.succMany?, UInt8.le_iff_toNat_le]
    apply Iff.intro
    · intro hle
      refine ⟨y.toNat - x.toNat, ?_⟩
      apply Exists.intro
      · rw [ofNatLT_sub (UInt8.toNat_lt y) hle, ofNatLT_toNat, ofNatLT_toNat, UInt8.add_comm,
          UInt8.sub_add_cancel]
      · rw [Nat.add_sub_cancel' ‹_›]
        exact UInt8.toNat_lt _
    · rintro ⟨n, hn, rfl⟩
      rw [UInt8.toNat_add, UInt8.toNat_ofNatLT, Nat.mod_eq_of_lt hn]
      omega

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
    simp only [SupportsUpperBound.IsSatisfied, UInt8.not_le, RangeSize.size, UInt8.lt_iff_toNat_lt]
    omega
  size_eq_one_of_succ?_eq_none bound x := by
    have := UInt8.toNat_lt bound
    simp [RangeSize.size, UInt8.le_iff_toNat_le, ← UInt8.toNat_inj]
    omega
  size_eq_succ_of_succ?_eq_some bound init x := by
    have := UInt8.toNat_lt bound
    simp [RangeSize.size, UInt8.le_iff_toNat_le, ← UInt8.toNat_inj]
    all_goals omega

instance : LawfulRangeSize .open UInt8 := inferInstance

end UInt8

namespace UInt16

instance : UpwardEnumerable UInt16 where
  succ? i := if i + 1 = 0 then none else some (i + 1)
  succMany? n i := if h : i.toNat + n < UInt16.size then some (.ofNatLT _ h) else none

instance : LawfulUpwardEnumerable UInt16 where
  ne_of_lt a b h := by
    obtain ⟨c, hc⟩ := h
    simp [UpwardEnumerable.succMany?, ← UInt16.toNat_inj, UInt16.size] at hc ⊢
    omega
  succMany?_zero x := by simp [UpwardEnumerable.succMany?, x.toNat_lt_size]
  succMany?_succ a b := by
    simp only [UpwardEnumerable.succMany?, UInt16.size, UpwardEnumerable.succ?]
    split <;> split <;> simp [← UInt16.toNat_inj] <;> omega

instance : LawfulUpwardEnumerableLE UInt16 where
  le_iff x y := by
    simp [UpwardEnumerable.LE, UpwardEnumerable.succMany?, UInt16.le_iff_toNat_le]
    apply Iff.intro
    · intro hle
      refine ⟨y.toNat - x.toNat, ?_⟩
      apply Exists.intro
      · rw [ofNatLT_sub (UInt16.toNat_lt y) hle, ofNatLT_toNat, ofNatLT_toNat, UInt16.add_comm,
          UInt16.sub_add_cancel]
      · rw [Nat.add_sub_cancel' ‹_›]
        exact UInt16.toNat_lt _
    · rintro ⟨n, hn, rfl⟩
      rw [UInt16.toNat_add, UInt16.toNat_ofNatLT, Nat.mod_eq_of_lt hn]
      omega

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
    simp only [SupportsUpperBound.IsSatisfied, UInt16.not_le, RangeSize.size, UInt16.lt_iff_toNat_lt]
    omega
  size_eq_one_of_succ?_eq_none bound x := by
    have := UInt16.toNat_lt bound
    simp [RangeSize.size, UInt16.le_iff_toNat_le, ← UInt16.toNat_inj]
    omega
  size_eq_succ_of_succ?_eq_some bound init x := by
    have := UInt16.toNat_lt bound
    simp [RangeSize.size, UInt16.le_iff_toNat_le, ← UInt16.toNat_inj]
    all_goals omega

instance : LawfulRangeSize .open UInt16 := inferInstance

end UInt16

namespace UInt32

instance : UpwardEnumerable UInt32 where
  succ? i := if i + 1 = 0 then none else some (i + 1)
  succMany? n i := if h : i.toNat + n < UInt32.size then some (.ofNatLT _ h) else none

instance : LawfulUpwardEnumerable UInt32 where
  ne_of_lt a b h := by
    obtain ⟨c, hc⟩ := h
    simp [UpwardEnumerable.succMany?, ← UInt32.toNat_inj, UInt32.size] at hc ⊢
    omega
  succMany?_zero x := by simp [UpwardEnumerable.succMany?, x.toNat_lt_size]
  succMany?_succ a b := by
    simp only [UpwardEnumerable.succMany?, UInt32.size, UpwardEnumerable.succ?]
    split <;> split <;> simp [← UInt32.toNat_inj] <;> omega

instance : LawfulUpwardEnumerableLE UInt32 where
  le_iff x y := by
    simp [UpwardEnumerable.LE, UpwardEnumerable.succMany?, UInt32.le_iff_toNat_le]
    apply Iff.intro
    · intro hle
      refine ⟨y.toNat - x.toNat, ?_⟩
      apply Exists.intro
      · rw [ofNatLT_sub (UInt32.toNat_lt y) hle, ofNatLT_toNat, ofNatLT_toNat, UInt32.add_comm,
          UInt32.sub_add_cancel]
      · rw [Nat.add_sub_cancel' ‹_›]
        exact UInt32.toNat_lt _
    · rintro ⟨n, hn, rfl⟩
      rw [UInt32.toNat_add, UInt32.toNat_ofNatLT, Nat.mod_eq_of_lt hn]
      omega

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
    simp only [SupportsUpperBound.IsSatisfied, UInt32.not_le, RangeSize.size, UInt32.lt_iff_toNat_lt]
    omega
  size_eq_one_of_succ?_eq_none bound x := by
    have := UInt32.toNat_lt bound
    simp [RangeSize.size, UInt32.le_iff_toNat_le, ← UInt32.toNat_inj]
    omega
  size_eq_succ_of_succ?_eq_some bound init x := by
    have := UInt32.toNat_lt bound
    simp [RangeSize.size, UInt32.le_iff_toNat_le, ← UInt32.toNat_inj]
    all_goals omega

instance : LawfulRangeSize .open UInt32 := inferInstance

end UInt32

namespace UInt64

instance : UpwardEnumerable UInt64 where
  succ? i := if i + 1 = 0 then none else some (i + 1)
  succMany? n i := if h : i.toNat + n < UInt64.size then some (.ofNatLT _ h) else none

instance : LawfulUpwardEnumerable UInt64 where
  ne_of_lt a b h := by
    obtain ⟨c, hc⟩ := h
    simp [UpwardEnumerable.succMany?, ← UInt64.toNat_inj, UInt64.size] at hc ⊢
    omega
  succMany?_zero x := by simp [UpwardEnumerable.succMany?, x.toNat_lt_size]
  succMany?_succ a b := by
    simp only [UpwardEnumerable.succMany?, UInt64.size, UpwardEnumerable.succ?]
    split <;> split <;> simp [← UInt64.toNat_inj] <;> omega

instance : LawfulUpwardEnumerableLE UInt64 where
  le_iff x y := by
    simp [UpwardEnumerable.LE, UpwardEnumerable.succMany?, UInt64.le_iff_toNat_le]
    apply Iff.intro
    · intro hle
      refine ⟨y.toNat - x.toNat, ?_⟩
      apply Exists.intro
      · rw [ofNatLT_sub (UInt64.toNat_lt y) hle, ofNatLT_toNat, ofNatLT_toNat, UInt64.add_comm,
          UInt64.sub_add_cancel]
      · rw [Nat.add_sub_cancel' ‹_›]
        exact UInt64.toNat_lt _
    · rintro ⟨n, hn, rfl⟩
      rw [UInt64.toNat_add, UInt64.toNat_ofNatLT, Nat.mod_eq_of_lt hn]
      omega

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
    simp only [SupportsUpperBound.IsSatisfied, UInt64.not_le, RangeSize.size, UInt64.lt_iff_toNat_lt]
    omega
  size_eq_one_of_succ?_eq_none bound x := by
    have := UInt64.toNat_lt bound
    simp [RangeSize.size, UInt64.le_iff_toNat_le, ← UInt64.toNat_inj]
    omega
  size_eq_succ_of_succ?_eq_some bound init x := by
    have := UInt64.toNat_lt bound
    simp [RangeSize.size, UInt64.le_iff_toNat_le, ← UInt64.toNat_inj]
    all_goals omega

instance : LawfulRangeSize .open UInt64 := inferInstance

end UInt64

namespace USize

instance : UpwardEnumerable USize where
  succ? i := if i + 1 = 0 then none else some (i + 1)
  succMany? n i := if h : i.toNat + n < USize.size then some (.ofNatLT _ h) else none

instance : LawfulUpwardEnumerable USize where
  ne_of_lt := by
    simp +contextual [UpwardEnumerable.LT, ← USize.toNat_inj, Nat.mod_eq_of_lt] at ⊢
    omega
  succMany?_zero := by simp [UpwardEnumerable.succMany?, USize.toNat_lt_size]
  succMany?_succ a b := by
    simp +contextual [← USize.toNat_inj, size]
    split <;> split
    · rename_i h
      simp [← USize.toNat_inj, Nat.mod_eq_of_lt (a := b.toNat + a + 1) ‹_›,
        Nat.mod_eq_of_lt (a := b.toNat + (a + 1)) ‹_›]
      all_goals omega
    · omega
    · have : b.toNat + a + 1 = 2 ^ System.Platform.numBits := by omega
      simp [this]
    · simp

instance : LawfulUpwardEnumerableLE USize where
  le_iff x y := by
    simp [UpwardEnumerable.LE, UpwardEnumerable.succMany?, USize.le_iff_toNat_le]
    apply Iff.intro
    · intro hle
      refine ⟨y.toNat - x.toNat, ?_⟩
      have := USize.toNat_lt_two_pow_numBits y
      apply Exists.intro
      · rw [ofNatLT_sub ‹_› ‹_›, ofNatLT_toNat, ofNatLT_toNat, USize.add_comm, USize.sub_add_cancel]
      · rwa [Nat.add_comm, Nat.sub_add_cancel hle]
    · rintro ⟨n, hn, rfl⟩
      rw [USize.toNat_add, toNat_ofNatLT, Nat.mod_eq_of_lt (a := x.toNat + n)]
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
    simp only [SupportsUpperBound.IsSatisfied, USize.not_le, RangeSize.size, USize.lt_iff_toNat_lt]
    omega
  size_eq_one_of_succ?_eq_none bound x := by
    simp only [SupportsUpperBound.IsSatisfied, succ?, ite_eq_left_iff, reduceCtorEq, imp_false,
      Decidable.not_not, RangeSize.size]
    intro hle hz
    rw [USize.le_iff_toNat_le] at hle
    replace hz := congrArg USize.toNat hz
    simp only [USize.toNat_add, USize.reduceToNat, USize.toNat_zero] at hz
    have := USize.toNat_lt_two_pow_numBits bound
    have : ¬ (x.toNat + 1 < 2 ^ System.Platform.numBits) := by
      intro h
      rw [Nat.mod_eq_of_lt h] at hz
      omega
    omega
  size_eq_succ_of_succ?_eq_some bound init x := by
    simp only [SupportsUpperBound.IsSatisfied, le_iff_toNat_le, succ?, ← USize.toNat_inj,
      USize.toNat_add, toNat_one, Option.ite_none_left_eq_some, Option.some.injEq,
      RangeSize.size, and_imp]
    rintro hi hi''  hi'
    have := USize.toNat_lt_two_pow_numBits bound
    have : ¬ (init.toNat + 1 ≥ 2 ^ System.Platform.numBits) := by
      intro h
      have : init.toNat + 1 = 2 ^ System.Platform.numBits := by omega
      simp_all
    rw [Nat.mod_eq_of_lt] at hi'
    all_goals omega

instance : LawfulRangeSize .open USize := inferInstance

end USize
