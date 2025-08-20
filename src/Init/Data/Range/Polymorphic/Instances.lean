/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Order.Classes
public import Init.Data.Range.Polymorphic.Basic
import Init.Data.Nat.Lemmas
import Init.Data.Order.Lemmas

public section

namespace Std.PRange

instance [LE α] [LT α] [UpwardEnumerable α] [LawfulUpwardEnumerable α]
    [LawfulUpwardEnumerableLE α] [LawfulOrderLT α] : LawfulUpwardEnumerableLT α where
  lt_iff a b := by
    simp only [LawfulOrderLT.lt_iff, LawfulUpwardEnumerableLE.le_iff]
    constructor
    · intro h
      obtain ⟨n, hn⟩ := h.1
      cases n
      · apply h.2.elim
        refine ⟨0, ?_⟩
        simpa [UpwardEnumerable.succMany?_zero] using hn.symm
      exact ⟨_, hn⟩
    · intro h
      constructor
      · match h with | ⟨_, hn⟩ => exact ⟨_, hn⟩
      · exact UpwardEnumerable.not_ge_of_lt h

instance [LE α] [DecidableLE α] [UpwardEnumerable α] [LawfulUpwardEnumerableLE α] :
    LawfulUpwardEnumerableLowerBound .closed α where
  isSatisfied_iff a l := by
    simp [SupportsLowerBound.IsSatisfied, BoundedUpwardEnumerable.init?,
      LawfulUpwardEnumerableLE.le_iff]

instance [LE α] [DecidableLE α] [UpwardEnumerable α] [LawfulUpwardEnumerableLE α]
    [Trans (α := α) (· ≤ ·) (· ≤ ·) (· ≤ ·)]:
    LawfulUpwardEnumerableUpperBound .closed α where
  isSatisfied_of_le u a b hub hab := by
    simp only [SupportsUpperBound.IsSatisfied, ← LawfulUpwardEnumerableLE.le_iff] at hub hab ⊢
    exact Trans.trans hab hub

instance [LT α] [DecidableLT α] [UpwardEnumerable α] [LawfulUpwardEnumerable α]
    [LawfulUpwardEnumerableLT α] :
    LawfulUpwardEnumerableLowerBound .open α where
  isSatisfied_iff a l := by
    simp only [SupportsLowerBound.IsSatisfied, BoundedUpwardEnumerable.init?,
      LawfulUpwardEnumerableLT.lt_iff]
    constructor
    · rintro ⟨n, hn⟩
      simp only [LawfulUpwardEnumerable.succMany?_succ_eq_succ?_bind_succMany?] at hn
      cases h : UpwardEnumerable.succ? l
      · simp [h] at hn
      · exact ⟨_, rfl, n, by simpa [h] using hn⟩
    · rintro ⟨init, hi, n, hn⟩
      exact ⟨n, by simpa [LawfulUpwardEnumerable.succMany?_succ_eq_succ?_bind_succMany?, hi] using hn⟩

instance [LT α] [DecidableLT α] [UpwardEnumerable α] [LawfulUpwardEnumerable α]
    [LawfulUpwardEnumerableLT α] :
    LawfulUpwardEnumerableUpperBound .open α where
  isSatisfied_of_le u a b hub hab := by
    simp only [SupportsUpperBound.IsSatisfied, LawfulUpwardEnumerableLT.lt_iff] at hub ⊢
    exact UpwardEnumerable.lt_of_le_of_lt hab hub

instance [UpwardEnumerable α] [Least? α] [LawfulUpwardEnumerableLeast? α] :
    LawfulUpwardEnumerableLowerBound .unbounded α where
  isSatisfied_iff a l := by
    simpa [SupportsLowerBound.IsSatisfied, BoundedUpwardEnumerable.init?] using
      LawfulUpwardEnumerableLeast?.eq_succMany?_least? a

instance [LE α] [Total (α := α) (· ≤ ·)] [UpwardEnumerable α] [LawfulUpwardEnumerable α]
    [LawfulUpwardEnumerableLE α] :
    LinearlyUpwardEnumerable α where
  eq_of_succ?_eq a b hab := by
    cases Total.total (α := α) (r := (· ≤ ·)) a b <;> rename_i h <;>
      simp only [LawfulUpwardEnumerableLE.le_iff] at h
    · obtain ⟨n, hn⟩ := h
      cases n
      · simpa [UpwardEnumerable.succMany?_zero] using hn
      · exfalso
        rw [LawfulUpwardEnumerable.succMany?_succ_eq_succ?_bind_succMany?, hab,
          ← LawfulUpwardEnumerable.succMany?_succ_eq_succ?_bind_succMany?] at hn
        exact UpwardEnumerable.lt_irrefl ⟨_, hn⟩
    · obtain ⟨n, hn⟩ := h
      cases n
      · simpa [UpwardEnumerable.succMany?_zero] using hn.symm
      · exfalso
        rw [LawfulUpwardEnumerable.succMany?_succ_eq_succ?_bind_succMany?, hab.symm,
          ← LawfulUpwardEnumerable.succMany?_succ_eq_succ?_bind_succMany?] at hn
        exact UpwardEnumerable.lt_irrefl ⟨_, hn⟩

instance [UpwardEnumerable α] : LawfulUpwardEnumerableUpperBound .unbounded α where
  isSatisfied_of_le _ _ _ _ _ := .intro

/--
Creates a `RangeSize .open α` from a `RangeSize .closed α` instance. If the latter is lawful
and certain other conditions hold, then the former is also lawful by
`LawfulRangeSize.open_of_closed`.
-/
@[inline]
abbrev RangeSize.openOfClosed [RangeSize .closed α] : RangeSize .open α where
  size bound a := RangeSize.size (shape := .closed) bound a - 1

attribute [local instance] RangeSize.openOfClosed in
instance LawfulRangeSize.open_of_closed [UpwardEnumerable α] [LE α] [DecidableLE α]
    [LT α] [DecidableLT α] [LawfulOrderLT α] [IsPartialOrder α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α]
    [RangeSize .closed α] [LawfulRangeSize .closed α] :
    LawfulRangeSize .open α where
  size_eq_zero_of_not_isSatisfied bound a h := by
    simp only [SupportsUpperBound.IsSatisfied] at h
    simp only [RangeSize.size]
    by_cases h' : a ≤ bound
    · match hs : UpwardEnumerable.succ? a with
      | none => rw [LawfulRangeSize.size_eq_one_of_succ?_eq_none (h := h') (h' := by omega)]
      | some b =>
        rw [LawfulRangeSize.size_eq_succ_of_succ?_eq_some (h := h') (h' := hs)]
        have : ¬ b ≤ bound := by
          intro hb
          have : a < b := by
            rw [LawfulUpwardEnumerableLT.lt_iff]
            exact ⟨0, by simpa [UpwardEnumerable.succMany?_one] using hs⟩
          exact h (lt_of_lt_of_le this hb)
        rw [LawfulRangeSize.size_eq_zero_of_not_isSatisfied (h := this)]
    · suffices RangeSize.size (shape := .closed) bound a = 0 by omega
      exact LawfulRangeSize.size_eq_zero_of_not_isSatisfied _ _ h'
  size_eq_one_of_succ?_eq_none bound a h h' := by
    exfalso
    simp only [SupportsUpperBound.IsSatisfied, LawfulUpwardEnumerableLT.lt_iff] at h
    obtain ⟨n, hn⟩ := h
    simp [LawfulUpwardEnumerable.succMany?_succ_eq_succ?_bind_succMany?, h'] at hn
  size_eq_succ_of_succ?_eq_some bound a a' h h' := by
    simp only [SupportsUpperBound.IsSatisfied] at h
    simp only [RangeSize.size, Nat.pred_eq_succ_iff]
    rw [LawfulRangeSize.size_eq_succ_of_succ?_eq_some (h := le_of_lt h) (h' := h')]
    rw [← Nat.sub_add_comm]
    · omega
    · simp only [Nat.succ_le_iff, LawfulRangeSize.size_pos_iff_isSatisfied,
        SupportsUpperBound.IsSatisfied]
      rw [LawfulUpwardEnumerableLE.le_iff]
      rw [LawfulUpwardEnumerableLT.lt_iff] at h
      refine ⟨h.choose, ?_⟩
      simpa [LawfulUpwardEnumerable.succMany?_succ_eq_succ?_bind_succMany?, h'] using h.choose_spec

instance LawfulRangeSize.instHasFiniteRanges [UpwardEnumerable α] [LawfulUpwardEnumerable α]
    [RangeSize su α] [SupportsUpperBound su α] [LawfulRangeSize su α] : HasFiniteRanges su α where
  finite init bound := by
    refine ⟨RangeSize.size bound init, ?_⟩
    generalize hn : RangeSize.size bound init = n
    induction n generalizing init with
    | zero =>
      simp only [LawfulRangeSize.size_eq_zero_iff_not_isSatisfied] at hn
      simp [UpwardEnumerable.succMany?_zero, hn]
    | succ =>
      rename_i n ih
      rw [LawfulUpwardEnumerable.succMany?_succ_eq_succ?_bind_succMany?]
      match hs : UpwardEnumerable.succ? init with
      | none => simp
      | some a =>
        simp only [Option.bind_some]
        apply ih
        have : SupportsUpperBound.IsSatisfied bound init :=
          LawfulRangeSize.size_pos_iff_isSatisfied.mp (by omega)
        rw [LawfulRangeSize.size_eq_succ_of_succ?_eq_some (h := this) (h' := hs)] at hn
        omega

end Std.PRange
