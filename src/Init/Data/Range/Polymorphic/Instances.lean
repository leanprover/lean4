/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Range.Polymorphic.Basic
public import Init.Data.Order.Classes

open Std PRange

public section

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
    simp [SupportsLowerBound.IsSatisfied, BoundedUpwardEnumerable.init?,
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
