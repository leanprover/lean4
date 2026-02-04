/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Range.Polymorphic.Basic
import Init.Data.Nat.Lemmas
import Init.Data.Order.Lemmas
import Init.ByCases
import Init.Data.Int.Lemmas
import Init.Data.Int.Order
import Init.Data.Option.Lemmas
import Init.Omega

/-!
This module provides instances that reduce the amount of code necessary to make a type compatible
with the polymorphic ranges. For an example of the required work, take a look at
`Init.Data.Range.Polymorphic.Nat`.
-/

set_option doc.verso true

public section

namespace Std
open PRange

instance [LE α] [LT α] [UpwardEnumerable α] [LawfulUpwardEnumerable α]
    [LawfulUpwardEnumerableLE α] [LawfulOrderLT α] : LawfulUpwardEnumerableLT α where
  lt_iff a b := by
    simp only [LawfulOrderLT.lt_iff, UpwardEnumerable.le_iff]
    constructor
    · intro h
      obtain ⟨n, hn⟩ := h.1
      cases n
      · apply h.2.elim
        refine ⟨0, ?_⟩
        simpa [succMany?_zero] using hn.symm
      exact ⟨_, hn⟩
    · intro h
      constructor
      · match h with | ⟨_, hn⟩ => exact ⟨_, hn⟩
      · exact UpwardEnumerable.not_ge_of_lt h

instance [LE α] [Total (α := α) (· ≤ ·)] [UpwardEnumerable α] [LawfulUpwardEnumerable α]
    [LawfulUpwardEnumerableLE α] :
    LinearlyUpwardEnumerable α where
  eq_of_succ?_eq a b hab := by
    cases Total.total (α := α) (r := (· ≤ ·)) a b <;> rename_i h <;>
      simp only [UpwardEnumerable.le_iff] at h
    · obtain ⟨n, hn⟩ := h
      cases n
      · simpa [succMany?_zero] using hn
      · exfalso
        rw [succMany?_add_one_eq_succ?_bind_succMany?, hab,
          ← succMany?_add_one_eq_succ?_bind_succMany?] at hn
        exact UpwardEnumerable.lt_irrefl ⟨_, hn⟩
    · obtain ⟨n, hn⟩ := h
      cases n
      · simpa [succMany?_zero] using hn.symm
      · exfalso
        rw [succMany?_add_one_eq_succ?_bind_succMany?, hab.symm,
          ← succMany?_add_one_eq_succ?_bind_succMany?] at hn
        exact UpwardEnumerable.lt_irrefl ⟨_, hn⟩

namespace Rxc

instance instIsAlwaysFiniteOfLawfulHasSize [LE α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [HasSize α] [LawfulHasSize α] :
    IsAlwaysFinite α where
  finite lo hi := by
    refine ⟨HasSize.size lo hi, ?_⟩
    generalize hn : HasSize.size lo hi = n
    induction n generalizing lo with
    | zero =>
      simp only [size_eq_zero_iff_not_le] at hn
      simp [succMany?_zero, hn]
    | succ =>
      rename_i n ih
      rw [succMany?_add_one_eq_succ?_bind_succMany?]
      match hs : succ? lo with
      | none => simp
      | some a =>
        simp only [Option.bind_some]
        apply ih
        have : lo ≤ hi := size_pos_iff_le.mp (by omega)
        rw [LawfulHasSize.size_eq_succ_of_succ?_eq_some (h := this) (h' := hs)] at hn
        omega

end Rxc

namespace Rxo

@[inline]
abbrev HasSize.ofClosed [Rxc.HasSize α] : HasSize α where
  size lo hi := Rxc.HasSize.size lo hi - 1

attribute [local instance] HasSize.ofClosed in
instance LawfulHasSize.of_closed [UpwardEnumerable α] [LE α] [DecidableLE α]
    [LT α] [DecidableLT α] [LawfulOrderLT α] [IsPartialOrder α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α]
    [Rxc.HasSize α] [Rxc.LawfulHasSize α] :
    LawfulHasSize α where
  size_eq_zero_of_not_le lo hi h := by
    simp only [HasSize.size]
    by_cases h' : lo ≤ hi
    · match hs : succ? lo with
      | none => rw [Rxc.LawfulHasSize.size_eq_one_of_succ?_eq_none (h := h') (h' := by omega)]
      | some b =>
        rw [Rxc.LawfulHasSize.size_eq_succ_of_succ?_eq_some (h := h') (h' := hs)]
        have : ¬ b ≤ hi := by
          intro hb
          have : lo < b := by
            rw [UpwardEnumerable.lt_iff]
            exact ⟨0, by simpa [succMany?_one] using hs⟩
          exact h (lt_of_lt_of_le this hb)
        rw [Rxc.LawfulHasSize.size_eq_zero_of_not_le (h := this)]
    · suffices Rxc.HasSize.size lo hi = 0 by omega
      exact Rxc.LawfulHasSize.size_eq_zero_of_not_le _ _ h'
  size_eq_one_of_succ?_eq_none bound a h h' := by
    exfalso
    simp only [UpwardEnumerable.lt_iff] at h
    obtain ⟨n, hn⟩ := h
    simp [succMany?_add_one_eq_succ?_bind_succMany?, h'] at hn
  size_eq_succ_of_succ?_eq_some bound a a' h h' := by
    simp only [HasSize.size, Nat.pred_eq_succ_iff]
    rw [Rxc.LawfulHasSize.size_eq_succ_of_succ?_eq_some (h := le_of_lt h) (h' := h')]
    rw [← Nat.sub_add_comm]
    · omega
    · simp only [Nat.succ_le_iff, Rxc.size_pos_iff_le]
      rw [UpwardEnumerable.le_iff]
      rw [UpwardEnumerable.lt_iff] at h
      refine ⟨h.choose, ?_⟩
      simpa [succMany?_add_one_eq_succ?_bind_succMany?, h'] using h.choose_spec

/--
Creates a {lean}`HasSize α` from a {lean}`HasSize α` instance. If the latter is lawful
and certain other conditions hold, then the former is also lawful by
{name}`Rxo.LawfulHasSize.of_closed`.
-/
add_decl_doc HasSize.ofClosed

instance instIsAlwaysFiniteOfLawfulHasSize [LT α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [HasSize α] [LawfulHasSize α] :
    IsAlwaysFinite α where
  finite lo hi := by
    refine ⟨HasSize.size lo hi, ?_⟩
    generalize hn : HasSize.size lo hi = n
    induction n generalizing lo with
    | zero =>
      simp only [size_eq_zero_iff_not_le] at hn
      simp [succMany?_zero, hn]
    | succ =>
      rename_i n ih
      rw [succMany?_add_one_eq_succ?_bind_succMany?]
      match hs : succ? lo with
      | none => simp
      | some a =>
        simp only [Option.bind_some]
        apply ih
        have : lo < hi := size_pos_iff_lt.mp (by omega)
        rw [LawfulHasSize.size_eq_succ_of_succ?_eq_some (h := this) (h' := hs)] at hn
        omega

end Rxo

namespace Rxi

instance instIsAlwaysFiniteOfLawfulHasSize [LT α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [HasSize α] [LawfulHasSize α] :
    IsAlwaysFinite α where
  finite lo := by
    refine ⟨HasSize.size lo, ?_⟩
    generalize hn : HasSize.size lo = n
    induction n generalizing lo with
    | zero =>
      simp [Nat.ne_of_gt size_pos] at hn
    | succ =>
      rename_i n ih
      rw [succMany?_add_one_eq_succ?_bind_succMany?]
      match hs : succ? lo with
      | none => simp
      | some a =>
        simp only [Option.bind_some]
        apply ih
        rw [LawfulHasSize.size_eq_succ_of_succ?_eq_some (h := hs)] at hn
        omega

end Rxi

end Std
