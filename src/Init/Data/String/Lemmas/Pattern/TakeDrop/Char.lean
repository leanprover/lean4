/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Markus Himmel
-/
module

prelude
public import Init.Data.String.Slice
public import Init.Data.String.TakeDrop
import Init.Data.String.Lemmas.Pattern.TakeDrop.Basic
import Init.Data.String.Lemmas.Pattern.Char
import Init.Data.Option.Lemmas

public section

open String.Slice Pattern Model

namespace String

namespace Slice

theorem skipPrefix?_char_eq_some_iff {c : Char} {s : Slice} {pos : s.Pos} :
    s.skipPrefix? c = some pos ↔ ∃ h, pos = s.startPos.next h ∧ s.startPos.get h = c := by
  rw [Pattern.Model.skipPrefix?_eq_some_iff, Char.isLongestMatch_iff]

theorem startsWith_char_iff_get {c : Char} {s : Slice} :
    s.startsWith c ↔ ∃ h, s.startPos.get h = c := by
  simp [Pattern.Model.startsWith_iff, Char.matchesAt_iff]

theorem startsWith_char_eq_false_iff_get {c : Char} {s : Slice} :
    s.startsWith c = false ↔ ∀ h, s.startPos.get h ≠ c := by
  simp [Pattern.Model.startsWith_eq_false_iff, Char.matchesAt_iff]

theorem startsWith_char_eq_head? {c : Char} {s : Slice} :
    s.startsWith c = (s.copy.toList.head? == some c) := by
  rw [Bool.eq_iff_iff, Pattern.Model.startsWith_iff, Char.matchesAt_iff_splits]
  simp only [splits_startPos_iff, exists_and_left, exists_eq_left, beq_iff_eq]
  refine ⟨fun ⟨t, ht⟩ => by simp [← ht], fun h => ?_⟩
  simp only [← toList_inj, toList_append, toList_singleton, List.cons_append, List.nil_append]
  cases h : s.copy.toList <;> simp_all [← ofList_inj]

end Slice

theorem skipPrefix?_char_eq_some_iff {c : Char} {s : String} {pos : s.Pos} :
    s.skipPrefix? c = some pos ↔ ∃ h, pos = s.startPos.next h ∧ s.startPos.get h = c := by
  simp [skipPrefix?_eq_skipPrefix?_toSlice, Slice.skipPrefix?_char_eq_some_iff, ← Pos.toSlice_inj,
    Pos.toSlice_next]

theorem startsWith_char_iff_get {c : Char} {s : String} :
    s.startsWith c ↔ ∃ h, s.startPos.get h = c := by
  simp [startsWith_eq_startsWith_toSlice, Slice.startsWith_char_iff_get]

theorem startsWith_char_eq_false_iff_get {c : Char} {s : String} :
    s.startsWith c = false ↔ ∀ h, s.startPos.get h ≠ c := by
  simp [startsWith_eq_startsWith_toSlice, Slice.startsWith_char_eq_false_iff_get]

theorem startsWith_char_eq_head? {c : Char} {s : String} :
    s.startsWith c = (s.toList.head? == some c) := by
  simp [startsWith_eq_startsWith_toSlice, Slice.startsWith_char_eq_head?]

end String
