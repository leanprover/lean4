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
import Init.Data.String.Lemmas.Pattern.Pred
import Init.Data.Option.Lemmas
import Init.ByCases

public section

open String.Slice Pattern Model

namespace String

namespace Slice

theorem skipPrefix?_bool_eq_some_iff {p : Char → Bool} {s : Slice} {pos : s.Pos} :
    s.skipPrefix? p = some pos ↔ ∃ h, pos = s.startPos.next h ∧ p (s.startPos.get h) = true := by
  rw [Pattern.Model.skipPrefix?_eq_some_iff, CharPred.isLongestMatch_iff]

theorem startsWith_bool_iff_get {p : Char → Bool} {s : Slice} :
    s.startsWith p ↔ ∃ h, p (s.startPos.get h) = true := by
  simp [Pattern.Model.startsWith_iff, CharPred.matchesAt_iff]

theorem startsWith_bool_eq_false_iff_get {p : Char → Bool} {s : Slice} :
    s.startsWith p = false ↔ ∀ h, p (s.startPos.get h) = false := by
  simp [Pattern.Model.startsWith_eq_false_iff, CharPred.matchesAt_iff]

theorem startsWith_bool_eq_head? {p : Char → Bool} {s : Slice} :
    s.startsWith p = s.copy.toList.head?.any p := by
  rw [Bool.eq_iff_iff, Pattern.Model.startsWith_iff, CharPred.matchesAt_iff]
  by_cases h : s.startPos = s.endPos
  · refine ⟨fun ⟨h', _⟩ => by simp_all, ?_⟩
    have : s.copy = "" := by simp_all [Slice.startPos_eq_endPos_iff]
    simp [this]
  · obtain ⟨t, ht⟩ := s.splits_startPos.exists_eq_singleton_append h
    simp [h, ht]

theorem skipPrefix?_prop_eq_some_iff {P : Char → Prop} [DecidablePred P] {s : Slice} {pos : s.Pos} :
    s.skipPrefix? P = some pos ↔ ∃ h, pos = s.startPos.next h ∧ P (s.startPos.get h) := by
  simp [skipPrefix?_prop_eq_skipPrefix?_decide, skipPrefix?_bool_eq_some_iff]

theorem startsWith_prop_iff_get {P : Char → Prop} [DecidablePred P] {s : Slice} :
    s.startsWith P ↔ ∃ h, P (s.startPos.get h) := by
  simp [startsWith_prop_eq_startsWith_decide, startsWith_bool_iff_get]

theorem startsWith_prop_eq_false_iff_get {P : Char → Prop} [DecidablePred P] {s : Slice} :
    s.startsWith P = false ↔ ∀ h, ¬ P (s.startPos.get h) := by
  simp [startsWith_prop_eq_startsWith_decide, startsWith_bool_eq_false_iff_get]

theorem startsWith_prop_eq_head? {P : Char → Prop} [DecidablePred P] {s : Slice} :
    s.startsWith P = s.copy.toList.head?.any (decide <| P ·) := by
  simp [startsWith_prop_eq_startsWith_decide, startsWith_bool_eq_head?]

end Slice

theorem skipPrefix?_bool_eq_some_iff {p : Char → Bool} {s : String} {pos : s.Pos} :
    s.skipPrefix? p = some pos ↔ ∃ h, pos = s.startPos.next h ∧ p (s.startPos.get h) = true := by
  simp [skipPrefix?_eq_skipPrefix?_toSlice, Slice.skipPrefix?_bool_eq_some_iff, ← Pos.toSlice_inj,
    Pos.toSlice_next]

theorem startsWith_bool_iff_get {p : Char → Bool} {s : String} :
    s.startsWith p ↔ ∃ h, p (s.startPos.get h) = true := by
  simp [startsWith_eq_startsWith_toSlice, Slice.startsWith_bool_iff_get]

theorem startsWith_bool_eq_false_iff_get {p : Char → Bool} {s : String} :
    s.startsWith p = false ↔ ∀ h, p (s.startPos.get h) = false := by
  simp [startsWith_eq_startsWith_toSlice, Slice.startsWith_bool_eq_false_iff_get]

theorem startsWith_bool_eq_head? {p : Char → Bool} {s : String} :
    s.startsWith p = s.toList.head?.any p := by
  simp [startsWith_eq_startsWith_toSlice, Slice.startsWith_bool_eq_head?]

theorem skipPrefix?_prop_eq_some_iff {P : Char → Prop} [DecidablePred P] {s : String} {pos : s.Pos} :
    s.skipPrefix? P = some pos ↔ ∃ h, pos = s.startPos.next h ∧ P (s.startPos.get h) := by
  simp [skipPrefix?_eq_skipPrefix?_toSlice, Slice.skipPrefix?_prop_eq_some_iff, ← Pos.toSlice_inj,
    Pos.toSlice_next]

theorem startsWith_prop_iff_get {P : Char → Prop} [DecidablePred P] {s : String} :
    s.startsWith P ↔ ∃ h, P (s.startPos.get h) := by
  simp [startsWith_eq_startsWith_toSlice, Slice.startsWith_prop_iff_get]

theorem startsWith_prop_eq_false_iff_get {P : Char → Prop} [DecidablePred P] {s : String} :
    s.startsWith P = false ↔ ∀ h, ¬ P (s.startPos.get h) := by
  simp [startsWith_eq_startsWith_toSlice, Slice.startsWith_prop_eq_false_iff_get]

theorem startsWith_prop_eq_head? {P : Char → Prop} [DecidablePred P] {s : String} :
    s.startsWith P = s.toList.head?.any (decide <| P ·) := by
  simp [startsWith_eq_startsWith_toSlice, Slice.startsWith_prop_eq_head?]

end String
