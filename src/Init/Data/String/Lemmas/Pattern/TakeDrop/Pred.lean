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
import Init.Data.String.Lemmas.FindPos
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

theorem eq_append_of_dropPrefix?_bool_eq_some {p : Char → Bool} {s res : Slice} (h : s.dropPrefix? p = some res) :
    ∃ c, s.copy = singleton c ++ res.copy ∧ p c = true := by
  obtain ⟨_, ⟨c, ⟨rfl, h₁⟩⟩, h₂⟩ := by simpa [PatternModel.Matches] using Pattern.Model.eq_append_of_dropPrefix?_eq_some h
  exact ⟨_, h₂, h₁⟩

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

theorem eq_append_of_dropPrefix?_prop_eq_some {P : Char → Prop} [DecidablePred P] {s res : Slice} (h : s.dropPrefix? P = some res) :
    ∃ c, s.copy = singleton c ++ res.copy ∧ P c := by
  rw [dropPrefix?_prop_eq_dropPrefix?_decide] at h
  simpa using eq_append_of_dropPrefix?_bool_eq_some h

theorem skipSuffix?_bool_eq_some_iff {p : Char → Bool} {s : Slice} {pos : s.Pos} :
    s.skipSuffix? p = some pos ↔ ∃ h, pos = s.endPos.prev h ∧ p ((s.endPos.prev h).get (by simp)) = true := by
  rw [Pattern.Model.skipSuffix?_eq_some_iff, CharPred.isLongestRevMatch_iff]

theorem endsWith_bool_iff_get {p : Char → Bool} {s : Slice} :
    s.endsWith p ↔ ∃ h, p ((s.endPos.prev h).get (by simp)) = true := by
  simp [Pattern.Model.endsWith_iff, CharPred.revMatchesAt_iff]

theorem endsWith_bool_eq_false_iff_get {p : Char → Bool} {s : Slice} :
    s.endsWith p = false ↔ ∀ h, p ((s.endPos.prev h).get (by simp)) = false := by
  simp [Pattern.Model.endsWith_eq_false_iff, CharPred.revMatchesAt_iff]

theorem endsWith_bool_eq_getLast? {p : Char → Bool} {s : Slice} :
    s.endsWith p = s.copy.toList.getLast?.any p := by
  rw [Bool.eq_iff_iff, Pattern.Model.endsWith_iff, CharPred.revMatchesAt_iff]
  by_cases h : s.endPos = s.startPos
  · refine ⟨fun ⟨h', _⟩ => by simp_all, ?_⟩
    have : s.copy = "" := by simp_all [Slice.startPos_eq_endPos_iff.mp h.symm]
    simp [this]
  · obtain ⟨t, ht⟩ := s.splits_endPos.exists_eq_append_singleton_of_ne_startPos h
    simp [h, ht]

theorem eq_append_of_dropSuffix?_bool_eq_some {p : Char → Bool} {s res : Slice} (h : s.dropSuffix? p = some res) :
    ∃ c, s.copy = res.copy ++ singleton c ∧ p c = true := by
  obtain ⟨_, ⟨c, ⟨rfl, h₁⟩⟩, h₂⟩ := by simpa [PatternModel.Matches] using Pattern.Model.eq_append_of_dropSuffix?_eq_some h
  exact ⟨_, h₂, h₁⟩

theorem skipSuffix?_prop_eq_some_iff {P : Char → Prop} [DecidablePred P] {s : Slice} {pos : s.Pos} :
    s.skipSuffix? P = some pos ↔ ∃ h, pos = s.endPos.prev h ∧ P ((s.endPos.prev h).get (by simp)) := by
  simp [skipSuffix?_prop_eq_skipSuffix?_decide, skipSuffix?_bool_eq_some_iff]

theorem endsWith_prop_iff_get {P : Char → Prop} [DecidablePred P] {s : Slice} :
    s.endsWith P ↔ ∃ h, P ((s.endPos.prev h).get (by simp)) := by
  simp [endsWith_prop_eq_endsWith_decide, endsWith_bool_iff_get]

theorem endsWith_prop_eq_false_iff_get {P : Char → Prop} [DecidablePred P] {s : Slice} :
    s.endsWith P = false ↔ ∀ h, ¬ P ((s.endPos.prev h).get (by simp)) := by
  simp [endsWith_prop_eq_endsWith_decide, endsWith_bool_eq_false_iff_get]

theorem endsWith_prop_eq_getLast? {P : Char → Prop} [DecidablePred P] {s : Slice} :
    s.endsWith P = s.copy.toList.getLast?.any (decide <| P ·) := by
  simp [endsWith_prop_eq_endsWith_decide, endsWith_bool_eq_getLast?]

theorem eq_append_of_dropSuffix?_prop_eq_some {P : Char → Prop} [DecidablePred P] {s res : Slice} (h : s.dropSuffix? P = some res) :
    ∃ c, s.copy = res.copy ++ singleton c ∧ P c := by
  rw [dropSuffix?_prop_eq_dropSuffix?_decide] at h
  simpa using eq_append_of_dropSuffix?_bool_eq_some h

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

theorem eq_append_of_dropPrefix?_bool_eq_some {p : Char → Bool} {s : String} {res : Slice} (h : s.dropPrefix? p = some res) :
    ∃ c, s = singleton c ++ res.copy ∧ p c = true := by
  rw [dropPrefix?_eq_dropPrefix?_toSlice] at h
  simpa using Slice.eq_append_of_dropPrefix?_bool_eq_some h

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

theorem eq_append_of_dropPrefix?_prop_eq_some {P : Char → Prop} [DecidablePred P] {s : String} {res : Slice}
    (h : s.dropPrefix? P = some res) : ∃ c, s = singleton c ++ res.copy ∧ P c := by
  rw [dropPrefix?_eq_dropPrefix?_toSlice] at h
  simpa using Slice.eq_append_of_dropPrefix?_prop_eq_some h

theorem skipSuffix?_bool_eq_some_iff {p : Char → Bool} {s : String} {pos : s.Pos} :
    s.skipSuffix? p = some pos ↔ ∃ h, pos = s.endPos.prev h ∧ p ((s.endPos.prev h).get (by simp)) = true := by
  simp [skipSuffix?_eq_skipSuffix?_toSlice, Slice.skipSuffix?_bool_eq_some_iff, ← Pos.toSlice_inj,
    Pos.prev_toSlice]

theorem endsWith_bool_iff_get {p : Char → Bool} {s : String} :
    s.endsWith p ↔ ∃ h, p ((s.endPos.prev h).get (by simp)) = true := by
  simp [endsWith_eq_endsWith_toSlice, Slice.endsWith_bool_iff_get, Pos.prev_toSlice]

theorem endsWith_bool_eq_false_iff_get {p : Char → Bool} {s : String} :
    s.endsWith p = false ↔ ∀ h, p ((s.endPos.prev h).get (by simp)) = false := by
  simp [endsWith_eq_endsWith_toSlice, Slice.endsWith_bool_eq_false_iff_get, Pos.prev_toSlice]

theorem endsWith_bool_eq_getLast? {p : Char → Bool} {s : String} :
    s.endsWith p = s.toList.getLast?.any p := by
  simp [endsWith_eq_endsWith_toSlice, Slice.endsWith_bool_eq_getLast?]

theorem eq_append_of_dropSuffix?_bool_eq_some {p : Char → Bool} {s : String} {res : Slice} (h : s.dropSuffix? p = some res) :
    ∃ c, s = res.copy ++ singleton c ∧ p c = true := by
  rw [dropSuffix?_eq_dropSuffix?_toSlice] at h
  simpa using Slice.eq_append_of_dropSuffix?_bool_eq_some h

theorem skipSuffix?_prop_eq_some_iff {P : Char → Prop} [DecidablePred P] {s : String} {pos : s.Pos} :
    s.skipSuffix? P = some pos ↔ ∃ h, pos = s.endPos.prev h ∧ P ((s.endPos.prev h).get (by simp)) := by
  simp [skipSuffix?_eq_skipSuffix?_toSlice, Slice.skipSuffix?_prop_eq_some_iff, ← Pos.toSlice_inj,
    Pos.prev_toSlice]

theorem endsWith_prop_iff_get {P : Char → Prop} [DecidablePred P] {s : String} :
    s.endsWith P ↔ ∃ h, P ((s.endPos.prev h).get (by simp)) := by
  simp [endsWith_eq_endsWith_toSlice, Slice.endsWith_prop_iff_get, Pos.prev_toSlice]

theorem endsWith_prop_eq_false_iff_get {P : Char → Prop} [DecidablePred P] {s : String} :
    s.endsWith P = false ↔ ∀ h, ¬ P ((s.endPos.prev h).get (by simp)) := by
  simp [endsWith_eq_endsWith_toSlice, Slice.endsWith_prop_eq_false_iff_get, Pos.prev_toSlice]

theorem endsWith_prop_eq_getLast? {P : Char → Prop} [DecidablePred P] {s : String} :
    s.endsWith P = s.toList.getLast?.any (decide <| P ·) := by
  simp [endsWith_eq_endsWith_toSlice, Slice.endsWith_prop_eq_getLast?]

theorem eq_append_of_dropSuffix?_prop_eq_some {P : Char → Prop} [DecidablePred P] {s : String} {res : Slice}
    (h : s.dropSuffix? P = some res) : ∃ c, s = res.copy ++ singleton c ∧ P c := by
  rw [dropSuffix?_eq_dropSuffix?_toSlice] at h
  simpa using Slice.eq_append_of_dropSuffix?_prop_eq_some h

end String
