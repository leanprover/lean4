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
import Init.Data.String.Lemmas.FindPos
import Init.Data.List.Sublist

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

theorem startsWith_char_iff_exists_append {c : Char} {s : Slice} :
    s.startsWith c ↔ ∃ t, s.copy = singleton c ++ t := by
  simp only [startsWith_char_eq_head?, beq_iff_eq, List.head?_eq_some_iff, ← toList_inj,
    toList_append, toList_singleton, List.cons_append, List.nil_append]
  exact ⟨fun ⟨t, ht⟩ => ⟨ofList t, by simp [ht]⟩, fun ⟨t, ht⟩ => ⟨t.toList, by simp [ht]⟩⟩

theorem startsWith_char_eq_false_iff_forall_append {c : Char} {s : Slice} :
    s.startsWith c = false ↔ ∀ t, s.copy ≠ singleton c ++ t := by
  simp [← Bool.not_eq_true, startsWith_char_iff_exists_append]

theorem eq_append_of_dropPrefix?_char_eq_some {c : Char} {s res : Slice} (h : s.dropPrefix? c = some res) :
    s.copy = singleton c ++ res.copy := by
  simpa [PatternModel.Matches] using Pattern.Model.eq_append_of_dropPrefix?_eq_some h

theorem Pos.skip?_char_eq_some_iff {c : Char} {s : Slice} {pos res : s.Pos} :
    pos.skip? c = some res ↔ ∃ h, res = pos.next h ∧ pos.get h = c := by
  simp [Pattern.Model.Pos.skip?_eq_some_iff, Char.isLongestMatchAt_iff]

@[simp]
theorem Pos.skip?_char_eq_none_iff {c : Char} {s : Slice} {pos : s.Pos} :
    pos.skip? c = none ↔ ∀ h, pos.get h ≠ c := by
  simp [Pattern.Model.Pos.skip?_eq_none_iff, Char.matchesAt_iff]

theorem Pos.get_skipWhile_char_ne {c : Char} {s : Slice} {pos : s.Pos} {h} :
    (pos.skipWhile c).get h ≠ c := by
  have := Pattern.Model.Pos.not_matchesAt_skipWhile c pos
  simp_all [Char.matchesAt_iff]

theorem Pos.skipWhile_char_eq_self_iff_get {c : Char} {s : Slice} {pos : s.Pos} :
    pos.skipWhile c = pos ↔ ∀ h, pos.get h ≠ c := by
  simp [Pattern.Model.Pos.skipWhile_eq_self_iff, Char.matchesAt_iff]

theorem Pos.get_eq_of_lt_skipWhile_char {c : Char} {s : Slice} {pos pos' : s.Pos}
    (h₁ : pos ≤ pos') (h₂ : pos' < pos.skipWhile c) : pos'.get (ne_endPos_of_lt h₂) = c :=
  (Char.isLongestMatchAtChain_iff.1 (Pattern.Model.Pos.isLongestMatchAtChain_skipWhile c pos)).2 _ h₁ h₂

theorem get_skipPrefixWhile_char_ne {c : Char} {s : Slice} {h} :
    (s.skipPrefixWhile c).get h ≠ c := by
  simp [skipPrefixWhile_eq_skipWhile_startPos, Pos.get_skipWhile_char_ne]

theorem get_eq_of_lt_skipPrefixWhile_char {c : Char} {s : Slice} {pos : s.Pos} (h : pos < s.skipPrefixWhile c) :
    pos.get (Pos.ne_endPos_of_lt h) = c :=
  Pos.get_eq_of_lt_skipWhile_char (Pos.startPos_le _) (by rwa [skipPrefixWhile_eq_skipWhile_startPos] at h)

@[simp]
theorem all_char_iff {c : Char} {s : Slice} : s.all c ↔ s.copy.toList = List.replicate s.copy.length c := by
  rw [Bool.eq_iff_iff]
  simp [Pattern.Model.all_eq_true_iff, Char.isLongestMatchAtChain_startPos_endPos_iff_toList]

theorem Pos.revSkip?_char_eq_some_iff {c : Char} {s : Slice} {pos res : s.Pos} :
    pos.revSkip? c = some res ↔ ∃ h, res = pos.prev h ∧ (pos.prev h).get (by simp) = c := by
  simp [Pattern.Model.Pos.revSkip?_eq_some_iff, Char.isLongestRevMatchAt_iff]

@[simp]
theorem Pos.revSkip?_char_eq_none_iff {c : Char} {s : Slice} {pos : s.Pos} :
    pos.revSkip? c = none ↔ ∀ h, (pos.prev h).get (by simp) ≠ c := by
  simp [Pattern.Model.Pos.revSkip?_eq_none_iff, Char.revMatchesAt_iff]

theorem Pos.get_revSkipWhile_char_ne {c : Char} {s : Slice} {pos : s.Pos} {h} :
    ((pos.revSkipWhile c).prev h).get (by simp) ≠ c := by
  have := Pattern.Model.Pos.not_revMatchesAt_revSkipWhile c pos
  simp_all [Char.revMatchesAt_iff]

theorem Pos.revSkipWhile_char_eq_self_iff_get {c : Char} {s : Slice} {pos : s.Pos} :
    pos.revSkipWhile c = pos ↔ ∀ h, (pos.prev h).get (by simp) ≠ c := by
  simp [Pattern.Model.Pos.revSkipWhile_eq_self_iff, Char.revMatchesAt_iff]

theorem Pos.get_eq_of_revSkipWhile_le_char {c : Char} {s : Slice} {pos pos' : s.Pos}
    (h₁ : pos' < pos) (h₂ : pos.revSkipWhile c ≤ pos') : pos'.get (Pos.ne_endPos_of_lt h₁) = c :=
  (Char.isLongestRevMatchAtChain_iff.1 (Pattern.Model.Pos.isLongestRevMatchAtChain_revSkipWhile c pos)).2 _ h₂ h₁

theorem get_skipSuffixWhile_char_ne {c : Char} {s : Slice} {h} :
    ((s.skipSuffixWhile c).prev h).get (by simp) ≠ c := by
  simp [skipSuffixWhile_eq_revSkipWhile_endPos, Pos.get_revSkipWhile_char_ne]

theorem get_eq_of_skipSuffixWhile_le_char {c : Char} {s : Slice} {pos : s.Pos}
    (h : s.skipSuffixWhile c ≤ pos) (h' : pos < s.endPos) :
    pos.get (Pos.ne_endPos_of_lt h') = c :=
  Pos.get_eq_of_revSkipWhile_le_char h' (by rwa [skipSuffixWhile_eq_revSkipWhile_endPos] at h)

@[simp]
theorem revAll_char_iff {c : Char} {s : Slice} : s.revAll c ↔ s.copy.toList = List.replicate s.copy.length c := by
  rw [Bool.eq_iff_iff]
  simp [Pattern.Model.revAll_eq_true_iff, Char.isLongestRevMatchAtChain_startPos_endPos_iff_toList]

theorem skipSuffix?_char_eq_some_iff {c : Char} {s : Slice} {pos : s.Pos} :
    s.skipSuffix? c = some pos ↔ ∃ h, pos = s.endPos.prev h ∧ (s.endPos.prev h).get (by simp) = c := by
  rw [Pattern.Model.skipSuffix?_eq_some_iff, Char.isLongestRevMatch_iff]

theorem endsWith_char_iff_get {c : Char} {s : Slice} :
    s.endsWith c ↔ ∃ h, (s.endPos.prev h).get (by simp) = c := by
  simp [Pattern.Model.endsWith_iff, Char.revMatchesAt_iff]

theorem endsWith_char_eq_false_iff_get {c : Char} {s : Slice} :
    s.endsWith c = false ↔ ∀ h, (s.endPos.prev h).get (by simp) ≠ c := by
  simp [Pattern.Model.endsWith_eq_false_iff, Char.revMatchesAt_iff]

theorem endsWith_char_iff_exists_append {c : Char} {s : Slice} :
    s.endsWith c ↔ ∃ t, s.copy = t ++ singleton c := by
  rw [Pattern.Model.endsWith_iff, Char.revMatchesAt_iff_splits]
  simp only [splits_endPos_iff, exists_eq_right, eq_comm (a := s.copy)]

theorem endsWith_char_eq_getLast? {c : Char} {s : Slice} :
    s.endsWith c = (s.copy.toList.getLast? == some c) := by
  rw [Bool.eq_iff_iff, endsWith_char_iff_exists_append, beq_iff_eq,
    ← List.singleton_suffix_iff_getLast?_eq_some, List.suffix_iff_exists_eq_append]
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨t.toList, by rw [ht, toList_append, toList_singleton]⟩
  · rintro ⟨l, hl⟩
    exact ⟨ofList l, by rw [← toList_inj, toList_append, toList_singleton, toList_ofList]; exact hl⟩

theorem endsWith_char_eq_false_iff_forall_append {c : Char} {s : Slice} :
    s.endsWith c = false ↔ ∀ t, s.copy ≠ t ++ singleton c := by
  simp [← Bool.not_eq_true, endsWith_char_iff_exists_append]

theorem eq_append_of_dropSuffix?_char_eq_some {c : Char} {s res : Slice} (h : s.dropSuffix? c = some res) :
    s.copy = res.copy ++ singleton c := by
  simpa [PatternModel.Matches] using Pattern.Model.eq_append_of_dropSuffix?_eq_some h

end Slice

theorem skipPrefix?_char_eq_some_iff {c : Char} {s : String} {pos : s.Pos} :
    s.skipPrefix? c = some pos ↔ ∃ h, pos = s.startPos.next h ∧ s.startPos.get h = c := by
  simp [skipPrefix?_eq_skipPrefix?_toSlice, Slice.skipPrefix?_char_eq_some_iff, ← Pos.toSlice_inj,
    Pos.toSlice_next]

theorem startsWith_char_iff_get {c : Char} {s : String} :
    s.startsWith c ↔ ∃ h, s.startPos.get h = c := by
  simp [← startsWith_toSlice, Slice.startsWith_char_iff_get]

theorem startsWith_char_eq_false_iff_get {c : Char} {s : String} :
    s.startsWith c = false ↔ ∀ h, s.startPos.get h ≠ c := by
  simp [← startsWith_toSlice, Slice.startsWith_char_eq_false_iff_get]

theorem startsWith_char_eq_head? {c : Char} {s : String} :
    s.startsWith c = (s.toList.head? == some c) := by
  simp [← startsWith_toSlice, Slice.startsWith_char_eq_head?]

theorem startsWith_char_iff_exists_append {c : Char} {s : String} :
    s.startsWith c ↔ ∃ t, s = singleton c ++ t := by
  simp [← startsWith_toSlice, Slice.startsWith_char_iff_exists_append]

theorem startsWith_char_eq_false_iff_forall_append {c : Char} {s : String} :
    s.startsWith c = false ↔ ∀ t, s ≠ singleton c ++ t := by
  simp [← Bool.not_eq_true, startsWith_char_iff_exists_append]

theorem eq_append_of_dropPrefix?_char_eq_some {c : Char} {s : String} {res : Slice} (h : s.dropPrefix? c = some res) :
    s = singleton c ++ res.copy := by
  rw [dropPrefix?_eq_dropPrefix?_toSlice] at h
  simpa using Slice.eq_append_of_dropPrefix?_char_eq_some h

theorem skipSuffix?_char_eq_some_iff {c : Char} {s : String} {pos : s.Pos} :
    s.skipSuffix? c = some pos ↔ ∃ h, pos = s.endPos.prev h ∧ (s.endPos.prev h).get (by simp) = c := by
  simp [skipSuffix?_eq_skipSuffix?_toSlice, Slice.skipSuffix?_char_eq_some_iff, ← Pos.toSlice_inj,
    Pos.prev_toSlice]

theorem endsWith_char_iff_get {c : Char} {s : String} :
    s.endsWith c ↔ ∃ h, (s.endPos.prev h).get (by simp) = c := by
  simp [← endsWith_toSlice, Slice.endsWith_char_iff_get, Pos.prev_toSlice]

theorem endsWith_char_eq_false_iff_get {c : Char} {s : String} :
    s.endsWith c = false ↔ ∀ h, (s.endPos.prev h).get (by simp) ≠ c := by
  simp [← endsWith_toSlice, Slice.endsWith_char_eq_false_iff_get, Pos.prev_toSlice]

theorem endsWith_char_eq_getLast? {c : Char} {s : String} :
    s.endsWith c = (s.toList.getLast? == some c) := by
  simp [← endsWith_toSlice, Slice.endsWith_char_eq_getLast?]

theorem endsWith_char_iff_exists_append {c : Char} {s : String} :
    s.endsWith c ↔ ∃ t, s = t ++ singleton c := by
  simp [← endsWith_toSlice, Slice.endsWith_char_iff_exists_append]

theorem endsWith_char_eq_false_iff_forall_append {c : Char} {s : String} :
    s.endsWith c = false ↔ ∀ t, s ≠ t ++ singleton c := by
  simp [← Bool.not_eq_true, endsWith_char_iff_exists_append]

theorem eq_append_of_dropSuffix?_char_eq_some {c : Char} {s : String} {res : Slice} (h : s.dropSuffix? c = some res) :
    s = res.copy ++ singleton c := by
  rw [dropSuffix?_eq_dropSuffix?_toSlice] at h
  simpa using Slice.eq_append_of_dropSuffix?_char_eq_some h

end String
