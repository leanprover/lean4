/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Markus Himmel
-/
module

prelude
public import Init.Data.String.Slice
public import Init.Data.String.TakeDrop
public import Init.Data.String.Lemmas.Order
import Init.Data.String.Lemmas.Pattern.TakeDrop.Basic
import Init.Data.String.Lemmas.Pattern.Pred
import Init.Data.Option.Lemmas
import Init.Data.String.Lemmas.FindPos
import Init.Data.String.Lemmas.Intercalate
import Init.ByCases
import Init.Data.Order.Lemmas
import Init.Data.String.OrderInstances
import Init.Data.String.Lemmas.Basic

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

@[simp]
theorem Pos.skip?_bool_eq_some_iff {p : Char → Bool} {s : Slice} {pos res : s.Pos} :
    pos.skip? p = some res ↔ ∃ h, res = pos.next h ∧ p (pos.get h) := by
  simp [Pattern.Model.Pos.skip?_eq_some_iff, CharPred.isLongestMatchAt_iff]

@[simp]
theorem Pos.skip?_bool_eq_none_iff {p : Char → Bool} {s : Slice} {pos : s.Pos} :
    pos.skip? p = none ↔ ∀ h, p (pos.get h) = false := by
  simp [Pattern.Model.Pos.skip?_eq_none_iff, CharPred.matchesAt_iff]

theorem Pos.apply_skipWhile_bool_eq_false {p : Char → Bool} {s : Slice} {pos : s.Pos} {h} :
    p ((pos.skipWhile p).get h) = false := by
  have := Pattern.Model.Pos.not_matchesAt_skipWhile p pos
  simp_all [CharPred.matchesAt_iff]

theorem Pos.skipWhile_bool_eq_self_iff_get {p : Char → Bool} {s : Slice} {pos : s.Pos} :
    pos.skipWhile p = pos ↔ ∀ h, p (pos.get h) = false := by
  simp [Pattern.Model.Pos.skipWhile_eq_self_iff, CharPred.matchesAt_iff]

theorem Pos.apply_eq_true_of_lt_skipWhile_bool {p : Char → Bool} {s : Slice} {pos pos' : s.Pos}
    (h₁ : pos ≤ pos') (h₂ : pos' < pos.skipWhile p) : p (pos'.get (ne_endPos_of_lt h₂)) = true :=
  (CharPred.isLongestMatchAtChain_iff.1 (Pattern.Model.Pos.isLongestMatchAtChain_skipWhile p pos)).2 _ h₁ h₂

theorem apply_skipPrefixWhile_bool_eq_false {p : Char → Bool} {s : Slice} {h} :
    p ((s.skipPrefixWhile p).get h) = false := by
  simp [skipPrefixWhile_eq_skipWhile_startPos, Pos.apply_skipWhile_bool_eq_false]

theorem apply_eq_true_of_lt_skipPrefixWhile_bool {p : Char → Bool} {s : Slice} {pos : s.Pos} (h : pos < s.skipPrefixWhile p) :
    p (pos.get (Pos.ne_endPos_of_lt h)) = true :=
  Pos.apply_eq_true_of_lt_skipWhile_bool (Pos.startPos_le _) (skipPrefixWhile_eq_skipWhile_startPos ▸ h)

@[simp]
theorem all_bool_eq {p : Char → Bool} {s : Slice} : s.all p = s.copy.toList.all p := by
  rw [Bool.eq_iff_iff, Pattern.Model.all_eq_true_iff,
    CharPred.isLongestMatchAtChain_startPos_endPos_iff_toList, List.all_eq_true]

@[simp]
theorem Pos.skip?_prop_eq_some_iff {P : Char → Prop} [DecidablePred P] {s : Slice} {pos res : s.Pos} :
    pos.skip? P = some res ↔ ∃ h, res = pos.next h ∧ P (pos.get h) := by
  simp [Pos.skip?_prop_eq_skip?_decide, skip?_bool_eq_some_iff]

@[simp]
theorem Pos.skip?_prop_eq_none_iff {P : Char → Prop} [DecidablePred P] {s : Slice} {pos : s.Pos} :
    pos.skip? P = none ↔ ∀ h, ¬ P (pos.get h) := by
  simp [Pos.skip?_prop_eq_skip?_decide, skip?_bool_eq_none_iff]

theorem Pos.apply_skipWhile_prop {P : Char → Prop} [DecidablePred P] {s : Slice} {pos : s.Pos} {h} :
    ¬ P ((pos.skipWhile P).get h) := by
  have := Pattern.Model.Pos.not_matchesAt_skipWhile P pos
  simp_all [CharPred.Decidable.matchesAt_iff]

theorem Pos.skipWhile_prop_eq_self_iff_get {P : Char → Prop} [DecidablePred P] {s : Slice} {pos : s.Pos} :
    pos.skipWhile P = pos ↔ ∀ h, ¬ P (pos.get h) := by
  simp [Pos.skipWhile_prop_eq_skipWhile_decide, skipWhile_bool_eq_self_iff_get]

theorem Pos.apply_of_lt_skipWhile_prop {P : Char → Prop} [DecidablePred P] {s : Slice} {pos pos' : s.Pos}
    (h₁ : pos ≤ pos') (h₂ : pos' < pos.skipWhile P) : P (pos'.get (ne_endPos_of_lt h₂)) := by
  simp [Pos.skipWhile_prop_eq_skipWhile_decide] at h₂
  simpa using apply_eq_true_of_lt_skipWhile_bool h₁ h₂

theorem apply_skipPrefixWhile_prop {P : Char → Prop} [DecidablePred P] {s : Slice} {h} :
    ¬ P ((s.skipPrefixWhile P).get h) := by
  simp [skipPrefixWhile_eq_skipWhile_startPos, Pos.apply_skipWhile_prop]

theorem apply_of_lt_skipPrefixWhile_prop {P : Char → Prop} [DecidablePred P] {s : Slice} {pos : s.Pos}
    (h : pos < s.skipPrefixWhile P) : P (pos.get (Pos.ne_endPos_of_lt h)) := by
  simp [skipPrefixWhile_prop_eq_skipPrefixWhile_decide] at h
  simpa using apply_eq_true_of_lt_skipPrefixWhile_bool h

@[simp]
theorem all_prop_eq {P : Char → Prop} [DecidablePred P] {s : Slice} :
    s.all P = s.copy.toList.all (decide <| P ·) := by
  simp [all_prop_eq_all_decide]

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

@[simp]
theorem Pos.revSkip?_bool_eq_some_iff {p : Char → Bool} {s : Slice} {pos res : s.Pos} :
    pos.revSkip? p = some res ↔ ∃ h, res = pos.prev h ∧ p ((pos.prev h).get (by simp)) := by
  simp [Pattern.Model.Pos.revSkip?_eq_some_iff, CharPred.isLongestRevMatchAt_iff]

@[simp]
theorem Pos.revSkip?_bool_eq_none_iff {p : Char → Bool} {s : Slice} {pos : s.Pos} :
    pos.revSkip? p = none ↔ ∀ h, p ((pos.prev h).get (by simp)) = false := by
  simp [Pattern.Model.Pos.revSkip?_eq_none_iff, CharPred.revMatchesAt_iff]

theorem Pos.apply_revSkipWhile_bool_eq_false {p : Char → Bool} {s : Slice} {pos : s.Pos} {h} :
    p (((pos.revSkipWhile p).prev h).get (by simp)) = false := by
  have := Pattern.Model.Pos.not_revMatchesAt_revSkipWhile p pos
  simp_all [CharPred.revMatchesAt_iff]

theorem Pos.revSkipWhile_bool_eq_self_iff_get {p : Char → Bool} {s : Slice} {pos : s.Pos} :
    pos.revSkipWhile p = pos ↔ ∀ h, p ((pos.prev h).get (by simp)) = false := by
  simp [Pattern.Model.Pos.revSkipWhile_eq_self_iff, CharPred.revMatchesAt_iff]

theorem Pos.apply_eq_true_of_revSkipWhile_le_bool {p : Char → Bool} {s : Slice} {pos pos' : s.Pos}
    (h₁ : pos' < pos) (h₂ : pos.revSkipWhile p ≤ pos') : p (pos'.get (Pos.ne_endPos_of_lt h₁)) = true :=
  (CharPred.isLongestRevMatchAtChain_iff.1 (Pattern.Model.Pos.isLongestRevMatchAtChain_revSkipWhile p pos)).2 _ h₂ h₁

theorem apply_skipSuffixWhile_bool_eq_false {p : Char → Bool} {s : Slice} {h} :
    p (((s.skipSuffixWhile p).prev h).get (by simp)) = false := by
  simp [skipSuffixWhile_eq_revSkipWhile_endPos, Pos.apply_revSkipWhile_bool_eq_false]

theorem apply_eq_true_of_skipSuffixWhile_le_bool {p : Char → Bool} {s : Slice} {pos : s.Pos}
    (h : s.skipSuffixWhile p ≤ pos) (h' : pos < s.endPos) :
    p (pos.get (Pos.ne_endPos_of_lt h')) = true :=
  Pos.apply_eq_true_of_revSkipWhile_le_bool h' (skipSuffixWhile_eq_revSkipWhile_endPos ▸ h)

@[simp]
theorem revAll_bool_eq {p : Char → Bool} {s : Slice} : s.revAll p = s.copy.toList.all p := by
  rw [Bool.eq_iff_iff, Pattern.Model.revAll_eq_true_iff,
    CharPred.isLongestRevMatchAtChain_startPos_endPos_iff_toList, List.all_eq_true]

@[simp]
theorem Pos.revSkip?_prop_eq_some_iff {P : Char → Prop} [DecidablePred P] {s : Slice} {pos res : s.Pos} :
    pos.revSkip? P = some res ↔ ∃ h, res = pos.prev h ∧ P ((pos.prev h).get (by simp)) := by
  simp [Pos.revSkip?_prop_eq_revSkip?_decide, revSkip?_bool_eq_some_iff]

@[simp]
theorem Pos.revSkip?_prop_eq_none_iff {P : Char → Prop} [DecidablePred P] {s : Slice} {pos : s.Pos} :
    pos.revSkip? P = none ↔ ∀ h, ¬ P ((pos.prev h).get (by simp)) := by
  simp [Pos.revSkip?_prop_eq_revSkip?_decide, revSkip?_bool_eq_none_iff]

theorem Pos.apply_revSkipWhile_prop {P : Char → Prop} [DecidablePred P] {s : Slice} {pos : s.Pos} {h} :
    ¬ P (((pos.revSkipWhile P).prev h).get (by simp)) := by
  have := Pattern.Model.Pos.not_revMatchesAt_revSkipWhile P pos
  simp_all [CharPred.Decidable.revMatchesAt_iff]

theorem Pos.revSkipWhile_prop_eq_self_iff_get {P : Char → Prop} [DecidablePred P] {s : Slice} {pos : s.Pos} :
    pos.revSkipWhile P = pos ↔ ∀ h, ¬ P ((pos.prev h).get (by simp)) := by
  simp [Pos.revSkipWhile_prop_eq_revSkipWhile_decide, revSkipWhile_bool_eq_self_iff_get]

theorem Pos.apply_of_revSkipWhile_le_prop {P : Char → Prop} [DecidablePred P] {s : Slice} {pos pos' : s.Pos}
    (h₁ : pos' < pos) (h₂ : pos.revSkipWhile P ≤ pos') : P (pos'.get (Pos.ne_endPos_of_lt h₁)) := by
  have h₂' : pos.revSkipWhile (decide <| P ·) ≤ pos' :=
    Pos.revSkipWhile_prop_eq_revSkipWhile_decide (p := P) pos ▸ h₂
  simpa using Pos.apply_eq_true_of_revSkipWhile_le_bool h₁ h₂'

theorem apply_skipSuffixWhile_prop {P : Char → Prop} [DecidablePred P] {s : Slice} {h} :
    ¬ P (((s.skipSuffixWhile P).prev h).get (by simp)) := by
  have := Pattern.Model.Pos.not_revMatchesAt_revSkipWhile P s.endPos
  simp_all [CharPred.Decidable.revMatchesAt_iff, skipSuffixWhile_eq_revSkipWhile_endPos]

theorem apply_of_skipSuffixWhile_le_prop {P : Char → Prop} [DecidablePred P] {s : Slice} {pos : s.Pos}
    (h : s.skipSuffixWhile P ≤ pos) (h' : pos < s.endPos) :
    P (pos.get (Pos.ne_endPos_of_lt h')) :=
  Pos.apply_of_revSkipWhile_le_prop h' (skipSuffixWhile_eq_revSkipWhile_endPos (pat := P) ▸ h)

@[simp]
theorem revAll_prop_eq {P : Char → Prop} [DecidablePred P] {s : Slice} :
    s.revAll P = s.copy.toList.all (decide <| P ·) := by
  simp [revAll_prop_eq_revAll_decide, revAll_bool_eq]

end Slice

theorem skipPrefix?_bool_eq_some_iff {p : Char → Bool} {s : String} {pos : s.Pos} :
    s.skipPrefix? p = some pos ↔ ∃ h, pos = s.startPos.next h ∧ p (s.startPos.get h) = true := by
  simp [skipPrefix?_eq_skipPrefix?_toSlice, Slice.skipPrefix?_bool_eq_some_iff, ← Pos.toSlice_inj,
    Pos.toSlice_next]

theorem startsWith_bool_iff_get {p : Char → Bool} {s : String} :
    s.startsWith p ↔ ∃ h, p (s.startPos.get h) = true := by
  simp [← startsWith_toSlice, Slice.startsWith_bool_iff_get]

theorem startsWith_bool_eq_false_iff_get {p : Char → Bool} {s : String} :
    s.startsWith p = false ↔ ∀ h, p (s.startPos.get h) = false := by
  simp [← startsWith_toSlice, Slice.startsWith_bool_eq_false_iff_get]

theorem startsWith_bool_eq_head? {p : Char → Bool} {s : String} :
    s.startsWith p = s.toList.head?.any p := by
  simp [← startsWith_toSlice, Slice.startsWith_bool_eq_head?]

theorem eq_append_of_dropPrefix?_bool_eq_some {p : Char → Bool} {s : String} {res : Slice} (h : s.dropPrefix? p = some res) :
    ∃ c, s = singleton c ++ res.copy ∧ p c = true := by
  rw [dropPrefix?_eq_dropPrefix?_toSlice] at h
  simpa using Slice.eq_append_of_dropPrefix?_bool_eq_some h

@[simp]
theorem Pos.skip?_bool_eq_some_iff {p : Char → Bool} {s : String} {pos res : s.Pos} :
    pos.skip? p = some res ↔ ∃ h, res = pos.next h ∧ p (pos.get h) := by
  simp [skip?_eq_skip?_toSlice, ← toSlice_inj, toSlice_next]

@[simp]
theorem Pos.skip?_bool_eq_none_iff {p : Char → Bool} {s : String} {pos : s.Pos} :
    pos.skip? p = none ↔ ∀ h, p (pos.get h) = false := by
  simp [skip?_eq_skip?_toSlice]

theorem Pos.apply_skipWhile_bool_eq_false {p : Char → Bool} {s : String} {pos : s.Pos} {h} :
    p ((pos.skipWhile p).get h) = false := by
  simp [skipWhile_eq_skipWhile_toSlice, Slice.Pos.apply_skipWhile_bool_eq_false]

theorem Pos.skipWhile_bool_eq_self_iff_get {p : Char → Bool} {s : String} {pos : s.Pos} :
    pos.skipWhile p = pos ↔ ∀ h, p (pos.get h) = false := by
  simp [skipWhile_eq_skipWhile_toSlice, ← toSlice_inj, Slice.Pos.skipWhile_bool_eq_self_iff_get]

theorem Pos.apply_eq_true_of_lt_skipWhile_bool {p : Char → Bool} {s : String} {pos pos' : s.Pos}
    (h₁ : pos ≤ pos') (h₂ : pos' < pos.skipWhile p) : p (pos'.get (ne_endPos_of_lt h₂)) = true := by
  rw [Pos.get_eq_get_toSlice]
  exact Slice.Pos.apply_eq_true_of_lt_skipWhile_bool (toSlice_le_toSlice_iff.2 h₁)
    (by simpa [skipWhile_eq_skipWhile_toSlice] using h₂)

theorem apply_skipPrefixWhile_bool_eq_false {p : Char → Bool} {s : String} {h} :
    p ((s.skipPrefixWhile p).get h) = false := by
  simp [skipPrefixWhile_eq_skipPrefixWhile_toSlice, Slice.apply_skipPrefixWhile_bool_eq_false]

theorem apply_eq_true_of_lt_skipPrefixWhile_bool {p : Char → Bool} {s : String} {pos : s.Pos} (h : pos < s.skipPrefixWhile p) :
    p (pos.get (Pos.ne_endPos_of_lt h)) = true := by
  rw [Pos.get_eq_get_toSlice]
  exact Slice.apply_eq_true_of_lt_skipPrefixWhile_bool (by simpa [skipPrefixWhile_eq_skipPrefixWhile_toSlice] using h)

@[simp]
theorem all_bool_eq {p : Char → Bool} {s : String} : s.all p = s.toList.all p := by
  simp [← all_toSlice]

theorem skipPrefix?_prop_eq_some_iff {P : Char → Prop} [DecidablePred P] {s : String} {pos : s.Pos} :
    s.skipPrefix? P = some pos ↔ ∃ h, pos = s.startPos.next h ∧ P (s.startPos.get h) := by
  simp [skipPrefix?_eq_skipPrefix?_toSlice, Slice.skipPrefix?_prop_eq_some_iff, ← Pos.toSlice_inj,
    Pos.toSlice_next]

theorem startsWith_prop_iff_get {P : Char → Prop} [DecidablePred P] {s : String} :
    s.startsWith P ↔ ∃ h, P (s.startPos.get h) := by
  simp [← startsWith_toSlice, Slice.startsWith_prop_iff_get]

theorem startsWith_prop_eq_false_iff_get {P : Char → Prop} [DecidablePred P] {s : String} :
    s.startsWith P = false ↔ ∀ h, ¬ P (s.startPos.get h) := by
  simp [← startsWith_toSlice, Slice.startsWith_prop_eq_false_iff_get]

theorem startsWith_prop_eq_head? {P : Char → Prop} [DecidablePred P] {s : String} :
    s.startsWith P = s.toList.head?.any (decide <| P ·) := by
  simp [← startsWith_toSlice, Slice.startsWith_prop_eq_head?]

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
  simp [← endsWith_toSlice, Slice.endsWith_bool_iff_get, Pos.prev_toSlice]

theorem endsWith_bool_eq_false_iff_get {p : Char → Bool} {s : String} :
    s.endsWith p = false ↔ ∀ h, p ((s.endPos.prev h).get (by simp)) = false := by
  simp [← endsWith_toSlice, Slice.endsWith_bool_eq_false_iff_get, Pos.prev_toSlice]

theorem endsWith_bool_eq_getLast? {p : Char → Bool} {s : String} :
    s.endsWith p = s.toList.getLast?.any p := by
  simp [← endsWith_toSlice, Slice.endsWith_bool_eq_getLast?]

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
  simp [← endsWith_toSlice, Slice.endsWith_prop_iff_get, Pos.prev_toSlice]

theorem endsWith_prop_eq_false_iff_get {P : Char → Prop} [DecidablePred P] {s : String} :
    s.endsWith P = false ↔ ∀ h, ¬ P ((s.endPos.prev h).get (by simp)) := by
  simp [← endsWith_toSlice, Slice.endsWith_prop_eq_false_iff_get, Pos.prev_toSlice]

theorem endsWith_prop_eq_getLast? {P : Char → Prop} [DecidablePred P] {s : String} :
    s.endsWith P = s.toList.getLast?.any (decide <| P ·) := by
  simp [← endsWith_toSlice, Slice.endsWith_prop_eq_getLast?]

theorem eq_append_of_dropSuffix?_prop_eq_some {P : Char → Prop} [DecidablePred P] {s : String} {res : Slice}
    (h : s.dropSuffix? P = some res) : ∃ c, s = res.copy ++ singleton c ∧ P c := by
  rw [dropSuffix?_eq_dropSuffix?_toSlice] at h
  simpa using Slice.eq_append_of_dropSuffix?_prop_eq_some h

@[simp]
theorem Pos.skip?_prop_eq_some_iff {P : Char → Prop} [DecidablePred P] {s : String} {pos res : s.Pos} :
    pos.skip? P = some res ↔ ∃ h, res = pos.next h ∧ P (pos.get h) := by
  simp [skip?_eq_skip?_toSlice, ← toSlice_inj, toSlice_next]

@[simp]
theorem Pos.skip?_prop_eq_none_iff {P : Char → Prop} [DecidablePred P] {s : String} {pos : s.Pos} :
    pos.skip? P = none ↔ ∀ h, ¬ P (pos.get h) := by
  simp [skip?_eq_skip?_toSlice]

theorem Pos.apply_skipWhile_prop {P : Char → Prop} [DecidablePred P] {s : String} {pos : s.Pos} {h} :
    ¬ P ((pos.skipWhile P).get h) := by
  simp [skipWhile_eq_skipWhile_toSlice, Slice.Pos.apply_skipWhile_prop]

theorem Pos.skipWhile_prop_eq_self_iff_get {P : Char → Prop} [DecidablePred P] {s : String} {pos : s.Pos} :
    pos.skipWhile P = pos ↔ ∀ h, ¬ P (pos.get h) := by
  simp [skipWhile_eq_skipWhile_toSlice, ← toSlice_inj, Slice.Pos.skipWhile_prop_eq_self_iff_get]

theorem Pos.apply_of_lt_skipWhile_prop {P : Char → Prop} [DecidablePred P] {s : String} {pos pos' : s.Pos}
    (h₁ : pos ≤ pos') (h₂ : pos' < pos.skipWhile P) : P (pos'.get (ne_endPos_of_lt h₂)) := by
  rw [Pos.get_eq_get_toSlice]
  exact Slice.Pos.apply_of_lt_skipWhile_prop (toSlice_le_toSlice_iff.2 h₁)
    (by simpa [skipWhile_eq_skipWhile_toSlice] using h₂)

theorem apply_skipPrefixWhile_prop {P : Char → Prop} [DecidablePred P] {s : String} {h} :
    ¬ P ((s.skipPrefixWhile P).get h) := by
  simp [skipPrefixWhile_eq_skipPrefixWhile_toSlice, Slice.apply_skipPrefixWhile_prop]

theorem apply_of_lt_skipPrefixWhile_prop {P : Char → Prop} [DecidablePred P] {s : String} {pos : s.Pos}
    (h : pos < s.skipPrefixWhile P) : P (pos.get (Pos.ne_endPos_of_lt h)) := by
  rw [Pos.get_eq_get_toSlice]
  exact Slice.apply_of_lt_skipPrefixWhile_prop (by simpa [skipPrefixWhile_eq_skipPrefixWhile_toSlice] using h)

@[simp]
theorem all_prop_eq {P : Char → Prop} [DecidablePred P] {s : String} :
    s.all P = s.toList.all (decide <| P ·) := by
  simp [← all_toSlice]

@[simp]
theorem Pos.revSkip?_bool_eq_some_iff {p : Char → Bool} {s : String} {pos res : s.Pos} :
    pos.revSkip? p = some res ↔ ∃ h, res = pos.prev h ∧ p ((pos.prev h).get (by simp)) := by
  simp [revSkip?_eq_revSkip?_toSlice, ← toSlice_inj, toSlice_prev, get_eq_get_toSlice]

@[simp]
theorem Pos.revSkip?_bool_eq_none_iff {p : Char → Bool} {s : String} {pos : s.Pos} :
    pos.revSkip? p = none ↔ ∀ h, p ((pos.prev h).get (by simp)) = false := by
  simp [revSkip?_eq_revSkip?_toSlice, Pos.prev_toSlice]

theorem Pos.apply_revSkipWhile_bool_eq_false {p : Char → Bool} {s : String} {pos : s.Pos} {h} :
    p (((pos.revSkipWhile p).prev h).get (by simp)) = false := by
  have h' : pos.toSlice.revSkipWhile p ≠ s.toSlice.startPos := by
    simpa [Pos.revSkipWhile_eq_revSkipWhile_toSlice, ← toSlice_inj] using h
  have := Slice.Pos.apply_revSkipWhile_bool_eq_false (pos := pos.toSlice) (h := h')
  simpa [Pos.revSkipWhile_eq_revSkipWhile_toSlice, Pos.prev_ofToSlice]

theorem Pos.revSkipWhile_bool_eq_self_iff_get {p : Char → Bool} {s : String} {pos : s.Pos} :
    pos.revSkipWhile p = pos ↔ ∀ h, p ((pos.prev h).get (by simp)) = false := by
  simp [Pos.revSkipWhile_eq_revSkipWhile_toSlice, ← toSlice_inj, Slice.Pos.revSkipWhile_bool_eq_self_iff_get,
    Pos.prev_toSlice]

theorem Pos.apply_eq_true_of_revSkipWhile_le_bool {p : Char → Bool} {s : String} {pos pos' : s.Pos}
    (h₁ : pos' < pos) (h₂ : pos.revSkipWhile p ≤ pos') : p (pos'.get (ne_endPos_of_lt h₁)) = true := by
  rw [Pos.get_eq_get_toSlice]
  exact Slice.Pos.apply_eq_true_of_revSkipWhile_le_bool
    (Pos.toSlice_lt_toSlice_iff.2 h₁)
    (by simpa [Pos.revSkipWhile_eq_revSkipWhile_toSlice, Pos.ofToSlice_le_iff] using h₂)

theorem apply_skipSuffixWhile_bool_eq_false {p : Char → Bool} {s : String} {h} :
    p (((s.skipSuffixWhile p).prev h).get (by simp)) = false := by
  have h' : s.toSlice.skipSuffixWhile p ≠ s.toSlice.startPos := by
    simpa [skipSuffixWhile_eq_skipSuffixWhile_toSlice, ← Pos.toSlice_inj] using h
  have := Slice.apply_skipSuffixWhile_bool_eq_false (s := s.toSlice) (h := h')
  simpa [skipSuffixWhile_eq_skipSuffixWhile_toSlice, Pos.prev_ofToSlice]

theorem apply_eq_true_of_skipSuffixWhile_le_bool {p : Char → Bool} {s : String} {pos : s.Pos}
    (h : s.skipSuffixWhile p ≤ pos) (h' : pos < s.endPos) :
    p (pos.get (Pos.ne_endPos_of_lt h')) = true := by
  rw [Pos.get_eq_get_toSlice]
  exact Slice.apply_eq_true_of_skipSuffixWhile_le_bool
    (by simpa [skipSuffixWhile_eq_skipSuffixWhile_toSlice, Pos.ofToSlice_le_iff] using h)
    (by simpa [Pos.toSlice_lt_toSlice_iff] using h')

@[simp]
theorem revAll_bool_eq {p : Char → Bool} {s : String} : s.revAll p = s.toList.all p := by
  simp [← revAll_toSlice]

@[simp]
theorem Pos.revSkip?_prop_eq_some_iff {P : Char → Prop} [DecidablePred P] {s : String} {pos res : s.Pos} :
    pos.revSkip? P = some res ↔ ∃ h, res = pos.prev h ∧ P ((pos.prev h).get (by simp)) := by
  simp [revSkip?_eq_revSkip?_toSlice, ← toSlice_inj, toSlice_prev, get_eq_get_toSlice]

@[simp]
theorem Pos.revSkip?_prop_eq_none_iff {P : Char → Prop} [DecidablePred P] {s : String} {pos : s.Pos} :
    pos.revSkip? P = none ↔ ∀ h, ¬ P ((pos.prev h).get (by simp)) := by
  simp [revSkip?_eq_revSkip?_toSlice, Pos.prev_toSlice]

theorem Pos.apply_revSkipWhile_prop {P : Char → Prop} [DecidablePred P] {s : String} {pos : s.Pos} {h} :
    ¬ P (((pos.revSkipWhile P).prev h).get (by simp)) := by
  have h' : pos.toSlice.revSkipWhile P ≠ s.toSlice.startPos := by
    simpa [Pos.revSkipWhile_eq_revSkipWhile_toSlice, ← toSlice_inj] using h
  have := Slice.Pos.apply_revSkipWhile_prop (pos := pos.toSlice) (h := h')
  simpa [Pos.revSkipWhile_eq_revSkipWhile_toSlice, Pos.prev_ofToSlice]

theorem Pos.revSkipWhile_prop_eq_self_iff_get {P : Char → Prop} [DecidablePred P] {s : String} {pos : s.Pos} :
    pos.revSkipWhile P = pos ↔ ∀ h, ¬ P ((pos.prev h).get (by simp)) := by
  simp [Pos.revSkipWhile_eq_revSkipWhile_toSlice, ← toSlice_inj,
    Slice.Pos.revSkipWhile_prop_eq_self_iff_get, Pos.prev_toSlice]

theorem Pos.apply_of_revSkipWhile_le_prop {P : Char → Prop} [DecidablePred P] {s : String} {pos pos' : s.Pos}
    (h₁ : pos' < pos) (h₂ : pos.revSkipWhile P ≤ pos') : P (pos'.get (ne_endPos_of_lt h₁)) := by
  rw [Pos.get_eq_get_toSlice]
  exact Slice.Pos.apply_of_revSkipWhile_le_prop
    (Pos.toSlice_lt_toSlice_iff.2 h₁)
    (by simpa [Pos.revSkipWhile_eq_revSkipWhile_toSlice, Pos.ofToSlice_le_iff] using h₂)

theorem apply_skipSuffixWhile_prop {P : Char → Prop} [DecidablePred P] {s : String} {h} :
    ¬ P (((s.skipSuffixWhile P).prev h).get (by simp)) := by
  have h' : s.toSlice.skipSuffixWhile P ≠ s.toSlice.startPos := by
    simpa [skipSuffixWhile_eq_skipSuffixWhile_toSlice, ← Pos.toSlice_inj] using h
  have := Slice.apply_skipSuffixWhile_prop (s := s.toSlice) (h := h')
  simpa [skipSuffixWhile_eq_skipSuffixWhile_toSlice, Pos.prev_ofToSlice]

theorem apply_of_skipSuffixWhile_le_prop {P : Char → Prop} [DecidablePred P] {s : String} {pos : s.Pos}
    (h : s.skipSuffixWhile P ≤ pos) (h' : pos < s.endPos) :
    P (pos.get (Pos.ne_endPos_of_lt h')) := by
  rw [Pos.get_eq_get_toSlice]
  exact Slice.apply_of_skipSuffixWhile_le_prop
    (by simpa [skipSuffixWhile_eq_skipSuffixWhile_toSlice, Pos.ofToSlice_le_iff] using h)
    (by simpa [Pos.toSlice_lt_toSlice_iff] using h')

@[simp]
theorem revAll_prop_eq {P : Char → Prop} [DecidablePred P] {s : String} :
    s.revAll P = s.toList.all (decide <| P ·) := by
  simp [← revAll_toSlice]

end String
