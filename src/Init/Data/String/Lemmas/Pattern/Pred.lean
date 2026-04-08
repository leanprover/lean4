/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

prelude
public import Init.Data.String.Pattern.Pred
public import Init.Data.String.Lemmas.Pattern.Basic
public import Init.Data.String.Slice
public import Init.Data.String.Search
import all Init.Data.String.Slice
import all Init.Data.String.Pattern.Pred
import all Init.Data.String.Search
import Init.Data.Option.Lemmas
import Init.Data.String.Lemmas.Basic
import Init.Data.String.Lemmas.Order
import Init.Data.Order.Lemmas
import Init.Data.String.OrderInstances
import Init.Data.String.Lemmas.Iterate
import Init.Omega
import Init.Data.String.Lemmas.FindPos

public section

namespace String.Slice.Pattern.Model.CharPred

instance {p : Char → Bool} : PatternModel p where
  Matches s := ∃ c, s = singleton c ∧ p c

instance {p : Char → Bool} : StrictPatternModel p where
  not_matches_empty := by simp [PatternModel.Matches]

instance {p : Char → Bool} : NoPrefixPatternModel p :=
  .of_length_eq (by simp +contextual [PatternModel.Matches])

instance {p : Char → Bool} : NoSuffixPatternModel p :=
  .of_length_eq (by simp +contextual [PatternModel.Matches])

theorem isMatch_iff {p : Char → Bool} {s : Slice} {pos : s.Pos} :
    IsMatch p pos ↔
      ∃ (h : s.startPos ≠ s.endPos), pos = s.startPos.next h ∧ p (s.startPos.get h) := by
  simp only [Model.isMatch_iff, PatternModel.Matches, copy_sliceTo_eq_iff_exists_splits]
  refine ⟨?_, ?_⟩
  · simp only [splits_singleton_iff]
    refine fun ⟨c, ⟨t₂, h, h₁, h₂, h₃⟩, hc⟩ => ⟨h, h₁, h₂ ▸ hc⟩
  · rintro ⟨h, rfl, h'⟩
    exact ⟨s.startPos.get h, ⟨_, Slice.splits_next_startPos⟩, h'⟩

theorem isRevMatch_iff {p : Char → Bool} {s : Slice} {pos : s.Pos} :
    IsRevMatch p pos ↔
      ∃ (h : s.endPos ≠ s.startPos), pos = s.endPos.prev h ∧ p ((s.endPos.prev h).get (by simp)) := by
  simp only [Model.isRevMatch_iff, PatternModel.Matches, copy_sliceFrom_eq_iff_exists_splits]
  refine ⟨?_, ?_⟩
  · simp only [splits_singleton_right_iff]
    refine fun ⟨c, ⟨t₂, h, h₁, h₂, h₃⟩, hc⟩ => ⟨h, h₁, h₂ ▸ hc⟩
  · rintro ⟨h, rfl, h'⟩
    exact ⟨(s.endPos.prev h).get (by simp), ⟨_, Slice.splits_prev_endPos⟩, h'⟩

theorem isLongestMatch_iff {p : Char → Bool} {s : Slice} {pos : s.Pos} :
    IsLongestMatch p pos ↔
      ∃ (h : s.startPos ≠ s.endPos), pos = s.startPos.next h ∧ p (s.startPos.get h) := by
  rw [isLongestMatch_iff_isMatch, isMatch_iff]

theorem isLongestRevMatch_iff {p : Char → Bool} {s : Slice} {pos : s.Pos} :
    IsLongestRevMatch p pos ↔
      ∃ (h : s.endPos ≠ s.startPos), pos = s.endPos.prev h ∧ p ((s.endPos.prev h).get (by simp)) := by
  rw [isLongestRevMatch_iff_isRevMatch, isRevMatch_iff]

theorem isLongestMatchAt_iff {p : Char → Bool} {s : Slice} {pos pos' : s.Pos} :
    IsLongestMatchAt p pos pos' ↔ ∃ h, pos' = pos.next h ∧ p (pos.get h) := by
  simp +contextual [Model.isLongestMatchAt_iff, isLongestMatch_iff, ← Pos.ofSliceFrom_inj,
    Pos.get_eq_get_ofSliceFrom, Pos.ofSliceFrom_next]

theorem isLongestMatchAtChain_iff {p : Char → Bool} {s : Slice} {pos pos' : s.Pos} :
    IsLongestMatchAtChain p pos pos' ↔ pos ≤ pos' ∧ ∀ pos'', pos ≤ pos'' → (h : pos'' < pos') → p (pos''.get (Pos.ne_endPos_of_lt h)) := by
  induction pos using WellFounded.induction Pos.wellFounded_gt with | h pos ih
  obtain (h|rfl|h) := Std.lt_trichotomy pos pos'
  · refine ⟨fun h => ?_, fun ⟨h₁, h₂⟩ => ?_⟩
    · cases h with
      | nil => exact (Std.lt_irrefl h).elim
      | cons _ mid _ h₁ h₂ =>
        obtain ⟨h₀, rfl, h₁'⟩ := isLongestMatchAt_iff.1 h₁
        refine ⟨Std.le_of_lt h, fun pos'' hp₁ hp₂ => ?_⟩
        obtain (hh|rfl) := Std.le_iff_lt_or_eq.1 hp₁
        · exact ((ih (pos.next (Pos.ne_endPos_of_lt h)) Pos.lt_next).1 h₂).2 _ (by simpa) hp₂
        · exact h₁'
    · refine .cons _ (pos.next (Pos.ne_endPos_of_lt h)) _ ?_ ((ih _ Pos.lt_next).2 ?_)
      · exact isLongestMatchAt_iff.2 ⟨Pos.ne_endPos_of_lt h, rfl, h₂ _ (by simp) h⟩
      · exact ⟨by simpa, fun pos'' hp₁ hp₂ => h₂ _ (Std.le_trans Pos.le_next hp₁) hp₂⟩
  · simpa using fun _ h₁ h₂ => (Std.lt_irrefl (Std.lt_of_le_of_lt h₁ h₂)).elim
  · simpa [Std.not_le.2 h] using fun h' => (Std.not_le.2 h h'.le).elim

theorem isLongestMatchAtChain_iff_toList {p : Char → Bool} {s : Slice} {pos pos' : s.Pos} :
    IsLongestMatchAtChain p pos pos' ↔ ∃ (h : pos ≤ pos'), ∀ c, c ∈ (s.slice pos pos' h).copy.toList → p c := by
  simp only [isLongestMatchAtChain_iff, mem_toList_copy_iff_exists_get, Pos.get_eq_get_ofSlice,
    forall_exists_index]
  refine ⟨fun ⟨h₁, h₂⟩ => ⟨h₁, fun c p' hp => ?_⟩, fun ⟨h₁, h₂⟩ => ⟨h₁, fun p' hp₁ hp₂ => ?_⟩⟩
  · rintro rfl
    exact h₂ _ Pos.le_ofSlice (by simp [Pos.ofSlice_lt_iff, h₁, hp])
  · refine h₂ _ (Pos.slice p' _ _ hp₁ (Std.le_of_lt hp₂)) ?_ (by simp)
    rwa [← Pos.lt_endPos_iff, ← Pos.slice_eq_endPos (h := h₁), Pos.slice_lt_slice_iff]

theorem isLongestMatchAtChain_startPos_endPos_iff_toList {p : Char → Bool} {s : Slice} :
    IsLongestMatchAtChain p s.startPos s.endPos ↔ ∀ c, c ∈ s.copy.toList → p c := by
  simp [isLongestMatchAtChain_iff_toList]

theorem isLongestRevMatchAt_iff {p : Char → Bool} {s : Slice} {pos pos' : s.Pos} :
    IsLongestRevMatchAt p pos pos' ↔ ∃ h, pos = pos'.prev h ∧ p ((pos'.prev h).get (by simp)) := by
  simp +contextual [Model.isLongestRevMatchAt_iff, isLongestRevMatch_iff, ← Pos.ofSliceTo_inj,
    Pos.get_eq_get_ofSliceTo, Pos.ofSliceTo_prev]

theorem isLongestMatchAt_of_get {p : Char → Bool} {s : Slice} {pos : s.Pos} {h : pos ≠ s.endPos}
    (hc : p (pos.get h)) : IsLongestMatchAt p pos (pos.next h) :=
  isLongestMatchAt_iff.2 ⟨h, by simp [hc]⟩

theorem isLongestRevMatchAt_of_get {p : Char → Bool} {s : Slice} {pos : s.Pos} {h : pos ≠ s.startPos}
    (hc : p ((pos.prev h).get (by simp))) : IsLongestRevMatchAt p (pos.prev h) pos :=
  isLongestRevMatchAt_iff.2 ⟨h, by simp [hc]⟩

theorem isLongestRevMatchAtChain_iff {p : Char → Bool} {s : Slice} {pos pos' : s.Pos} :
    IsLongestRevMatchAtChain p pos pos' ↔ pos ≤ pos' ∧ ∀ pos'', pos ≤ pos'' → (h : pos'' < pos') → p (pos''.get (Pos.ne_endPos_of_lt h)) := by
  induction pos' using WellFounded.induction Pos.wellFounded_lt with | h pos' ih
  obtain (h|rfl|h) := Std.lt_trichotomy pos pos'
  · refine ⟨fun h => ?_, fun ⟨h₁, h₂⟩ => ?_⟩
    · cases h with
      | nil => exact (Std.lt_irrefl h).elim
      | cons _ _ hchain hmatch =>
        obtain ⟨hne, hmid, hp⟩ := isLongestRevMatchAt_iff.1 hmatch
        refine ⟨Std.le_of_lt h, fun pos'' hp₁ hp₂ => ?_⟩
        rcases Std.le_iff_lt_or_eq.1 (Pos.le_prev_iff_lt.2 hp₂) with hh | heq
        · exact ((ih _ Pos.prev_lt).1 (hmid ▸ hchain)).2 _ hp₁ hh
        · exact heq ▸ hp
    · have hne : pos' ≠ s.startPos := Slice.Pos.ne_startPos_of_lt h
      refine .cons _ (pos'.prev hne) _ ((ih _ Pos.prev_lt).2 ?_)
        (isLongestRevMatchAt_of_get (h₂ _ (Pos.le_prev_iff_lt.2 h) Pos.prev_lt))
      exact ⟨Pos.le_prev_iff_lt.2 h, fun pos'' hp₁ hp₂ =>
        h₂ _ hp₁ (Std.lt_trans hp₂ Pos.prev_lt)⟩
  · simpa using fun _ h₁ h₂ => (Std.lt_irrefl (Std.lt_of_le_of_lt h₁ h₂)).elim
  · simpa [Std.not_le.2 h] using fun h' => (Std.not_le.2 h h'.le).elim

theorem isLongestRevMatchAtChain_iff_toList {p : Char → Bool} {s : Slice} {pos pos' : s.Pos} :
    IsLongestRevMatchAtChain p pos pos' ↔ ∃ (h : pos ≤ pos'), ∀ c, c ∈ (s.slice pos pos' h).copy.toList → p c :=
  isLongestRevMatchAtChain_iff.trans (isLongestMatchAtChain_iff.symm.trans isLongestMatchAtChain_iff_toList)

theorem isLongestRevMatchAtChain_startPos_endPos_iff_toList {p : Char → Bool} {s : Slice} :
    IsLongestRevMatchAtChain p s.startPos s.endPos ↔ ∀ c, c ∈ s.copy.toList → p c := by
  simp [isLongestRevMatchAtChain_iff_toList]

instance {p : Char → Bool} : LawfulForwardPatternModel p where
  skipPrefix?_eq_some_iff {s} pos := by
    simp [isLongestMatch_iff, ForwardPattern.skipPrefix?, and_comm, eq_comm (b := pos)]

instance {p : Char → Bool} : LawfulBackwardPatternModel p where
  skipSuffix?_eq_some_iff {s} pos := by
    simp [isLongestRevMatch_iff, BackwardPattern.skipSuffix?, and_comm, eq_comm (b := pos)]

instance {p : Char → Bool} : LawfulToForwardSearcherModel p :=
  .defaultImplementation

instance {p : Char → Bool} : LawfulToBackwardSearcherModel p :=
  .defaultImplementation

theorem matchesAt_iff {p : Char → Bool} {s : Slice} {pos : s.Pos} :
    MatchesAt p pos ↔ ∃ (h : pos ≠ s.endPos), p (pos.get h) := by
  simp [matchesAt_iff_exists_isLongestMatchAt, isLongestMatchAt_iff, exists_comm]

theorem revMatchesAt_iff {p : Char → Bool} {s : Slice} {pos : s.Pos} :
    RevMatchesAt p pos ↔ ∃ (h : pos ≠ s.startPos), p ((pos.prev h).get (by simp)) := by
  simp [revMatchesAt_iff_exists_isLongestRevMatchAt, isLongestRevMatchAt_iff, exists_comm]

theorem not_matchesAt_of_get {p : Char → Bool} {s : Slice} {pos : s.Pos} {h : pos ≠ s.endPos}
    (hc : p (pos.get h) = false) : ¬ MatchesAt p pos := by
  simp [matchesAt_iff, hc]

theorem not_revMatchesAt_of_get {p : Char → Bool} {s : Slice} {pos : s.Pos} {h : pos ≠ s.startPos}
    (hc : p ((pos.prev h).get (by simp)) = false) : ¬ RevMatchesAt p pos := by
  simp [revMatchesAt_iff, hc]

theorem matchAt?_eq {s : Slice} {pos : s.Pos} {p : Char → Bool} :
    matchAt? p pos =
      if h₀ : ∃ (h : pos ≠ s.endPos), p (pos.get h) then some (pos.next h₀.1) else none := by
  split <;> simp_all [isLongestMatchAt_iff, matchesAt_iff]

theorem revMatchAt?_eq {s : Slice} {pos : s.Pos} {p : Char → Bool} :
    revMatchAt? p pos =
      if h₀ : ∃ (h : pos ≠ s.startPos), p ((pos.prev h).get (by simp)) then some (pos.prev h₀.1) else none := by
  split <;> simp_all [isLongestRevMatchAt_iff, revMatchesAt_iff]

namespace Decidable

instance {p : Char → Prop} [DecidablePred p] : PatternModel p where
  Matches := PatternModel.Matches (decide <| p ·)

instance {p : Char → Prop} [DecidablePred p] : StrictPatternModel p where
  not_matches_empty := StrictPatternModel.not_matches_empty (pat := (decide <| p ·))

instance {p : Char → Prop} [DecidablePred p] : NoPrefixPatternModel p where
  eq_empty := NoPrefixPatternModel.eq_empty (pat := (decide <| p ·))

instance {p : Char → Prop} [DecidablePred p] : NoSuffixPatternModel p where
  eq_empty := NoSuffixPatternModel.eq_empty (pat := (decide <| p ·))

theorem isMatch_iff_isMatch_decide {p : Char → Prop} [DecidablePred p] {s : Slice} {pos : s.Pos} :
    IsMatch p pos ↔ IsMatch (decide <| p ·) pos :=
  ⟨fun ⟨h⟩ => ⟨h⟩, fun ⟨h⟩ => ⟨h⟩⟩

theorem isRevMatch_iff_isRevMatch_decide {p : Char → Prop} [DecidablePred p] {s : Slice} {pos : s.Pos} :
    IsRevMatch p pos ↔ IsRevMatch (decide <| p ·) pos :=
  ⟨fun ⟨h⟩ => ⟨h⟩, fun ⟨h⟩ => ⟨h⟩⟩

theorem isMatch_iff {p : Char → Prop} [DecidablePred p] {s : Slice} {pos : s.Pos} :
    IsMatch p pos ↔
      ∃ (h : s.startPos ≠ s.endPos), pos = s.startPos.next h ∧ p (s.startPos.get h) := by
  simp [isMatch_iff_isMatch_decide, CharPred.isMatch_iff]

theorem isRevMatch_iff {p : Char → Prop} [DecidablePred p] {s : Slice} {pos : s.Pos} :
    IsRevMatch p pos ↔
      ∃ (h : s.endPos ≠ s.startPos), pos = s.endPos.prev h ∧ p ((s.endPos.prev h).get (by simp)) := by
  simp [isRevMatch_iff_isRevMatch_decide, CharPred.isRevMatch_iff]

theorem isLongestMatch_iff {p : Char → Prop} [DecidablePred p] {s : Slice} {pos : s.Pos} :
    IsLongestMatch p pos ↔
      ∃ (h : s.startPos ≠ s.endPos), pos = s.startPos.next h ∧ p (s.startPos.get h) := by
  rw [isLongestMatch_iff_isMatch, isMatch_iff]

theorem isLongestRevMatch_iff {p : Char → Prop} [DecidablePred p] {s : Slice} {pos : s.Pos} :
    IsLongestRevMatch p pos ↔
      ∃ (h : s.endPos ≠ s.startPos), pos = s.endPos.prev h ∧ p ((s.endPos.prev h).get (by simp)) := by
  simp [isLongestRevMatch_iff_isRevMatch, isRevMatch_iff]

theorem isLongestMatch_iff_isLongestMatch_decide {p : Char → Prop} [DecidablePred p] {s : Slice}
    {pos : s.Pos} : IsLongestMatch p pos ↔ IsLongestMatch (decide <| p ·) pos := by
  simp [isLongestMatch_iff_isMatch, isMatch_iff_isMatch_decide]

theorem isLongestRevMatch_iff_isLongestRevMatch_decide {p : Char → Prop} [DecidablePred p] {s : Slice}
    {pos : s.Pos} : IsLongestRevMatch p pos ↔ IsLongestRevMatch (decide <| p ·) pos := by
  simp [isLongestRevMatch_iff_isRevMatch, isRevMatch_iff_isRevMatch_decide]

theorem isLongestMatchAt_iff_isLongestMatchAt_decide {p : Char → Prop} [DecidablePred p]
    {s : Slice} {pos pos' : s.Pos} :
    IsLongestMatchAt p pos pos' ↔ IsLongestMatchAt (decide <| p ·) pos pos' := by
  simp [Model.isLongestMatchAt_iff, isLongestMatch_iff_isLongestMatch_decide]

theorem isLongestRevMatchAt_iff_isLongestRevMatchAt_decide {p : Char → Prop} [DecidablePred p]
    {s : Slice} {pos pos' : s.Pos} :
    IsLongestRevMatchAt p pos pos' ↔ IsLongestRevMatchAt (decide <| p ·) pos pos' := by
  simp [Model.isLongestRevMatchAt_iff, isLongestRevMatch_iff_isLongestRevMatch_decide]

theorem isLongestMatchAtChain_iff_isLongestMatchAtChain_decide {p : Char → Prop} [DecidablePred p]
    {s : Slice} {pos pos' : s.Pos} :
    IsLongestMatchAtChain p pos pos' ↔ IsLongestMatchAtChain (decide <| p ·) pos pos' := by
  constructor
  · intro h; induction h with
    | nil => exact .nil _
    | cons _ mid _ hmatch hchain ih =>
      exact .cons _ mid _ (isLongestMatchAt_iff_isLongestMatchAt_decide.1 hmatch) ih
  · intro h; induction h with
    | nil => exact .nil _
    | cons _ mid _ hmatch hchain ih =>
      exact .cons _ mid _ (isLongestMatchAt_iff_isLongestMatchAt_decide.2 hmatch) ih

theorem isLongestRevMatchAtChain_iff_isLongestRevMatchAtChain_decide {p : Char → Prop} [DecidablePred p]
    {s : Slice} {pos pos' : s.Pos} :
    IsLongestRevMatchAtChain p pos pos' ↔ IsLongestRevMatchAtChain (decide <| p ·) pos pos' := by
  constructor
  · intro h; induction h with
    | nil => exact .nil _
    | cons _ _ hchain hmatch ih =>
      exact .cons _ _ _ ih (isLongestRevMatchAt_iff_isLongestRevMatchAt_decide.1 hmatch)
  · intro h; induction h with
    | nil => exact .nil _
    | cons _ _ hchain hmatch ih =>
      exact .cons _ _ _ ih (isLongestRevMatchAt_iff_isLongestRevMatchAt_decide.2 hmatch)

theorem isLongestMatchAt_iff {p : Char → Prop} [DecidablePred p] {s : Slice}
    {pos pos' : s.Pos} :
    IsLongestMatchAt p pos pos' ↔ ∃ h, pos' = pos.next h ∧ p (pos.get h) := by
  simp [isLongestMatchAt_iff_isLongestMatchAt_decide, CharPred.isLongestMatchAt_iff]

theorem isLongestRevMatchAt_iff {p : Char → Prop} [DecidablePred p] {s : Slice}
    {pos pos' : s.Pos} :
    IsLongestRevMatchAt p pos pos' ↔ ∃ h, pos = pos'.prev h ∧ p ((pos'.prev h).get (by simp)) := by
  simp [isLongestRevMatchAt_iff_isLongestRevMatchAt_decide, CharPred.isLongestRevMatchAt_iff]

theorem isLongestMatchAt_of_get {p : Char → Prop} [DecidablePred p] {s : Slice} {pos : s.Pos}
    {h : pos ≠ s.endPos} (hc : p (pos.get h)) : IsLongestMatchAt p pos (pos.next h) :=
  isLongestMatchAt_iff.2 ⟨h, by simp [hc]⟩

theorem isLongestRevMatchAt_of_get {p : Char → Prop} [DecidablePred p] {s : Slice} {pos : s.Pos}
    {h : pos ≠ s.startPos} (hc : p ((pos.prev h).get (by simp))) :
    IsLongestRevMatchAt p (pos.prev h) pos :=
  isLongestRevMatchAt_iff.2 ⟨h, by simp [hc]⟩

theorem matchesAt_iff_matchesAt_decide {p : Char → Prop} [DecidablePred p] {s : Slice}
    {pos : s.Pos} : MatchesAt p pos ↔ MatchesAt (decide <| p ·) pos := by
  simp [matchesAt_iff_exists_isLongestMatchAt, isLongestMatchAt_iff_isLongestMatchAt_decide]

theorem revMatchesAt_iff_revMatchesAt_decide {p : Char → Prop} [DecidablePred p] {s : Slice}
    {pos : s.Pos} : RevMatchesAt p pos ↔ RevMatchesAt (decide <| p ·) pos := by
  simp [revMatchesAt_iff_exists_isLongestRevMatchAt, isLongestRevMatchAt_iff_isLongestRevMatchAt_decide]

theorem matchAt?_eq_matchAt?_decide {p : Char → Prop} [DecidablePred p] {s : Slice}
    {pos : s.Pos} : matchAt? p pos = matchAt? (decide <| p ·) pos := by
  ext endPos
  simp [isLongestMatchAt_iff_isLongestMatchAt_decide]

theorem revMatchAt?_eq_revMatchAt?_decide {p : Char → Prop} [DecidablePred p] {s : Slice}
    {pos : s.Pos} : revMatchAt? p pos = revMatchAt? (decide <| p ·) pos := by
  ext startPos
  simp [isLongestRevMatchAt_iff_isLongestRevMatchAt_decide]

theorem skipPrefix?_eq_skipPrefix?_decide {p : Char → Prop} [DecidablePred p] :
    ForwardPattern.skipPrefix? p = ForwardPattern.skipPrefix? (decide <| p ·) := rfl

theorem skipSuffix?_eq_skipSuffix?_decide {p : Char → Prop} [DecidablePred p] :
    BackwardPattern.skipSuffix? p = BackwardPattern.skipSuffix? (decide <| p ·) := rfl

instance {p : Char → Prop} [DecidablePred p] : LawfulForwardPatternModel p where
  skipPrefix?_eq_some_iff {s} pos := by
    rw [skipPrefix?_eq_skipPrefix?_decide, isLongestMatch_iff_isLongestMatch_decide]
    exact LawfulForwardPatternModel.skipPrefix?_eq_some_iff ..

instance {p : Char → Prop} [DecidablePred p] : LawfulBackwardPatternModel p where
  skipSuffix?_eq_some_iff {s} pos := by
    rw [skipSuffix?_eq_skipSuffix?_decide, isLongestRevMatch_iff_isLongestRevMatch_decide]
    exact LawfulBackwardPatternModel.skipSuffix?_eq_some_iff ..

theorem toSearcher_eq {p : Char → Prop} [DecidablePred p] {s : Slice} :
    ToForwardSearcher.toSearcher p s = ToForwardSearcher.toSearcher (decide <| p ·) s := (rfl)

theorem toBackwardSearcher_eq {p : Char → Prop} [DecidablePred p] {s : Slice} :
    ToBackwardSearcher.toSearcher p s = ToBackwardSearcher.toSearcher (decide <| p ·) s := (rfl)

theorem isValidSearchFrom_iff_isValidSearchFrom_decide {p : Char → Prop} [DecidablePred p]
    {s : Slice} {pos : s.Pos} {l : List (SearchStep s)} :
    IsValidSearchFrom p pos l ↔ IsValidSearchFrom (decide <| p ·) pos l := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · induction h with
    | endPos => simpa using IsValidSearchFrom.endPos
    | matched => simp_all [IsValidSearchFrom.matched, isLongestMatchAt_iff_isLongestMatchAt_decide]
    | mismatched => simp_all [IsValidSearchFrom.mismatched, matchesAt_iff_matchesAt_decide]
  · induction h with
    | endPos => simpa using IsValidSearchFrom.endPos
    | matched => simp_all [IsValidSearchFrom.matched, isLongestMatchAt_iff_isLongestMatchAt_decide]
    | mismatched => simp_all [IsValidSearchFrom.mismatched, matchesAt_iff_matchesAt_decide]

theorem isValidRevSearchFrom_iff_isValidRevSearchFrom_decide {p : Char → Prop} [DecidablePred p]
    {s : Slice} {pos : s.Pos} {l : List (SearchStep s)} :
    IsValidRevSearchFrom p pos l ↔ IsValidRevSearchFrom (decide <| p ·) pos l := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · induction h with
    | startPos => simpa using IsValidRevSearchFrom.startPos
    | matched => simp_all [IsValidRevSearchFrom.matched, isLongestRevMatchAt_iff_isLongestRevMatchAt_decide]
    | mismatched => simp_all [IsValidRevSearchFrom.mismatched, revMatchesAt_iff_revMatchesAt_decide]
  · induction h with
    | startPos => simpa using IsValidRevSearchFrom.startPos
    | matched => simp_all [IsValidRevSearchFrom.matched, isLongestRevMatchAt_iff_isLongestRevMatchAt_decide]
    | mismatched => simp_all [IsValidRevSearchFrom.mismatched, revMatchesAt_iff_revMatchesAt_decide]

instance {p : Char → Prop} [DecidablePred p] : LawfulToForwardSearcherModel p where
  isValidSearchFrom_toList s := by
    simpa [toSearcher_eq, isValidSearchFrom_iff_isValidSearchFrom_decide] using
      LawfulToForwardSearcherModel.isValidSearchFrom_toList (pat := (decide <| p ·)) (s := s)

instance {p : Char → Prop} [DecidablePred p] : LawfulToBackwardSearcherModel p where
  isValidRevSearchFrom_toList s := by
    simpa [toBackwardSearcher_eq, isValidRevSearchFrom_iff_isValidRevSearchFrom_decide] using
      LawfulToBackwardSearcherModel.isValidRevSearchFrom_toList (pat := (decide <| p ·)) (s := s)

theorem matchesAt_iff {p : Char → Prop} [DecidablePred p] {s : Slice} {pos : s.Pos} :
    MatchesAt p pos ↔ ∃ (h : pos ≠ s.endPos), p (pos.get h) := by
  simp [matchesAt_iff_exists_isLongestMatchAt, isLongestMatchAt_iff, exists_comm]

theorem revMatchesAt_iff {p : Char → Prop} [DecidablePred p] {s : Slice} {pos : s.Pos} :
    RevMatchesAt p pos ↔ ∃ (h : pos ≠ s.startPos), p ((pos.prev h).get (by simp)) := by
  simp [revMatchesAt_iff_exists_isLongestRevMatchAt, isLongestRevMatchAt_iff, exists_comm]

theorem not_matchesAt_of_get {p : Char → Prop} [DecidablePred p] {s : Slice} {pos : s.Pos}
    {h : pos ≠ s.endPos} (hc : ¬ p (pos.get h)) : ¬ MatchesAt p pos := by
  simp [matchesAt_iff, hc]

theorem not_revMatchesAt_of_get {p : Char → Prop} [DecidablePred p] {s : Slice} {pos : s.Pos}
    {h : pos ≠ s.startPos} (hc : ¬ p ((pos.prev h).get (by simp))) : ¬ RevMatchesAt p pos := by
  simp [revMatchesAt_iff, hc]

theorem matchAt?_eq {s : Slice} {pos : s.Pos} {p : Char → Prop} [DecidablePred p] :
    matchAt? p pos =
      if h₀ : ∃ (h : pos ≠ s.endPos), p (pos.get h) then some (pos.next h₀.1) else none := by
  split <;> simp_all [isLongestMatchAt_iff, matchesAt_iff]

theorem revMatchAt?_eq {s : Slice} {pos : s.Pos} {p : Char → Prop} [DecidablePred p] :
    revMatchAt? p pos =
      if h₀ : ∃ (h : pos ≠ s.startPos), p ((pos.prev h).get (by simp)) then some (pos.prev h₀.1) else none := by
  split <;> simp_all [isLongestRevMatchAt_iff, revMatchesAt_iff]

end Decidable

end Pattern.Model.CharPred

theorem startsWith_prop_eq_startsWith_decide {p : Char → Prop} [DecidablePred p] {s : Slice} :
    s.startsWith p = s.startsWith (decide <| p ·) := (rfl)

theorem dropPrefix?_prop_eq_dropPrefix?_decide {p : Char → Prop} [DecidablePred p] {s : Slice} :
    s.dropPrefix? p = s.dropPrefix? (decide <| p ·) := (rfl)

theorem dropPrefix_prop_eq_dropPrefix_decide {p : Char → Prop} [DecidablePred p] {s : Slice} :
    s.dropPrefix p = s.dropPrefix (decide <| p ·) := (rfl)

theorem skipPrefix?_prop_eq_skipPrefix?_decide {p : Char → Prop} [DecidablePred p] {s : Slice} :
    s.skipPrefix? p = s.skipPrefix? (decide <| p ·) := (rfl)

theorem Pos.skip?_prop_eq_skip?_decide {p : Char → Prop} [DecidablePred p] {s : Slice} {pos : s.Pos} :
    pos.skip? p = pos.skip? (decide <| p ·) := (rfl)

theorem Pattern.ForwardPattern.skipPrefix?_prop_eq_skipPrefix?_decide
    {p : Char → Prop} [DecidablePred p] {s : Slice} :
    skipPrefix? p s = skipPrefix? (decide <| p ·) s := (rfl)

theorem Pos.skipWhile_prop_eq_skipWhile_decide {p : Char → Prop} [DecidablePred p] {s : Slice}
    (curr : s.Pos) :
    Pos.skipWhile curr p = Pos.skipWhile curr (decide <| p ·) := by
  fun_induction Pos.skipWhile curr p with
  | case1 pos nextCurr h₁ h₂ ih =>
    conv => rhs; rw [Pos.skipWhile]
    simp [← Pos.skip?_prop_eq_skip?_decide, h₁, h₂, ih]
  | case2 pos nextCurr h ih =>
    conv => rhs; rw [Pos.skipWhile]
    simp [← Pos.skip?_prop_eq_skip?_decide, h, ih]
  | case3 pos h =>
    conv => rhs; rw [Pos.skipWhile]
    simp [← Pos.skip?_prop_eq_skip?_decide, h]

theorem skipPrefixWhile_prop_eq_skipPrefixWhile_decide {p : Char → Prop} [DecidablePred p]
    {s : Slice} :
    s.skipPrefixWhile p = s.skipPrefixWhile (decide <| p ·) :=
  Pos.skipWhile_prop_eq_skipWhile_decide s.startPos

theorem dropWhile_prop_eq_dropWhile_decide {p : Char → Prop} [DecidablePred p] {s : Slice} :
    s.dropWhile p = s.dropWhile (decide <| p ·) := by
  simp only [dropWhile]; exact congrArg _ skipPrefixWhile_prop_eq_skipPrefixWhile_decide

theorem takeWhile_prop_eq_takeWhile_decide {p : Char → Prop} [DecidablePred p] {s : Slice} :
    s.takeWhile p = s.takeWhile (decide <| p ·) := by
  simp only [takeWhile]; exact congrArg _ skipPrefixWhile_prop_eq_skipPrefixWhile_decide

theorem all_prop_eq_all_decide {p : Char → Prop} [DecidablePred p] {s : Slice} :
    s.all p = s.all (decide <| p ·) := by
  simp only [all, skipPrefixWhile_prop_eq_skipPrefixWhile_decide]

theorem find?_prop_eq_find?_decide {p : Char → Prop} [DecidablePred p] {s : Slice} :
    s.find? p = s.find? (decide <| p ·) :=
  (rfl)

theorem Pos.find?_prop_eq_find?_decide {p : Char → Prop} [DecidablePred p] {s : Slice}
    {pos : s.Pos} :
    pos.find? p = pos.find? (decide <| p ·) :=
  (rfl)

theorem contains_prop_eq_contains_decide {p : Char → Prop} [DecidablePred p] {s : Slice} :
    s.contains p = s.contains (decide <| p ·) :=
  (rfl)

theorem endsWith_prop_eq_endsWith_decide {p : Char → Prop} [DecidablePred p] {s : Slice} :
    s.endsWith p = s.endsWith (decide <| p ·) := (rfl)

theorem skipSuffix?_prop_eq_skipSuffix?_decide {p : Char → Prop} [DecidablePred p] {s : Slice} :
    s.skipSuffix? p = s.skipSuffix? (decide <| p ·) := (rfl)

theorem dropSuffix?_prop_eq_dropSuffix?_decide {p : Char → Prop} [DecidablePred p] {s : Slice} :
    s.dropSuffix? p = s.dropSuffix? (decide <| p ·) := (rfl)

theorem dropSuffix_prop_eq_dropSuffix_decide {p : Char → Prop} [DecidablePred p] {s : Slice} :
    s.dropSuffix p = s.dropSuffix (decide <| p ·) := (rfl)

theorem Pattern.BackwardPattern.skipSuffix?_prop_eq_skipSuffix?_decide
    {p : Char → Prop} [DecidablePred p] {s : Slice} :
    skipSuffix? p s = skipSuffix? (decide <| p ·) s := (rfl)

theorem Pos.revSkip?_prop_eq_revSkip?_decide {p : Char → Prop} [DecidablePred p] {s : Slice} {pos : s.Pos} :
    pos.revSkip? p = pos.revSkip? (decide <| p ·) := (rfl)

theorem Pos.revSkipWhile_prop_eq_revSkipWhile_decide {p : Char → Prop} [DecidablePred p]
    {s : Slice} (curr : s.Pos) :
    Pos.revSkipWhile curr p = Pos.revSkipWhile curr (decide <| p ·) := by
  fun_induction Pos.revSkipWhile curr p with
  | case1 pos nextCurr h₁ h₂ ih =>
    conv => rhs; rw [Pos.revSkipWhile]
    simp [← Pos.revSkip?_prop_eq_revSkip?_decide, h₁, h₂, ih]
  | case2 pos nextCurr h ih =>
    conv => rhs; rw [Pos.revSkipWhile]
    simp [← Pos.revSkip?_prop_eq_revSkip?_decide, h, ih]
  | case3 pos h =>
    conv => rhs; rw [Pos.revSkipWhile]
    simp [← Pos.revSkip?_prop_eq_revSkip?_decide, h]

theorem skipSuffixWhile_prop_eq_skipSuffixWhile_decide {p : Char → Prop} [DecidablePred p]
    {s : Slice} :
    s.skipSuffixWhile p = s.skipSuffixWhile (decide <| p ·) :=
  Pos.revSkipWhile_prop_eq_revSkipWhile_decide s.endPos

theorem dropEndWhile_prop_eq_dropEndWhile_decide {p : Char → Prop} [DecidablePred p]
    {s : Slice} :
    s.dropEndWhile p = s.dropEndWhile (decide <| p ·) := by
  simp only [dropEndWhile]; exact congrArg _ skipSuffixWhile_prop_eq_skipSuffixWhile_decide

theorem takeEndWhile_prop_eq_takeEndWhile_decide {p : Char → Prop} [DecidablePred p]
    {s : Slice} :
    s.takeEndWhile p = s.takeEndWhile (decide <| p ·) := by
  simp only [takeEndWhile]; exact congrArg _ skipSuffixWhile_prop_eq_skipSuffixWhile_decide

theorem revAll_prop_eq_revAll_decide {p : Char → Prop} [DecidablePred p] {s : Slice} :
    s.revAll p = s.revAll (decide <| p ·) := by
  simp only [revAll, skipSuffixWhile_prop_eq_skipSuffixWhile_decide]

end String.Slice
