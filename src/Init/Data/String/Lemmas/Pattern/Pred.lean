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
import Init.Omega

public section

namespace String.Slice.Pattern.Model.CharPred

instance {p : Char → Bool} : ForwardPatternModel p where
  Matches s := ∃ c, s = singleton c ∧ p c
  not_matches_empty := by
    simp

instance {p : Char → Bool} : NoPrefixForwardPatternModel p :=
  .of_length_eq (by simp +contextual [ForwardPatternModel.Matches])

theorem isMatch_iff {p : Char → Bool} {s : Slice} {pos : s.Pos} :
    IsMatch p pos ↔
      ∃ (h : s.startPos ≠ s.endPos), pos = s.startPos.next h ∧ p (s.startPos.get h) := by
  simp only [Model.isMatch_iff, ForwardPatternModel.Matches, sliceTo_copy_eq_iff_exists_splits]
  refine ⟨?_, ?_⟩
  · simp only [splits_singleton_iff]
    refine fun ⟨c, ⟨t₂, h, h₁, h₂, h₃⟩, hc⟩ => ⟨h, h₁, h₂ ▸ hc⟩
  · rintro ⟨h, rfl, h'⟩
    exact ⟨s.startPos.get h, ⟨_, Slice.splits_next_startPos⟩, h'⟩

theorem isLongestMatch_iff {p : Char → Bool} {s : Slice} {pos : s.Pos} :
    IsLongestMatch p pos ↔
      ∃ (h : s.startPos ≠ s.endPos), pos = s.startPos.next h ∧ p (s.startPos.get h) := by
  rw [isLongestMatch_iff_isMatch, isMatch_iff]

theorem isLongestMatchAt_iff {p : Char → Bool} {s : Slice} {pos pos' : s.Pos} :
    IsLongestMatchAt p pos pos' ↔ ∃ h, pos' = pos.next h ∧ p (pos.get h) := by
  simp +contextual [Model.isLongestMatchAt_iff, isLongestMatch_iff, ← Pos.ofSliceFrom_inj,
    Pos.get_eq_get_ofSliceFrom, Pos.ofSliceFrom_next]

theorem isLongestMatchAt_of_get {p : Char → Bool} {s : Slice} {pos : s.Pos} {h : pos ≠ s.endPos}
    (hc : p (pos.get h)) : IsLongestMatchAt p pos (pos.next h) :=
  isLongestMatchAt_iff.2 ⟨h, by simp [hc]⟩

instance {p : Char → Bool} : LawfulForwardPatternModel p where
  skipPrefix?_eq_some_iff {s} pos := by
    simp [isLongestMatch_iff, ForwardPattern.skipPrefix?, and_comm, eq_comm (b := pos)]

instance {p : Char → Bool} : LawfulToForwardSearcherModel p :=
  .defaultImplementation

theorem matchesAt_iff {p : Char → Bool} {s : Slice} {pos : s.Pos} :
    MatchesAt p pos ↔ ∃ (h : pos ≠ s.endPos), p (pos.get h) := by
  simp [matchesAt_iff_exists_isLongestMatchAt, isLongestMatchAt_iff, exists_comm]

theorem not_matchesAt_of_get {p : Char → Bool} {s : Slice} {pos : s.Pos} {h : pos ≠ s.endPos}
    (hc : p (pos.get h) = false) : ¬ MatchesAt p pos := by
  simp [matchesAt_iff, hc]

theorem matchAt?_eq {s : Slice} {pos : s.Pos} {p : Char → Bool} :
    matchAt? p pos =
      if h₀ : ∃ (h : pos ≠ s.endPos), p (pos.get h) then some (pos.next h₀.1) else none := by
  split <;> simp_all [isLongestMatchAt_iff, matchesAt_iff]

namespace Decidable

instance {p : Char → Prop} [DecidablePred p] : ForwardPatternModel p where
  Matches := ForwardPatternModel.Matches (decide <| p ·)
  not_matches_empty := ForwardPatternModel.not_matches_empty (pat := (decide <| p ·))

instance {p : Char → Prop} [DecidablePred p] : NoPrefixForwardPatternModel p where
  eq_empty := NoPrefixForwardPatternModel.eq_empty (pat := (decide <| p ·))

theorem isMatch_iff_isMatch_decide {p : Char → Prop} [DecidablePred p] {s : Slice} {pos : s.Pos} :
    IsMatch p pos ↔ IsMatch (decide <| p ·) pos :=
  ⟨fun ⟨h⟩ => ⟨h⟩, fun ⟨h⟩ => ⟨h⟩⟩

theorem isMatch_iff {p : Char → Prop} [DecidablePred p] {s : Slice} {pos : s.Pos} :
    IsMatch p pos ↔
      ∃ (h : s.startPos ≠ s.endPos), pos = s.startPos.next h ∧ p (s.startPos.get h) := by
  simp [isMatch_iff_isMatch_decide, CharPred.isMatch_iff]

theorem isLongestMatch_iff {p : Char → Prop} [DecidablePred p] {s : Slice} {pos : s.Pos} :
    IsLongestMatch p pos ↔
      ∃ (h : s.startPos ≠ s.endPos), pos = s.startPos.next h ∧ p (s.startPos.get h) := by
  rw [isLongestMatch_iff_isMatch, isMatch_iff]

theorem isLongestMatch_iff_isLongestMatch_decide {p : Char → Prop} [DecidablePred p] {s : Slice}
    {pos : s.Pos} : IsLongestMatch p pos ↔ IsLongestMatch (decide <| p ·) pos := by
  simp [isLongestMatch_iff_isMatch, isMatch_iff_isMatch_decide]

theorem isLongestMatchAt_iff_isLongestMatchAt_decide {p : Char → Prop} [DecidablePred p]
    {s : Slice} {pos pos' : s.Pos} :
    IsLongestMatchAt p pos pos' ↔ IsLongestMatchAt (decide <| p ·) pos pos' := by
  simp [Model.isLongestMatchAt_iff, isLongestMatch_iff_isLongestMatch_decide]

theorem isLongestMatchAt_iff {p : Char → Prop} [DecidablePred p] {s : Slice}
    {pos pos' : s.Pos} :
    IsLongestMatchAt p pos pos' ↔ ∃ h, pos' = pos.next h ∧ p (pos.get h) := by
  simp [isLongestMatchAt_iff_isLongestMatchAt_decide, CharPred.isLongestMatchAt_iff]

theorem isLongestMatchAt_of_get {p : Char → Prop} [DecidablePred p] {s : Slice} {pos : s.Pos}
    {h : pos ≠ s.endPos} (hc : p (pos.get h)) : IsLongestMatchAt p pos (pos.next h) :=
  isLongestMatchAt_iff.2 ⟨h, by simp [hc]⟩

theorem matchesAt_iff_matchesAt_decide {p : Char → Prop} [DecidablePred p] {s : Slice}
    {pos : s.Pos} : MatchesAt p pos ↔ MatchesAt (decide <| p ·) pos := by
  simp [matchesAt_iff_exists_isLongestMatchAt, isLongestMatchAt_iff_isLongestMatchAt_decide]

theorem matchAt?_eq_matchAt?_decide {p : Char → Prop} [DecidablePred p] {s : Slice}
    {pos : s.Pos} : matchAt? p pos = matchAt? (decide <| p ·) pos := by
  ext endPos
  simp [isLongestMatchAt_iff_isLongestMatchAt_decide]

theorem skipPrefix?_eq_skipPrefix?_decide {p : Char → Prop} [DecidablePred p] :
    ForwardPattern.skipPrefix? p = ForwardPattern.skipPrefix? (decide <| p ·) := rfl

instance {p : Char → Prop} [DecidablePred p] : LawfulForwardPatternModel p where
  skipPrefix?_eq_some_iff {s} pos := by
    rw [skipPrefix?_eq_skipPrefix?_decide, isLongestMatch_iff_isLongestMatch_decide]
    exact LawfulForwardPatternModel.skipPrefix?_eq_some_iff ..

theorem toSearcher_eq {p : Char → Prop} [DecidablePred p] {s : Slice} :
    ToForwardSearcher.toSearcher p s = ToForwardSearcher.toSearcher (decide <| p ·) s := (rfl)

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

instance {p : Char → Prop} [DecidablePred p] : LawfulToForwardSearcherModel p where
  isValidSearchFrom_toList s := by
    simpa [toSearcher_eq, isValidSearchFrom_iff_isValidSearchFrom_decide] using
      LawfulToForwardSearcherModel.isValidSearchFrom_toList (pat := (decide <| p ·)) (s := s)

theorem matchesAt_iff {p : Char → Prop} [DecidablePred p] {s : Slice} {pos : s.Pos} :
    MatchesAt p pos ↔ ∃ (h : pos ≠ s.endPos), p (pos.get h) := by
  simp [matchesAt_iff_exists_isLongestMatchAt, isLongestMatchAt_iff, exists_comm]

theorem not_matchesAt_of_get {p : Char → Prop} [DecidablePred p] {s : Slice} {pos : s.Pos}
    {h : pos ≠ s.endPos} (hc : ¬ p (pos.get h)) : ¬ MatchesAt p pos := by
  simp [matchesAt_iff, hc]

theorem matchAt?_eq {s : Slice} {pos : s.Pos} {p : Char → Prop} [DecidablePred p] :
    matchAt? p pos =
      if h₀ : ∃ (h : pos ≠ s.endPos), p (pos.get h) then some (pos.next h₀.1) else none := by
  split <;> simp_all [isLongestMatchAt_iff, matchesAt_iff]

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

theorem Pattern.ForwardPattern.skipPrefix?_prop_eq_skipPrefix?_decide
    {p : Char → Prop} [DecidablePred p] {s : Slice} :
    skipPrefix? p s = skipPrefix? (decide <| p ·) s := (rfl)

theorem Pos.skipWhile_prop_eq_skipWhile_decide {p : Char → Prop} [DecidablePred p] {s : Slice}
    (curr : s.Pos) :
    Pos.skipWhile curr p = Pos.skipWhile curr (decide <| p ·) := by
  fun_induction Pos.skipWhile curr p with
  | case1 pos nextCurr h₁ h₂ ih =>
    conv => rhs; rw [Pos.skipWhile]
    simp [← Pattern.ForwardPattern.skipPrefix?_prop_eq_skipPrefix?_decide, h₁, h₂, ih]
  | case2 pos nextCurr h ih =>
    conv => rhs; rw [Pos.skipWhile]
    simp [← Pattern.ForwardPattern.skipPrefix?_prop_eq_skipPrefix?_decide, h, ih]
  | case3 pos h =>
    conv => rhs; rw [Pos.skipWhile]
    simp [← Pattern.ForwardPattern.skipPrefix?_prop_eq_skipPrefix?_decide]

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
  simp only [all, dropWhile_prop_eq_dropWhile_decide]

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

theorem Pos.revSkipWhile_prop_eq_revSkipWhile_decide {p : Char → Prop} [DecidablePred p]
    {s : Slice} (curr : s.Pos) :
    Pos.revSkipWhile curr p = Pos.revSkipWhile curr (decide <| p ·) := by
  fun_induction Pos.revSkipWhile curr p with
  | case1 pos nextCurr h₁ h₂ ih =>
    conv => rhs; rw [Pos.revSkipWhile]
    simp [← Pattern.BackwardPattern.skipSuffix?_prop_eq_skipSuffix?_decide, h₁, h₂, ih]
  | case2 pos nextCurr h ih =>
    conv => rhs; rw [Pos.revSkipWhile]
    simp [← Pattern.BackwardPattern.skipSuffix?_prop_eq_skipSuffix?_decide, h, ih]
  | case3 pos h =>
    conv => rhs; rw [Pos.revSkipWhile]
    simp [← Pattern.BackwardPattern.skipSuffix?_prop_eq_skipSuffix?_decide]

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

end String.Slice
