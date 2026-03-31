/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Markus Himmel
-/
module

prelude
public import Init.Data.String.Slice
public import Init.Data.String.TakeDrop
public import Init.Data.String.Lemmas.Pattern.Basic
import all Init.Data.String.Slice
import all Init.Data.String.TakeDrop
import Init.Data.String.Lemmas.Intercalate
import Init.Data.String.Lemmas.Basic
import Init.Data.String.OrderInstances

public section

open String.Slice Pattern Model

namespace String

namespace Slice

theorem skipPrefix?_eq_forwardPatternSkipPrefix? {ρ : Type} {pat : ρ} [ForwardPattern pat] {s : Slice} :
    s.skipPrefix? pat = ForwardPattern.skipPrefix? pat s := (rfl)

theorem startsWith_eq_forwardPatternStartsWith {ρ : Type} {pat : ρ} [ForwardPattern pat] {s : Slice} :
    s.startsWith pat = ForwardPattern.startsWith pat s := (rfl)

theorem dropPrefix?_eq_map_skipPrefix? {ρ : Type} {pat : ρ} [ForwardPattern pat] {s : Slice} :
    s.dropPrefix? pat = (s.skipPrefix? pat).map s.sliceFrom := (rfl)

theorem Pattern.Model.skipPrefix?_eq_some_iff {ρ : Type} {pat : ρ} [PatternModel pat] [ForwardPattern pat]
    [LawfulForwardPatternModel pat] {s : Slice} {pos : s.Pos} :
    s.skipPrefix? pat = some pos ↔ IsLongestMatch pat pos := by
  rw [skipPrefix?_eq_forwardPatternSkipPrefix?, LawfulForwardPatternModel.skipPrefix?_eq_some_iff]

theorem Pattern.Model.skipPrefix?_eq_none_iff {ρ : Type} {pat : ρ} [PatternModel pat] [ForwardPattern pat]
    [LawfulForwardPatternModel pat] {s : Slice} :
    s.skipPrefix? pat = none ↔ ¬ MatchesAt pat s.startPos := by
  rw [skipPrefix?_eq_forwardPatternSkipPrefix?, LawfulForwardPatternModel.skipPrefix?_eq_none_iff]

@[simp]
theorem isSome_skipPrefix? {ρ : Type} {pat : ρ} [ForwardPattern pat] [LawfulForwardPattern pat] {s : Slice} :
    (s.skipPrefix? pat).isSome = s.startsWith pat := by
  rw [startsWith_eq_forwardPatternStartsWith, skipPrefix?, LawfulForwardPattern.startsWith_eq]

theorem Pattern.Model.startsWith_eq_false_iff {ρ : Type} {pat : ρ} [PatternModel pat] [ForwardPattern pat]
    [LawfulForwardPatternModel pat] {s : Slice} :
    s.startsWith pat = false ↔ ¬ MatchesAt pat s.startPos := by
  rw [← Pattern.Model.skipPrefix?_eq_none_iff, ← Option.isNone_iff_eq_none,
    ← isSome_skipPrefix?, Option.isSome_eq_false_iff]


theorem Pattern.Model.startsWith_iff {ρ : Type} {pat : ρ} [PatternModel pat] [ForwardPattern pat]
    [LawfulForwardPatternModel pat] {s : Slice} :
    s.startsWith pat = true ↔ MatchesAt pat s.startPos := by
  rw [← Bool.not_eq_false, startsWith_eq_false_iff, Classical.not_not]

@[simp]
theorem skipPrefix?_eq_none_iff {ρ : Type} {pat : ρ} [ForwardPattern pat] [LawfulForwardPattern pat]
    {s : Slice} : s.skipPrefix? pat = none ↔ s.startsWith pat = false := by
  rw [← Option.isNone_iff_eq_none, ← Option.isSome_eq_false_iff, isSome_skipPrefix?]

@[simp]
theorem dropPrefix?_eq_none_iff {ρ : Type} {pat : ρ} [ForwardPattern pat] [LawfulForwardPattern pat]
    {s : Slice} : s.dropPrefix? pat = none ↔ s.startsWith pat = false := by
  simp [dropPrefix?_eq_map_skipPrefix?]

theorem Pattern.Model.eq_append_of_dropPrefix?_eq_some {ρ : Type} {pat : ρ} [PatternModel pat] [ForwardPattern pat]
    [LawfulForwardPatternModel pat] {s res : Slice} (h : s.dropPrefix? pat = some res) :
    ∃ t, PatternModel.Matches pat t ∧ s.copy = t ++ res.copy := by
  simp only [dropPrefix?_eq_map_skipPrefix?, Option.map_eq_some_iff, skipPrefix?_eq_some_iff] at h
  obtain ⟨pos, h₁, h₂⟩ := h
  exact ⟨(s.sliceTo pos).copy, h₁.isMatch.matches_copy, by simp [← h₂]⟩

theorem Pos.skip?_eq_map_skipPrefix? {ρ : Type} {pat : ρ} [ForwardPattern pat] {s : Slice} {pos : s.Pos} :
    pos.skip? pat = ((s.sliceFrom pos).skipPrefix? pat).map Pos.ofSliceFrom :=
  (rfl)

theorem Pattern.Model.Pos.skip?_eq_some_iff {ρ : Type} {pat : ρ} [PatternModel pat] [ForwardPattern pat]
    [LawfulForwardPatternModel pat] {s : Slice} {pos res : s.Pos} :
    pos.skip? pat = some res ↔ IsLongestMatchAt pat pos res := by
  simp only [Pos.skip?_eq_map_skipPrefix?, Option.map_eq_some_iff, skipPrefix?_eq_some_iff,
    isLongestMatchAt_iff]
  refine ⟨?_, ?_⟩
  · rintro ⟨p, ⟨h, rfl⟩⟩
    simpa
  · rintro ⟨h, h'⟩
    exact ⟨Pos.sliceFrom _ _ h, by simpa⟩

theorem Pattern.Model.Pos.skip?_eq_none_iff {ρ : Type} {pat : ρ} [PatternModel pat] [ForwardPattern pat]
    [LawfulForwardPatternModel pat] {s : Slice} {pos : s.Pos} :
    pos.skip? pat = none ↔ ¬ MatchesAt pat pos := by
  simp [Pos.skip?_eq_map_skipPrefix?, startsWith_eq_false_iff, matchesAt_iff_matchesAt_ofSliceFrom]

theorem Pattern.Model.Pos.skip?_eq_matchAt? {ρ : Type} {pat : ρ} [PatternModel pat] [ForwardPattern pat]
    [LawfulForwardPatternModel pat] {s : Slice} {pos : s.Pos} :
    pos.skip? pat = matchAt? pat pos :=
  Option.ext (fun res => by simp [Pattern.Model.Pos.skip?_eq_some_iff])

@[simp]
theorem skip?_startPos {ρ : Type} {pat : ρ} [PatternModel pat] [ForwardPattern pat] [LawfulForwardPatternModel pat]
    {s : Slice} : s.startPos.skip? pat = s.skipPrefix? pat :=
  Option.ext (fun pos => by simp [Pattern.Model.skipPrefix?_eq_some_iff, Pattern.Model.Pos.skip?_eq_some_iff])

theorem Pos.skip?_cast {ρ : Type} {pat : ρ} [PatternModel pat] [ForwardPattern pat] [LawfulForwardPatternModel pat]
    {s t : Slice} (hst : s.copy = t.copy) {pos : s.Pos} :
    (pos.cast hst).skip? pat = (pos.skip? pat).map (·.cast hst) := by
  simp [Pattern.Model.Pos.skip?_eq_matchAt?, matchAt?_cast]

theorem Pos.skip?_congr {ρ : Type} {pat : ρ} [PatternModel pat] [ForwardPattern pat] [LawfulForwardPatternModel pat]
    {s t : Slice} (hst : s.copy = t.copy) {pos : s.Pos} :
    pos.skip? pat = ((pos.cast hst).skip? pat).map (·.cast hst.symm) := by
  simp only [skip?_cast, Option.map_map]
  conv => lhs; rw [← Option.map_id_apply (x := pos.skip? pat)]
  congr
  ext; simp

theorem skipPrefix?_congr {ρ : Type} {pat : ρ} [PatternModel pat] [ForwardPattern pat]
    [LawfulForwardPatternModel pat] {s t : Slice} (hst : s.copy = t.copy) :
    s.skipPrefix? pat = (t.skipPrefix? pat).map (·.cast hst.symm) := by
  rw [← skip?_startPos, ← Pos.cast_startPos (hst := hst.symm), Pos.skip?_cast, skip?_startPos]

theorem startsWith_congr {ρ : Type} {pat : ρ} [PatternModel pat] [ForwardPattern pat]
    [LawfulForwardPatternModel pat] {s t : Slice} (hst : s.copy = t.copy) :
    s.startsWith pat = t.startsWith pat := by
  rw [← isSome_skipPrefix?, skipPrefix?_congr hst, Option.isSome_map, isSome_skipPrefix?]

theorem dropPrefix?_congr {ρ : Type} {pat : ρ} [PatternModel pat] [ForwardPattern pat]
    [LawfulForwardPatternModel pat] {s t : Slice} (hst : s.copy = t.copy) :
    (s.dropPrefix? pat).map String.Slice.copy = (t.dropPrefix? pat).map String.Slice.copy := by
  simp only [dropPrefix?_eq_map_skipPrefix?]
  rw [skipPrefix?_congr hst]
  simp only [Option.map_map]
  congr 1
  ext
  simp

theorem Pattern.Model.Pos.skipWhile_eq {ρ : Type} {pat : ρ} [PatternModel pat] [StrictPatternModel pat]
    [ForwardPattern pat] [LawfulForwardPatternModel pat] {s : Slice} {pos : s.Pos} :
    pos.skipWhile pat = (matchAt? pat pos).elim pos (·.skipWhile pat) := by
  fun_induction Pos.skipWhile with
  | case1 pos nextCurr h₁ h₂ ih =>
    rw [Pattern.Model.Pos.skip?_eq_matchAt?] at h₁
    simp [h₁]
  | case2 pos nextCurr h₁ h₂ =>
    rw [Pattern.Model.Pos.skip?_eq_some_iff] at h₁
    exact (h₂ h₁.lt).elim
  | case3 p h =>
    rw [Pattern.Model.Pos.skip?_eq_matchAt?] at h
    simp [h]

theorem Pos.skipWhile_cast {ρ : Type} {pat : ρ} [PatternModel pat] [ForwardPattern pat]
    [LawfulForwardPatternModel pat] {s t : Slice} (hst : s.copy = t.copy) {pos : s.Pos} :
    (pos.cast hst).skipWhile pat = (pos.skipWhile pat).cast hst := by
  fun_induction Pos.skipWhile with
  | case1 pos nextCurr h₁ h₂ ih =>
    rw [← ih, skipWhile]
    simp [skip?_cast, h₁, h₂]
  | case2 pos nextCurr h₁ h₂ =>
    rw [skipWhile]
    simp [skip?_cast, h₁, h₂]
  | case3 p h =>
    rw [skipWhile]
    simp [skip?_cast, h]

theorem Pos.skipWhile_congr {ρ : Type} {pat : ρ} [PatternModel pat] [ForwardPattern pat]
    [LawfulForwardPatternModel pat] {s t : Slice} (hst : s.copy = t.copy) {pos : s.Pos} :
    pos.skipWhile pat = ((pos.cast hst).skipWhile pat).cast hst.symm := by
  simp [Pos.skipWhile_cast]

theorem Pattern.Model.Pos.not_matchesAt_skipWhile {ρ : Type} {pat : ρ} [PatternModel pat]
    [StrictPatternModel pat]
    [ForwardPattern pat] [LawfulForwardPatternModel pat] {s : Slice} {pos : s.Pos} :
    ¬MatchesAt pat (pos.skipWhile pat) := by
  induction pos using WellFounded.induction Pos.wellFounded_gt with | h pos ih
  match hpos : matchAt? pat pos with
  | some nextCurr =>
    rw [skipWhile_eq, hpos]
    simpa using ih _ (matchAt?_eq_some_iff.1 hpos).lt
  | none => rwa [skipWhile_eq, hpos, Option.elim_none, ← matchAt?_eq_none_iff]

theorem Pos.le_skipWhile {ρ : Type} {pat : ρ} [PatternModel pat] [ForwardPattern pat]
    [LawfulForwardPatternModel pat] {s : Slice} {pos : s.Pos} : pos ≤ pos.skipWhile pat := by
  fun_induction Pos.skipWhile with
  | case1 pos nextCurr h₁ h₂ ih => exact Std.le_trans (Std.le_of_lt h₂) ih
  | case2 => simp
  | case3 => simp

theorem Pattern.Model.Pos.skipWhile_eq_self {ρ : Type} {pat : ρ} [PatternModel pat]
    [ForwardPattern pat] [LawfulForwardPatternModel pat] {s : Slice} {pos : s.Pos}
    (h : ¬ MatchesAt pat pos) : pos.skipWhile pat = pos := by
  rw [← matchAt?_eq_none_iff, ← skip?_eq_matchAt?] at h
  rw [Pos.skipWhile, h]

theorem Pattern.Model.Pos.skipWhile_eq_self_iff {ρ : Type} {pat : ρ} [PatternModel pat] [StrictPatternModel pat]
    [ForwardPattern pat] [LawfulForwardPatternModel pat] {s : Slice} {pos : s.Pos} :
    pos.skipWhile pat = pos ↔ ¬MatchesAt pat pos :=
  ⟨fun h => by rw [← h]; exact not_matchesAt_skipWhile, skipWhile_eq_self⟩

theorem Pattern.Model.Pos.exists_eq_of_skipWhile_eq {ρ : Type} {pat : ρ} [PatternModel pat]
    [ForwardPattern pat]
    [LawfulForwardPatternModel pat] {s : Slice} {pos : s.Pos} :
    ∃ (l : List String), (∀ t ∈ l, PatternModel.Matches pat t) ∧ (s.slice pos (pos.skipWhile pat) Pos.le_skipWhile).copy = String.join l := by
  fun_induction Pos.skipWhile with
  | case1 pos nextCurr h₁ h₂ ih =>
    obtain ⟨l, hl₁, hl₂⟩ := ih
    have h₀ := h₁
    rw [skip?_eq_matchAt?, matchAt?_eq_some_iff] at h₁
    refine ⟨(s.slice pos nextCurr h₁.le).copy :: l, ?_, ?_⟩
    · simpa using ⟨h₁.matches_slice, hl₁⟩
    · conv => enter [1, 1, 3]; rw [Pos.skipWhile]; simp only [h₀, h₂, ↓reduceIte]
      simpa [← hl₂] using (Slice.Pos.slice _ _ (nextCurr.skipWhile pat) h₁.le Pos.le_skipWhile).splits.eq_append
  | case2 pos nextCurr h₁ h₂ =>
    suffices pos.skipWhile pat = pos from ⟨[], by simp_all⟩
    rw [Pos.skipWhile]
    simp_all
  | case3 pos h =>
    suffices pos.skipWhile pat = pos from ⟨[], by simp_all⟩
    rw [Pos.skipWhile]
    simp_all

theorem skipPrefixWhile_eq_skipWhile_startPos {ρ : Type} {pat : ρ} [ForwardPattern pat] {s : Slice} :
    s.skipPrefixWhile pat = s.startPos.skipWhile pat :=
  (rfl)

@[simp]
theorem cast_skipPrefixWhile {ρ : Type} {pat : ρ} [PatternModel pat] [ForwardPattern pat]
    [LawfulForwardPatternModel pat] {s t : Slice} (hst : s.copy = t.copy) :
    (s.skipPrefixWhile pat).cast hst = t.skipPrefixWhile pat := by
  simp [skipPrefixWhile_eq_skipWhile_startPos, ← Pos.skipWhile_cast]

theorem Pattern.Model.not_matchesAt_skipPrefixWhile {ρ : Type} {pat : ρ} [PatternModel pat]
    [StrictPatternModel pat]
    [ForwardPattern pat] [LawfulForwardPatternModel pat] {s : Slice} :
    ¬MatchesAt pat (s.skipPrefixWhile pat) := by
  simpa [skipPrefixWhile_eq_skipWhile_startPos] using Pos.not_matchesAt_skipWhile

theorem skipPrefixWhile_eq_startPos {ρ : Type} {pat : ρ} [PatternModel pat]
    [ForwardPattern pat] [LawfulForwardPatternModel pat] {s : Slice} :
    s.startsWith pat = false → s.skipPrefixWhile pat = s.startPos := by
  simpa [skipPrefixWhile_eq_skipWhile_startPos,
    Pattern.Model.startsWith_eq_false_iff] using Pos.skipWhile_eq_self (pat := pat) (pos := s.startPos)

@[simp]
theorem skipPrefixWhile_eq_startPos_iff {ρ : Type} {pat : ρ} [PatternModel pat]
    [StrictPatternModel pat] [ForwardPattern pat] [LawfulForwardPatternModel pat] {s : Slice} :
    s.skipPrefixWhile pat = s.startPos ↔ s.startsWith pat = false := by
  simpa [skipPrefixWhile_eq_skipWhile_startPos, Pattern.Model.startsWith_eq_false_iff] using
    Pos.skipWhile_eq_self_iff (pat := pat) (pos := s.startPos)

theorem Pattern.Model.exists_sliceTo_skipPrefixWhile_eq {ρ : Type} {pat : ρ} [PatternModel pat]
    [ForwardPattern pat] [LawfulForwardPatternModel pat] {s : Slice} :
    ∃ (l : List String), (∀ t ∈ l, PatternModel.Matches pat t) ∧ (s.sliceTo (s.skipPrefixWhile pat)).copy = String.join l := by
  simpa [skipPrefixWhile_eq_skipWhile_startPos] using Pos.exists_eq_of_skipWhile_eq (pos := s.startPos)

theorem dropWhile_eq_sliceFrom_skipPrefixWhile {ρ : Type} {pat : ρ} [ForwardPattern pat] {s : Slice} :
    s.dropWhile pat = s.sliceFrom (s.skipPrefixWhile pat) :=
  (rfl)

theorem dropWhile_congr {ρ : Type} {pat : ρ} [PatternModel pat] [ForwardPattern pat] [LawfulForwardPatternModel pat]
    {s t : Slice} (hst : s.copy = t.copy) : (s.dropWhile pat).copy = (t.dropWhile pat).copy := by
  rw [dropWhile_eq_sliceFrom_skipPrefixWhile, dropWhile_eq_sliceFrom_skipPrefixWhile,
    ← cast_skipPrefixWhile hst, copy_sliceFrom_cast]

@[simp]
theorem startsWith_dropWhile {ρ : Type} {pat : ρ} [PatternModel pat] [StrictPatternModel pat]
    [ForwardPattern pat] [LawfulForwardPatternModel pat] {s : Slice} :
    (s.dropWhile pat).startsWith pat = false := by
  simpa [dropWhile_eq_sliceFrom_skipPrefixWhile, Pattern.Model.startsWith_eq_false_iff,
    matchesAt_iff_matchesAt_ofSliceFrom] using not_matchesAt_skipPrefixWhile

theorem dropWhile_eq_self {ρ : Type} {pat : ρ} [PatternModel pat] [ForwardPattern pat]
    [LawfulForwardPatternModel pat] {s : Slice} (h : s.startsWith pat = false) :
    s.dropWhile pat = s := by
  simpa [dropWhile_eq_sliceFrom_skipPrefixWhile] using skipPrefixWhile_eq_startPos h

@[simp]
theorem dropWhile_eq_self_iff {ρ : Type} {pat : ρ} [PatternModel pat] [StrictPatternModel pat]
    [ForwardPattern pat] [LawfulForwardPatternModel pat] {s : Slice} :
    s.dropWhile pat = s ↔ s.startsWith pat = false := by
  simp [dropWhile_eq_sliceFrom_skipPrefixWhile]

theorem Pattern.Model.exists_eq_append_dropWhile {ρ : Type} {pat : ρ} [PatternModel pat] [ForwardPattern pat]
    [LawfulForwardPatternModel pat] {s : Slice}  :
    ∃ (l : List String), (∀ t ∈ l, PatternModel.Matches pat t) ∧ s.copy = String.join l ++ (s.dropWhile pat).copy := by
  simpa [dropWhile_eq_sliceFrom_skipPrefixWhile, -Slice.sliceTo_append_sliceFrom,
    (s.skipPrefixWhile pat).splits.eq_append] using Pattern.Model.exists_sliceTo_skipPrefixWhile_eq

theorem takeWhile_eq_sliceTo_skipPrefixWhile {ρ : Type} {pat : ρ} [ForwardPattern pat] {s : Slice} :
    s.takeWhile pat = s.sliceTo (s.skipPrefixWhile pat) :=
  (rfl)

theorem takeWhile_append_dropWhile {ρ : Type} {pat : ρ} [PatternModel pat] [ForwardPattern pat]
    [LawfulForwardPattern pat] {s : Slice} : (s.takeWhile pat).copy ++ (s.dropWhile pat).copy = s.copy := by
  simp [takeWhile_eq_sliceTo_skipPrefixWhile, dropWhile_eq_sliceFrom_skipPrefixWhile]

theorem takeWhile_congr {ρ : Type} {pat : ρ} [PatternModel pat] [ForwardPattern pat] [LawfulForwardPatternModel pat]
    {s t : Slice} (hst : s.copy = t.copy) : (s.takeWhile pat).copy = (t.takeWhile pat).copy := by
  rw [takeWhile_eq_sliceTo_skipPrefixWhile, takeWhile_eq_sliceTo_skipPrefixWhile,
    ← cast_skipPrefixWhile hst, copy_sliceTo_cast]

theorem isEmpty_takeWhile_eq_true {ρ : Type} {pat : ρ} [PatternModel pat] [ForwardPattern pat]
    [LawfulForwardPatternModel pat] {s : Slice} (h : s.startsWith pat = false) :
    (s.takeWhile pat).isEmpty = true := by
  simpa [takeWhile_eq_sliceTo_skipPrefixWhile] using skipPrefixWhile_eq_startPos h

@[simp]
theorem isEmpty_takeWhile {ρ : Type} {pat : ρ} [PatternModel pat] [StrictPatternModel pat]
    [ForwardPattern pat] [LawfulForwardPatternModel pat] {s : Slice} :
    (s.takeWhile pat).isEmpty = !s.startsWith pat := by
  rw [Bool.eq_iff_iff]
  simp [takeWhile_eq_sliceTo_skipPrefixWhile]

theorem skipSuffix?_eq_backwardPatternSkipSuffix? {ρ : Type} {pat : ρ} [BackwardPattern pat] {s : Slice} :
    s.skipSuffix? pat = BackwardPattern.skipSuffix? pat s := (rfl)

theorem endsWith_eq_backwardPatternEndsWith {ρ : Type} {pat : ρ} [BackwardPattern pat] {s : Slice} :
    s.endsWith pat = BackwardPattern.endsWith pat s := (rfl)

theorem dropSuffix?_eq_map_skipSuffix? {ρ : Type} {pat : ρ} [BackwardPattern pat] {s : Slice} :
    s.dropSuffix? pat = (s.skipSuffix? pat).map s.sliceTo := (rfl)

theorem Pattern.Model.skipSuffix?_eq_some_iff {ρ : Type} {pat : ρ} [PatternModel pat] [BackwardPattern pat]
    [LawfulBackwardPatternModel pat] {s : Slice} {pos : s.Pos} :
    s.skipSuffix? pat = some pos ↔ IsLongestRevMatch pat pos := by
  rw [skipSuffix?_eq_backwardPatternSkipSuffix?, LawfulBackwardPatternModel.skipSuffix?_eq_some_iff]

theorem Pattern.Model.skipSuffix?_eq_none_iff {ρ : Type} {pat : ρ} [PatternModel pat] [BackwardPattern pat]
    [LawfulBackwardPatternModel pat] {s : Slice} :
    s.skipSuffix? pat = none ↔ ¬ RevMatchesAt pat s.endPos := by
  rw [skipSuffix?_eq_backwardPatternSkipSuffix?, LawfulBackwardPatternModel.skipSuffix?_eq_none_iff]

@[simp]
theorem isSome_skipSuffix? {ρ : Type} {pat : ρ} [BackwardPattern pat] [LawfulBackwardPattern pat] {s : Slice} :
    (s.skipSuffix? pat).isSome = s.endsWith pat := by
  rw [endsWith_eq_backwardPatternEndsWith, skipSuffix?, LawfulBackwardPattern.endsWith_eq]

theorem Pattern.Model.endsWith_eq_false_iff {ρ : Type} {pat : ρ} [PatternModel pat] [BackwardPattern pat]
    [LawfulBackwardPatternModel pat] {s : Slice} :
    s.endsWith pat = false ↔ ¬ RevMatchesAt pat s.endPos := by
  rw [← Pattern.Model.skipSuffix?_eq_none_iff, ← Option.isNone_iff_eq_none,
    ← isSome_skipSuffix?, Option.isSome_eq_false_iff]

theorem Pattern.Model.endsWith_iff {ρ : Type} {pat : ρ} [PatternModel pat] [BackwardPattern pat]
    [LawfulBackwardPatternModel pat] {s : Slice} :
    s.endsWith pat = true ↔ RevMatchesAt pat s.endPos := by
  rw [← Bool.not_eq_false, endsWith_eq_false_iff, Classical.not_not]

@[simp]
theorem skipSuffix?_eq_none_iff {ρ : Type} {pat : ρ} [BackwardPattern pat] [LawfulBackwardPattern pat]
    {s : Slice} : s.skipSuffix? pat = none ↔ s.endsWith pat = false := by
  rw [← Option.isNone_iff_eq_none, ← Option.isSome_eq_false_iff, isSome_skipSuffix?]

@[simp]
theorem dropSuffix?_eq_none_iff {ρ : Type} {pat : ρ} [BackwardPattern pat] [LawfulBackwardPattern pat]
    {s : Slice} : s.dropSuffix? pat = none ↔ s.endsWith pat = false := by
  simp [dropSuffix?_eq_map_skipSuffix?]

theorem Pattern.Model.eq_append_of_dropSuffix?_eq_some {ρ : Type} {pat : ρ} [PatternModel pat] [BackwardPattern pat]
    [LawfulBackwardPatternModel pat] {s res : Slice} (h : s.dropSuffix? pat = some res) :
    ∃ t, PatternModel.Matches pat t ∧ s.copy = res.copy ++ t := by
  simp only [dropSuffix?_eq_map_skipSuffix?, Option.map_eq_some_iff, skipSuffix?_eq_some_iff] at h
  obtain ⟨pos, h₁, h₂⟩ := h
  exact ⟨(s.sliceFrom pos).copy, h₁.isRevMatch.matches_copy, by simp [← h₂]⟩

theorem Pos.revSkip?_eq_map_skipSuffix? {ρ : Type} {pat : ρ} [BackwardPattern pat] {s : Slice} {pos : s.Pos} :
    pos.revSkip? pat = ((s.sliceTo pos).skipSuffix? pat).map Pos.ofSliceTo :=
  (rfl)

theorem Pattern.Model.Pos.revSkip?_eq_some_iff {ρ : Type} {pat : ρ} [PatternModel pat] [BackwardPattern pat]
    [LawfulBackwardPatternModel pat] {s : Slice} {pos res : s.Pos} :
    pos.revSkip? pat = some res ↔ IsLongestRevMatchAt pat res pos := by
  simp only [Pos.revSkip?_eq_map_skipSuffix?, Option.map_eq_some_iff, skipSuffix?_eq_some_iff,
    isLongestRevMatchAt_iff]
  refine ⟨?_, ?_⟩
  · rintro ⟨p, ⟨h, rfl⟩⟩
    simpa
  · rintro ⟨h, h'⟩
    exact ⟨Pos.sliceTo _ _ h, by simpa⟩

theorem Pattern.Model.Pos.revSkip?_eq_none_iff {ρ : Type} {pat : ρ} [PatternModel pat] [BackwardPattern pat]
    [LawfulBackwardPatternModel pat] {s : Slice} {pos : s.Pos} :
    pos.revSkip? pat = none ↔ ¬ RevMatchesAt pat pos := by
  simp [Pos.revSkip?_eq_map_skipSuffix?, endsWith_eq_false_iff, revMatchesAt_iff_revMatchesAt_ofSliceto]

theorem Pattern.Model.Pos.revSkip?_eq_revMatchAt? {ρ : Type} {pat : ρ} [PatternModel pat] [BackwardPattern pat]
    [LawfulBackwardPatternModel pat] {s : Slice} {pos : s.Pos} :
    pos.revSkip? pat = revMatchAt? pat pos :=
  Option.ext (fun res => by simp [Pattern.Model.Pos.revSkip?_eq_some_iff])

@[simp]
theorem revSkip?_endPos {ρ : Type} {pat : ρ} [PatternModel pat] [BackwardPattern pat] [LawfulBackwardPatternModel pat]
    {s : Slice} : s.endPos.revSkip? pat = s.skipSuffix? pat :=
  Option.ext (fun pos => by simp [Pattern.Model.skipSuffix?_eq_some_iff, Pattern.Model.Pos.revSkip?_eq_some_iff])

theorem Pos.revSkip?_cast {ρ : Type} {pat : ρ} [PatternModel pat] [BackwardPattern pat] [LawfulBackwardPatternModel pat]
    {s t : Slice} (hst : s.copy = t.copy) {pos : s.Pos} :
    (pos.cast hst).revSkip? pat = (pos.revSkip? pat).map (·.cast hst) := by
  simp [Pattern.Model.Pos.revSkip?_eq_revMatchAt?, revMatchAt?_cast]

theorem Pos.revSkip?_congr {ρ : Type} {pat : ρ} [PatternModel pat] [BackwardPattern pat] [LawfulBackwardPatternModel pat]
    {s t : Slice} (hst : s.copy = t.copy) {pos : s.Pos} :
    pos.revSkip? pat = ((pos.cast hst).revSkip? pat).map (·.cast hst.symm) := by
  simp only [revSkip?_cast, Option.map_map]
  conv => lhs; rw [← Option.map_id_apply (x := pos.revSkip? pat)]
  congr
  ext; simp

theorem skipSuffix?_congr {ρ : Type} {pat : ρ} [PatternModel pat] [BackwardPattern pat]
    [LawfulBackwardPatternModel pat] {s t : Slice} (hst : s.copy = t.copy) :
    s.skipSuffix? pat = (t.skipSuffix? pat).map (·.cast hst.symm) := by
  rw [← revSkip?_endPos, ← Pos.cast_endPos (hst := hst.symm), Pos.revSkip?_cast, revSkip?_endPos]

theorem endsWith_congr {ρ : Type} {pat : ρ} [PatternModel pat] [BackwardPattern pat]
    [LawfulBackwardPatternModel pat] {s t : Slice} (hst : s.copy = t.copy) :
    s.endsWith pat = t.endsWith pat := by
  rw [← isSome_skipSuffix?, skipSuffix?_congr hst, Option.isSome_map, isSome_skipSuffix?]

theorem dropSuffix?_congr {ρ : Type} {pat : ρ} [PatternModel pat] [BackwardPattern pat]
    [LawfulBackwardPatternModel pat] {s t : Slice} (hst : s.copy = t.copy) :
    (s.dropSuffix? pat).map String.Slice.copy = (t.dropSuffix? pat).map String.Slice.copy := by
  simp only [dropSuffix?_eq_map_skipSuffix?]
  rw [skipSuffix?_congr hst]
  simp only [Option.map_map]
  congr 1
  ext
  simp

theorem Pattern.Model.Pos.revSkipWhile_eq {ρ : Type} {pat : ρ} [PatternModel pat] [StrictPatternModel pat]
    [BackwardPattern pat] [LawfulBackwardPatternModel pat] {s : Slice} {pos : s.Pos} :
    pos.revSkipWhile pat = (revMatchAt? pat pos).elim pos (·.revSkipWhile pat) := by
  fun_induction Pos.revSkipWhile with
  | case1 pos nextCurr h₁ h₂ ih =>
    rw [Pattern.Model.Pos.revSkip?_eq_revMatchAt?] at h₁
    simp [h₁]
  | case2 pos nextCurr h₁ h₂ =>
    rw [Pattern.Model.Pos.revSkip?_eq_some_iff] at h₁
    exact (h₂ h₁.lt).elim
  | case3 p h =>
    rw [Pattern.Model.Pos.revSkip?_eq_revMatchAt?] at h
    simp [h]

theorem Pos.revSkipWhile_cast {ρ : Type} {pat : ρ} [PatternModel pat] [BackwardPattern pat]
    [LawfulBackwardPatternModel pat] {s t : Slice} (hst : s.copy = t.copy) {pos : s.Pos} :
    (pos.cast hst).revSkipWhile pat = (pos.revSkipWhile pat).cast hst := by
  fun_induction Pos.revSkipWhile with
  | case1 pos nextCurr h₁ h₂ ih =>
    rw [← ih, revSkipWhile]
    simp [revSkip?_cast, h₁, h₂]
  | case2 pos nextCurr h₁ h₂ =>
    rw [revSkipWhile]
    simp [revSkip?_cast, h₁, h₂]
  | case3 p h =>
    rw [revSkipWhile]
    simp [revSkip?_cast, h]

theorem Pos.revSkipWhile_congr {ρ : Type} {pat : ρ} [PatternModel pat] [BackwardPattern pat]
    [LawfulBackwardPatternModel pat] {s t : Slice} (hst : s.copy = t.copy) {pos : s.Pos} :
    pos.revSkipWhile pat = ((pos.cast hst).revSkipWhile pat).cast hst.symm := by
  simp [Pos.revSkipWhile_cast]

theorem Pattern.Model.Pos.not_revMatchesAt_revSkipWhile {ρ : Type} {pat : ρ} [PatternModel pat]
    [StrictPatternModel pat]
    [BackwardPattern pat] [LawfulBackwardPatternModel pat] {s : Slice} {pos : s.Pos} :
    ¬RevMatchesAt pat (pos.revSkipWhile pat) := by
  induction pos using WellFounded.induction Pos.wellFounded_lt with | h pos ih
  match hpos : revMatchAt? pat pos with
  | some nextCurr =>
    rw [revSkipWhile_eq, hpos]
    simpa using ih _ (revMatchAt?_eq_some_iff.1 hpos).lt
  | none => rwa [revSkipWhile_eq, hpos, Option.elim_none, ← revMatchAt?_eq_none_iff]

theorem Pos.revSkipWhile_le {ρ : Type} {pat : ρ} [PatternModel pat] [BackwardPattern pat]
    [LawfulBackwardPatternModel pat] {s : Slice} {pos : s.Pos} : pos.revSkipWhile pat ≤ pos := by
  fun_induction Pos.revSkipWhile with
  | case1 pos nextCurr h₁ h₂ ih => exact Std.le_trans ih (Std.le_of_lt h₂)
  | case2 => simp
  | case3 => simp

theorem Pattern.Model.Pos.revSkipWhile_eq_self {ρ : Type} {pat : ρ} [PatternModel pat]
    [BackwardPattern pat] [LawfulBackwardPatternModel pat] {s : Slice} {pos : s.Pos}
    (h : ¬ RevMatchesAt pat pos) : pos.revSkipWhile pat = pos := by
  rw [← revMatchAt?_eq_none_iff, ← revSkip?_eq_revMatchAt?] at h
  rw [Pos.revSkipWhile, h]

theorem Pattern.Model.Pos.revSkipWhile_eq_self_iff {ρ : Type} {pat : ρ} [PatternModel pat] [StrictPatternModel pat]
    [BackwardPattern pat] [LawfulBackwardPatternModel pat] {s : Slice} {pos : s.Pos} :
    pos.revSkipWhile pat = pos ↔ ¬RevMatchesAt pat pos :=
  ⟨fun h => by rw [← h]; exact not_revMatchesAt_revSkipWhile, revSkipWhile_eq_self⟩

theorem Pattern.Model.Pos.exists_eq_of_revSkipWhile_eq {ρ : Type} {pat : ρ} [PatternModel pat]
    [BackwardPattern pat]
    [LawfulBackwardPatternModel pat] {s : Slice} {pos : s.Pos} :
    ∃ (l : List String), (∀ t ∈ l, PatternModel.Matches pat t) ∧ (s.slice (pos.revSkipWhile pat) pos Pos.revSkipWhile_le).copy = String.join l := by
  fun_induction Pos.revSkipWhile with
  | case1 pos nextCurr h₁ h₂ ih =>
    obtain ⟨l, hl₁, hl₂⟩ := ih
    have h₀ := h₁
    rw [revSkip?_eq_revMatchAt?, revMatchAt?_eq_some_iff] at h₁
    refine ⟨l ++ [(s.slice nextCurr pos h₁.le).copy], ?_, ?_⟩
    · rw [List.forall_mem_append, List.forall_mem_cons]
      exact ⟨hl₁, h₁.matches_slice, by simp⟩
    · conv => enter [1, 1, 2]; rw [Pos.revSkipWhile]; simp only [h₀, h₂, ↓reduceIte]
      simpa [← hl₂] using (Slice.Pos.slice _ (nextCurr.revSkipWhile pat) _ Pos.revSkipWhile_le h₁.le).splits.eq_append
  | case2 pos nextCurr h₁ h₂ =>
    suffices pos.revSkipWhile pat = pos from ⟨[], by simp_all⟩
    rw [Pos.revSkipWhile]
    simp_all
  | case3 pos h =>
    suffices pos.revSkipWhile pat = pos from ⟨[], by simp_all⟩
    rw [Pos.revSkipWhile]
    simp_all

theorem skipSuffixWhile_eq_revSkipWhile_endPos {ρ : Type} {pat : ρ} [BackwardPattern pat] {s : Slice} :
    s.skipSuffixWhile pat = s.endPos.revSkipWhile pat :=
  (rfl)

@[simp]
theorem cast_skipSuffixWhile {ρ : Type} {pat : ρ} [PatternModel pat] [BackwardPattern pat]
    [LawfulBackwardPatternModel pat] {s t : Slice} (hst : s.copy = t.copy) :
    (s.skipSuffixWhile pat).cast hst = t.skipSuffixWhile pat := by
  simp [skipSuffixWhile_eq_revSkipWhile_endPos, ← Pos.revSkipWhile_cast]

theorem Pattern.Model.not_revMatchesAt_skipSuffixWhile {ρ : Type} {pat : ρ} [PatternModel pat]
    [StrictPatternModel pat]
    [BackwardPattern pat] [LawfulBackwardPatternModel pat] {s : Slice} :
    ¬RevMatchesAt pat (s.skipSuffixWhile pat) := by
  simpa [skipSuffixWhile_eq_revSkipWhile_endPos] using Pos.not_revMatchesAt_revSkipWhile

theorem skipSuffixWhile_eq_endPos {ρ : Type} {pat : ρ} [PatternModel pat]
    [BackwardPattern pat] [LawfulBackwardPatternModel pat] {s : Slice} :
    s.endsWith pat = false → s.skipSuffixWhile pat = s.endPos := by
  simpa [skipSuffixWhile_eq_revSkipWhile_endPos,
    Pattern.Model.endsWith_eq_false_iff] using Pos.revSkipWhile_eq_self (pat := pat) (pos := s.endPos)

@[simp]
theorem skipSuffixWhile_eq_endPos_iff {ρ : Type} {pat : ρ} [PatternModel pat]
    [StrictPatternModel pat] [BackwardPattern pat] [LawfulBackwardPatternModel pat] {s : Slice} :
    s.skipSuffixWhile pat = s.endPos ↔ s.endsWith pat = false := by
  simpa [skipSuffixWhile_eq_revSkipWhile_endPos, Pattern.Model.endsWith_eq_false_iff] using
    Pos.revSkipWhile_eq_self_iff (pat := pat) (pos := s.endPos)

theorem Pattern.Model.exists_sliceFrom_skipSuffixWhile_eq {ρ : Type} {pat : ρ} [PatternModel pat]
    [BackwardPattern pat] [LawfulBackwardPatternModel pat] {s : Slice} :
    ∃ (l : List String), (∀ t ∈ l, PatternModel.Matches pat t) ∧ (s.sliceFrom (s.skipSuffixWhile pat)).copy = String.join l := by
  simpa [skipSuffixWhile_eq_revSkipWhile_endPos] using Pos.exists_eq_of_revSkipWhile_eq (pos := s.endPos)

theorem dropEndWhile_eq_sliceTo_skipSuffixWhile {ρ : Type} {pat : ρ} [BackwardPattern pat] {s : Slice} :
    s.dropEndWhile pat = s.sliceTo (s.skipSuffixWhile pat) :=
  (rfl)

theorem dropEndWhile_congr {ρ : Type} {pat : ρ} [PatternModel pat] [BackwardPattern pat] [LawfulBackwardPatternModel pat]
    {s t : Slice} (hst : s.copy = t.copy) : (s.dropEndWhile pat).copy = (t.dropEndWhile pat).copy := by
  rw [dropEndWhile_eq_sliceTo_skipSuffixWhile, dropEndWhile_eq_sliceTo_skipSuffixWhile,
    ← cast_skipSuffixWhile hst, copy_sliceTo_cast]

@[simp]
theorem endsWith_dropEndWhile {ρ : Type} {pat : ρ} [PatternModel pat] [StrictPatternModel pat]
    [BackwardPattern pat] [LawfulBackwardPatternModel pat] {s : Slice} :
    (s.dropEndWhile pat).endsWith pat = false := by
  simpa [dropEndWhile_eq_sliceTo_skipSuffixWhile, Pattern.Model.endsWith_eq_false_iff,
    revMatchesAt_iff_revMatchesAt_ofSliceto] using not_revMatchesAt_skipSuffixWhile

theorem dropEndWhile_eq_self {ρ : Type} {pat : ρ} [PatternModel pat] [BackwardPattern pat]
    [LawfulBackwardPatternModel pat] {s : Slice} (h : s.endsWith pat = false) :
    s.dropEndWhile pat = s := by
  simpa [dropEndWhile_eq_sliceTo_skipSuffixWhile] using skipSuffixWhile_eq_endPos h

@[simp]
theorem dropEndWhile_eq_self_iff {ρ : Type} {pat : ρ} [PatternModel pat] [StrictPatternModel pat]
    [BackwardPattern pat] [LawfulBackwardPatternModel pat] {s : Slice} :
    s.dropEndWhile pat = s ↔ s.endsWith pat = false := by
  simp [dropEndWhile_eq_sliceTo_skipSuffixWhile]

theorem Pattern.Model.exists_eq_dropEndWhile_append {ρ : Type} {pat : ρ} [PatternModel pat] [BackwardPattern pat]
    [LawfulBackwardPatternModel pat] {s : Slice} :
    ∃ (l : List String), (∀ t ∈ l, PatternModel.Matches pat t) ∧ s.copy = (s.dropEndWhile pat).copy ++ String.join l := by
  simpa [dropEndWhile_eq_sliceTo_skipSuffixWhile, -Slice.sliceTo_append_sliceFrom,
    (s.skipSuffixWhile pat).splits.eq_append] using Pattern.Model.exists_sliceFrom_skipSuffixWhile_eq

theorem takeEndWhile_eq_sliceFrom_skipSuffixWhile {ρ : Type} {pat : ρ} [BackwardPattern pat] {s : Slice} :
    s.takeEndWhile pat = s.sliceFrom (s.skipSuffixWhile pat) :=
  (rfl)

theorem dropEndWhile_append_takeEndWhile {ρ : Type} {pat : ρ} [PatternModel pat] [BackwardPattern pat]
    [LawfulBackwardPattern pat] {s : Slice} : (s.dropEndWhile pat).copy ++ (s.takeEndWhile pat).copy = s.copy := by
  simp [dropEndWhile_eq_sliceTo_skipSuffixWhile, takeEndWhile_eq_sliceFrom_skipSuffixWhile]

theorem takeEndWhile_congr {ρ : Type} {pat : ρ} [PatternModel pat] [BackwardPattern pat] [LawfulBackwardPatternModel pat]
    {s t : Slice} (hst : s.copy = t.copy) : (s.takeEndWhile pat).copy = (t.takeEndWhile pat).copy := by
  rw [takeEndWhile_eq_sliceFrom_skipSuffixWhile, takeEndWhile_eq_sliceFrom_skipSuffixWhile,
    ← cast_skipSuffixWhile hst, copy_sliceFrom_cast]

theorem isEmpty_takeEndWhile_eq_true {ρ : Type} {pat : ρ} [PatternModel pat] [BackwardPattern pat]
    [LawfulBackwardPatternModel pat] {s : Slice} (h : s.endsWith pat = false) :
    (s.takeEndWhile pat).isEmpty = true := by
  simpa [takeEndWhile_eq_sliceFrom_skipSuffixWhile] using skipSuffixWhile_eq_endPos h

@[simp]
theorem isEmpty_takeEndWhile {ρ : Type} {pat : ρ} [PatternModel pat] [StrictPatternModel pat]
    [BackwardPattern pat] [LawfulBackwardPatternModel pat] {s : Slice} :
    (s.takeEndWhile pat).isEmpty = !s.endsWith pat := by
  rw [Bool.eq_iff_iff]
  simp [takeEndWhile_eq_sliceFrom_skipSuffixWhile]

end Slice

theorem skipPrefix?_eq_skipPrefix?_toSlice {ρ : Type} {pat : ρ} [ForwardPattern pat] {s : String} :
    s.skipPrefix? pat = (s.toSlice.skipPrefix? pat).map Pos.ofToSlice := (rfl)

theorem skipPrefix?_toSlice {ρ : Type} {pat : ρ} [ForwardPattern pat] {s : String} :
    s.toSlice.skipPrefix? pat = (s.skipPrefix? pat).map Pos.toSlice := by
  simp [skipPrefix?_eq_skipPrefix?_toSlice]

theorem Slice.skipPrefix?_copy {ρ : Type} {pat : ρ} [ForwardPattern pat] [PatternModel pat] [LawfulForwardPatternModel pat]
    {s : Slice} : s.copy.skipPrefix? pat = (s.skipPrefix? pat).map Slice.Pos.copy := by
  rw [skipPrefix?_eq_skipPrefix?_toSlice, Slice.skipPrefix?_congr String.copy_toSlice, Option.map_map]
  congr 1
  ext
  simp

theorem startsWith_eq_startsWith_toSlice {ρ : Type} {pat : ρ} [ForwardPattern pat] {s : String} :
    s.startsWith pat = s.toSlice.startsWith pat := (rfl)

@[simp]
theorem startsWith_toSlice {ρ : Type} {pat : ρ} [ForwardPattern pat] {s : String} :
    s.toSlice.startsWith pat = s.startsWith pat := (rfl)

@[simp]
theorem Slice.startsWith_copy {ρ : Type} {pat : ρ} [ForwardPattern pat] [PatternModel pat] [LawfulForwardPatternModel pat]
    {s : Slice} : s.copy.startsWith pat = s.startsWith pat := by
  simpa only [← startsWith_toSlice] using Slice.startsWith_congr (by simp)

theorem dropPrefix?_eq_dropPrefix?_toSlice {ρ : Type} {pat : ρ} [ForwardPattern pat] {s : String} :
    s.dropPrefix? pat = s.toSlice.dropPrefix? pat := (rfl)

@[simp]
theorem dropPrefix?_toSlice {ρ : Type} {pat : ρ} [ForwardPattern pat] {s : String} :
    s.toSlice.dropPrefix? pat = s.dropPrefix? pat := (rfl)

@[simp]
theorem Slice.copy_dropPrefix?_copy {ρ : Type} {pat : ρ} [ForwardPattern pat] [PatternModel pat]
    [LawfulForwardPatternModel pat] {s : Slice} :
    (s.copy.dropPrefix? pat).map String.Slice.copy = (s.dropPrefix? pat).map String.Slice.copy := by
  rw [dropPrefix?_eq_dropPrefix?_toSlice, Slice.dropPrefix?_congr String.copy_toSlice]

theorem skip?_eq_skip?_toSlice {ρ : Type} {pat : ρ} [ForwardPattern pat] {s : String} {pos : s.Pos} :
    pos.skip? pat = (pos.toSlice.skip? pat).map Pos.ofToSlice := (rfl)

theorem skip?_toSlice {ρ : Type} {pat : ρ} [ForwardPattern pat] {s : String} {pos : s.Pos} :
    pos.toSlice.skip? pat = (pos.skip? pat).map Pos.toSlice := by
  simp [skip?_eq_skip?_toSlice]

-- TODO: move
@[simp]
theorem Slice.Pos.cast_toSlice_copy {s : Slice} {pos : s.Pos} :
    pos.copy.toSlice.cast (by simp) = pos := by
  ext; simp

theorem Slice.Pos.skip?_copy {ρ : Type} {pat : ρ} [ForwardPattern pat] [PatternModel pat]
    [LawfulForwardPatternModel pat] {s : Slice} {pos : s.Pos} :
    pos.copy.skip? pat = (pos.skip? pat).map Slice.Pos.copy := by
  rw [skip?_eq_skip?_toSlice, Slice.Pos.skip?_congr (hst := String.copy_toSlice), cast_toSlice_copy, Option.map_map]
  congr 1
  ext
  simp

theorem Pos.skipWhile_eq_skipWhile_toSlice {ρ : Type} {pat : ρ} [ForwardPattern pat] {s : String}
    {pos : s.Pos} : pos.skipWhile pat = Pos.ofToSlice (pos.toSlice.skipWhile pat) := (rfl)

theorem Pos.skipWhile_toSlice {ρ : Type} {pat : ρ} [ForwardPattern pat] {s : String}
    {pos : s.Pos} : pos.toSlice.skipWhile pat = Pos.toSlice (pos.skipWhile pat) := by
  simp [Pos.skipWhile_eq_skipWhile_toSlice]

theorem Slice.Pos.skipWhile_copy {ρ : Type} {pat : ρ} [ForwardPattern pat] [PatternModel pat]
    [LawfulForwardPatternModel pat] {s : Slice}
    {pos : s.Pos} : pos.copy.skipWhile pat = (pos.skipWhile pat).copy := by
  rw [Pos.skipWhile_eq_skipWhile_toSlice, Slice.Pos.skipWhile_congr String.copy_toSlice,
    cast_toSlice_copy]
  ext
  simp

theorem skipPrefixWhile_eq_skipPrefixWhile_toSlice {ρ : Type} {pat : ρ} [ForwardPattern pat] {s : String} :
    s.skipPrefixWhile pat = Pos.ofToSlice (s.toSlice.skipPrefixWhile pat) := (rfl)

theorem skipPrefixWhile_toSlice {ρ : Type} {pat : ρ} [ForwardPattern pat] {s : String} :
    s.toSlice.skipPrefixWhile pat = Pos.toSlice (s.skipPrefixWhile pat) := by
  simp [skipPrefixWhile_eq_skipPrefixWhile_toSlice]

theorem Slice.skipPrefixWhile_copy {ρ : Type} {pat : ρ} [ForwardPattern pat] [PatternModel pat]
    [LawfulForwardPatternModel pat] {s : Slice} :
    s.copy.skipPrefixWhile pat = (s.skipPrefixWhile pat).copy := by
  rw [skipPrefixWhile_eq_skipPrefixWhile_toSlice, ← cast_skipPrefixWhile String.copy_toSlice.symm]
  ext
  simp [-cast_skipPrefixWhile]

theorem dropWhile_eq_dropWhile_toSlice {ρ : Type} {pat : ρ} [ForwardPattern pat] {s : String} :
    s.dropWhile pat = s.toSlice.dropWhile pat := (rfl)

@[simp]
theorem dropWhile_toSlice {ρ : Type} {pat : ρ} [ForwardPattern pat] {s : String} :
    s.toSlice.dropWhile pat = s.dropWhile pat := by
  simp [dropWhile_eq_dropWhile_toSlice]

@[simp]
theorem Slice.dropWhile_copy {ρ : Type} {pat : ρ} [ForwardPattern pat] [PatternModel pat]
    [LawfulForwardPatternModel pat] {s : Slice} :
    (s.copy.dropWhile pat).copy = (s.dropWhile pat).copy := by
  simpa [← dropWhile_toSlice] using Slice.dropWhile_congr (by simp)

theorem takeWhile_eq_takeWhile_toSlice {ρ : Type} {pat : ρ} [ForwardPattern pat] {s : String} :
    s.takeWhile pat = s.toSlice.takeWhile pat := (rfl)

@[simp]
theorem takeWhile_toSlice {ρ : Type} {pat : ρ} [ForwardPattern pat] {s : String} :
    s.toSlice.takeWhile pat = s.takeWhile pat := by
  simp [takeWhile_eq_takeWhile_toSlice]

@[simp]
theorem Slice.takeWhile_copy {ρ : Type} {pat : ρ} [ForwardPattern pat] [PatternModel pat]
    [LawfulForwardPatternModel pat] {s : Slice} :
    (s.copy.takeWhile pat).copy = (s.takeWhile pat).copy := by
  simpa [← takeWhile_toSlice] using Slice.takeWhile_congr (by simp)

theorem skipSuffix?_eq_skipSuffix?_toSlice {ρ : Type} {pat : ρ} [BackwardPattern pat] {s : String} :
    s.skipSuffix? pat = (s.toSlice.skipSuffix? pat).map Pos.ofToSlice := (rfl)

theorem skipSuffix?_toSlice {ρ : Type} {pat : ρ} [BackwardPattern pat] {s : String} :
    s.toSlice.skipSuffix? pat = (s.skipSuffix? pat).map Pos.toSlice := by
  simp [skipSuffix?_eq_skipSuffix?_toSlice]

theorem Slice.skipSuffix?_copy {ρ : Type} {pat : ρ} [BackwardPattern pat] [PatternModel pat] [LawfulBackwardPatternModel pat]
    {s : Slice} : s.copy.skipSuffix? pat = (s.skipSuffix? pat).map Slice.Pos.copy := by
  rw [skipSuffix?_eq_skipSuffix?_toSlice, Slice.skipSuffix?_congr String.copy_toSlice, Option.map_map]
  congr 1
  ext
  simp

theorem endsWith_eq_endsWith_toSlice {ρ : Type} {pat : ρ} [BackwardPattern pat] {s : String} :
    s.endsWith pat = s.toSlice.endsWith pat := (rfl)

@[simp]
theorem endsWith_toSlice {ρ : Type} {pat : ρ} [BackwardPattern pat] {s : String} :
    s.toSlice.endsWith pat = s.endsWith pat := (rfl)

@[simp]
theorem Slice.endsWith_copy {ρ : Type} {pat : ρ} [BackwardPattern pat] [PatternModel pat] [LawfulBackwardPatternModel pat]
    {s : Slice} : s.copy.endsWith pat = s.endsWith pat := by
  simpa only [← endsWith_toSlice] using Slice.endsWith_congr (by simp)

theorem dropSuffix?_eq_dropSuffix?_toSlice {ρ : Type} {pat : ρ} [BackwardPattern pat] {s : String} :
    s.dropSuffix? pat = s.toSlice.dropSuffix? pat := (rfl)

@[simp]
theorem dropSuffix?_toSlice {ρ : Type} {pat : ρ} [BackwardPattern pat] {s : String} :
    s.toSlice.dropSuffix? pat = s.dropSuffix? pat := (rfl)

@[simp]
theorem Slice.copy_dropSuffix?_copy {ρ : Type} {pat : ρ} [BackwardPattern pat] [PatternModel pat]
    [LawfulBackwardPatternModel pat] {s : Slice} :
    (s.copy.dropSuffix? pat).map String.Slice.copy = (s.dropSuffix? pat).map String.Slice.copy := by
  rw [dropSuffix?_eq_dropSuffix?_toSlice, Slice.dropSuffix?_congr String.copy_toSlice]

theorem revSkip?_eq_revSkip?_toSlice {ρ : Type} {pat : ρ} [BackwardPattern pat] {s : String} {pos : s.Pos} :
    pos.revSkip? pat = (pos.toSlice.revSkip? pat).map Pos.ofToSlice := (rfl)

theorem revSkip?_toSlice {ρ : Type} {pat : ρ} [BackwardPattern pat] {s : String} {pos : s.Pos} :
    pos.toSlice.revSkip? pat = (pos.revSkip? pat).map Pos.toSlice := by
  simp [revSkip?_eq_revSkip?_toSlice]

theorem Slice.Pos.revSkip?_copy {ρ : Type} {pat : ρ} [BackwardPattern pat] [PatternModel pat]
    [LawfulBackwardPatternModel pat] {s : Slice} {pos : s.Pos} :
    pos.copy.revSkip? pat = (pos.revSkip? pat).map Slice.Pos.copy := by
  rw [revSkip?_eq_revSkip?_toSlice, Slice.Pos.revSkip?_congr (hst := String.copy_toSlice), cast_toSlice_copy, Option.map_map]
  congr 1
  ext
  simp

theorem Pos.revSkipWhile_eq_revSkipWhile_toSlice {ρ : Type} {pat : ρ} [BackwardPattern pat] {s : String}
    {pos : s.Pos} : pos.revSkipWhile pat = Pos.ofToSlice (pos.toSlice.revSkipWhile pat) := (rfl)

theorem Pos.revSkipWhile_toSlice {ρ : Type} {pat : ρ} [BackwardPattern pat] {s : String}
    {pos : s.Pos} : pos.toSlice.revSkipWhile pat = Pos.toSlice (pos.revSkipWhile pat) := by
  simp [Pos.revSkipWhile_eq_revSkipWhile_toSlice]

theorem Slice.Pos.revSkipWhile_copy {ρ : Type} {pat : ρ} [BackwardPattern pat] [PatternModel pat]
    [LawfulBackwardPatternModel pat] {s : Slice}
    {pos : s.Pos} : pos.copy.revSkipWhile pat = (pos.revSkipWhile pat).copy := by
  rw [Pos.revSkipWhile_eq_revSkipWhile_toSlice, Slice.Pos.revSkipWhile_congr String.copy_toSlice,
    cast_toSlice_copy]
  ext
  simp

theorem skipSuffixWhile_eq_skipSuffixWhile_toSlice {ρ : Type} {pat : ρ} [BackwardPattern pat] {s : String} :
    s.skipSuffixWhile pat = Pos.ofToSlice (s.toSlice.skipSuffixWhile pat) := (rfl)

theorem skipSuffixWhile_toSlice {ρ : Type} {pat : ρ} [BackwardPattern pat] {s : String} :
    s.toSlice.skipSuffixWhile pat = Pos.toSlice (s.skipSuffixWhile pat) := by
  simp [skipSuffixWhile_eq_skipSuffixWhile_toSlice]

theorem Slice.skipSuffixWhile_copy {ρ : Type} {pat : ρ} [BackwardPattern pat] [PatternModel pat]
    [LawfulBackwardPatternModel pat] {s : Slice} :
    s.copy.skipSuffixWhile pat = (s.skipSuffixWhile pat).copy := by
  rw [skipSuffixWhile_eq_skipSuffixWhile_toSlice, ← cast_skipSuffixWhile String.copy_toSlice.symm]
  ext
  simp [-cast_skipSuffixWhile]

theorem dropEndWhile_eq_dropEndWhile_toSlice {ρ : Type} {pat : ρ} [BackwardPattern pat] {s : String} :
    s.dropEndWhile pat = s.toSlice.dropEndWhile pat := (rfl)

@[simp]
theorem dropEndWhile_toSlice {ρ : Type} {pat : ρ} [BackwardPattern pat] {s : String} :
    s.toSlice.dropEndWhile pat = s.dropEndWhile pat := by
  simp [dropEndWhile_eq_dropEndWhile_toSlice]

@[simp]
theorem Slice.dropEndWhile_copy {ρ : Type} {pat : ρ} [BackwardPattern pat] [PatternModel pat]
    [LawfulBackwardPatternModel pat] {s : Slice} :
    (s.copy.dropEndWhile pat).copy = (s.dropEndWhile pat).copy := by
  simpa [← dropEndWhile_toSlice] using Slice.dropEndWhile_congr (by simp)

theorem takeEndWhile_eq_takeEndWhile_toSlice {ρ : Type} {pat : ρ} [BackwardPattern pat] {s : String} :
    s.takeEndWhile pat = s.toSlice.takeEndWhile pat := (rfl)

@[simp]
theorem takeEndWhile_toSlice {ρ : Type} {pat : ρ} [BackwardPattern pat] {s : String} :
    s.toSlice.takeEndWhile pat = s.takeEndWhile pat := by
  simp [takeEndWhile_eq_takeEndWhile_toSlice]

@[simp]
theorem Slice.takeEndWhile_copy {ρ : Type} {pat : ρ} [BackwardPattern pat] [PatternModel pat]
    [LawfulBackwardPatternModel pat] {s : Slice} :
    (s.copy.takeEndWhile pat).copy = (s.takeEndWhile pat).copy := by
  simpa [← takeEndWhile_toSlice] using Slice.takeEndWhile_congr (by simp)

namespace Slice

theorem Pattern.Model.exists_of_takeWhile_eq {ρ : Type} {pat : ρ} [PatternModel pat] [ForwardPattern pat]
    [LawfulForwardPatternModel pat] {s : Slice} :
    ∃ (l : List String), (∀ t ∈ l, PatternModel.Matches pat t) ∧ (s.takeWhile pat).copy = String.join l := by
  simpa [takeWhile_eq_sliceTo_skipPrefixWhile] using exists_sliceTo_skipPrefixWhile_eq

theorem Pattern.Model.exists_of_takeEndWhile_eq {ρ : Type} {pat : ρ} [PatternModel pat] [BackwardPattern pat]
    [LawfulBackwardPatternModel pat] {s : Slice} :
    ∃ (l : List String), (∀ t ∈ l, PatternModel.Matches pat t) ∧ (s.takeEndWhile pat).copy = String.join l := by
  simpa [takeEndWhile_eq_sliceFrom_skipSuffixWhile] using exists_sliceFrom_skipSuffixWhile_eq

end Slice

end String
