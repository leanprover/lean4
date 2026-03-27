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
  exact ⟨(s.sliceTo pos).copy, h₁.isMatch.matches_copy, by simp [← h₂, ← copy_eq_copy_sliceTo]⟩

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

theorem Pattern.Model.Pos.exists_eq_of_skipWhile_eq {ρ : Type} {pat : ρ} [PatternModel pat] [StrictPatternModel pat]
    [ForwardPattern pat]
    [LawfulForwardPatternModel pat] {s : Slice} {pos res : s.Pos} (h : pos.skipWhile pat = res) :
    ∃ (l : List String),
      (∀ t ∈ l, PatternModel.Matches pat t) ∧ ¬MatchesAt pat res ∧ (s.sliceFrom pos).copy = String.join l ++ (s.sliceFrom res).copy := by
  subst h
  induction pos using WellFounded.induction Pos.wellFounded_gt with | h pos ih
  match hpos : matchAt? pat pos with
  | some nextCurr =>
    rw [skipWhile_eq]
    simp only [hpos, Option.elim_some]
    rw [matchAt?_eq_some_iff] at hpos
    obtain ⟨l, hl₁, hl₂, hl₃⟩ := ih nextCurr hpos.lt
    refine ⟨(s.slice pos nextCurr hpos.le).copy :: l, ?_, hl₂, ?_⟩
    · simpa only [List.mem_cons, forall_eq_or_imp] using ⟨hpos.matches_slice, hl₁⟩
    · simpa [String.append_assoc, ← hl₃] using (Slice.Pos.sliceFrom _ _ hpos.le).splits.eq_append
  | none =>
    rw [skipWhile_eq]
    simpa [hpos] using ⟨[], by simp, by simpa using hpos, by simp⟩

theorem skipPrefixWhile_eq_skipWhile_startPos {ρ : Type} {pat : ρ} [ForwardPattern pat] {s : Slice} :
    s.skipPrefixWhile pat = s.startPos.skipWhile pat :=
  (rfl)

@[simp]
theorem cast_skipPrefixWhile {ρ : Type} {pat : ρ} [PatternModel pat] [ForwardPattern pat]
    [LawfulForwardPatternModel pat] {s t : Slice} (hst : s.copy = t.copy) :
    (s.skipPrefixWhile pat).cast hst = t.skipPrefixWhile pat := by
  simp [skipPrefixWhile_eq_skipWhile_startPos, ← Pos.skipWhile_cast]

theorem Pattern.Model.exists_eq_of_skipPrefixWhile_eq {ρ : Type} {pat : ρ} [PatternModel pat] [StrictPatternModel pat] [ForwardPattern pat]
    [LawfulForwardPatternModel pat] {s : Slice} {res : s.Pos} (h : s.skipPrefixWhile pat = res) :
    ∃ (l : List String),
      (∀ t ∈ l, PatternModel.Matches pat t) ∧ ¬MatchesAt pat res ∧ s.copy = String.join l ++ (s.sliceFrom res).copy := by
  rw [skipPrefixWhile_eq_skipWhile_startPos] at h
  simpa using Pos.exists_eq_of_skipWhile_eq h

theorem dropWhile_eq_sliceFrom_skipPrefixWhile {ρ : Type} {pat : ρ} [ForwardPattern pat] {s : Slice} :
    s.dropWhile pat = s.sliceFrom (s.skipPrefixWhile pat) :=
  (rfl)

theorem dropWhile_congr {ρ : Type} {pat : ρ} [PatternModel pat] [ForwardPattern pat] [LawfulForwardPatternModel pat]
    {s t : Slice} (hst : s.copy = t.copy) : (s.dropWhile pat).copy = (t.dropWhile pat).copy := by
  rw [dropWhile_eq_sliceFrom_skipPrefixWhile, dropWhile_eq_sliceFrom_skipPrefixWhile,
    ← cast_skipPrefixWhile hst, copy_sliceFrom_cast]

theorem Pattern.Model.exists_of_dropWhile_eq {ρ : Type} {pat : ρ} [PatternModel pat] [StrictPatternModel pat] [ForwardPattern pat]
    [LawfulForwardPatternModel pat] {s res : Slice} (h : s.dropWhile pat = res) :
    ∃ (l : List String), (∀ t ∈ l, PatternModel.Matches pat t) ∧ res.startsWith pat = false ∧ s.copy = String.join l ++ res.copy := by
  subst res
  simpa [dropWhile_eq_sliceFrom_skipPrefixWhile, Pattern.Model.startsWith_eq_false_iff,
    matchesAt_iff_matchesAt_ofSliceFrom] using exists_eq_of_skipPrefixWhile_eq (rfl : s.skipPrefixWhile pat = _)

theorem takeWhile_eq_sliceTo_skipPrefixWhile {ρ : Type} {pat : ρ} [ForwardPattern pat] {s : Slice} :
    s.takeWhile pat = s.sliceTo (s.skipPrefixWhile pat) :=
  (rfl)

theorem takeWhile_congr {ρ : Type} {pat : ρ} [PatternModel pat] [ForwardPattern pat] [LawfulForwardPatternModel pat]
    {s t : Slice} (hst : s.copy = t.copy) : (s.takeWhile pat).copy = (t.takeWhile pat).copy := by
  rw [takeWhile_eq_sliceTo_skipPrefixWhile, takeWhile_eq_sliceTo_skipPrefixWhile,
    ← cast_skipPrefixWhile hst, copy_sliceTo_cast]

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
  exact ⟨(s.sliceFrom pos).copy, h₁.isRevMatch.matches_copy, by simp [← h₂, ← copy_eq_copy_sliceTo]⟩

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

theorem endsWith_eq_endsWith_toSlice {ρ : Type} {pat : ρ} [BackwardPattern pat] {s : String} :
    s.endsWith pat = s.toSlice.endsWith pat := (rfl)

theorem dropSuffix?_eq_dropSuffix?_toSlice {ρ : Type} {pat : ρ} [BackwardPattern pat] {s : String} :
    s.dropSuffix? pat = s.toSlice.dropSuffix? pat := (rfl)

namespace Slice

theorem Pattern.Model.exists_of_takeWhile_eq {ρ : Type} {pat : ρ} [PatternModel pat] [StrictPatternModel pat] [ForwardPattern pat]
    [LawfulForwardPatternModel pat] {s res : Slice} (h : s.takeWhile pat = res) :
    ∃ (l : List String) (r : String), (∀ t ∈ l, PatternModel.Matches pat t) ∧ r.startsWith pat = false ∧ res.copy = String.join l ∧ s.copy = res.copy ++ r := by
  subst res
  obtain ⟨t, ht₁, ht₂, ht₃⟩ := exists_eq_of_skipPrefixWhile_eq (rfl : s.skipPrefixWhile pat = _)
  simp only [takeWhile_eq_sliceTo_skipPrefixWhile, exists_and_left]
  refine ⟨t, ht₁, (s.sliceFrom (s.skipPrefixWhile pat)).copy, ?_, ?_, (s.skipPrefixWhile pat).splits.eq_append⟩
  · simpa [startsWith_eq_false_iff, matchesAt_iff_matchesAt_ofSliceFrom]
  · simpa [(s.skipPrefixWhile pat).splits.eq_append] using ht₃

end Slice

end String
