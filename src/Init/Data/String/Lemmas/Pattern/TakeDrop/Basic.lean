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
import Init.Data.String.Lemmas.Order
import Init.Data.String.Lemmas.Basic
import Init.Data.String.OrderInstances
import Init.ByCases

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

theorem Pattern.Model.Pos.skipWhile_eq_self {ρ : Type} {pat : ρ} [PatternModel pat]
    [ForwardPattern pat] [LawfulForwardPatternModel pat] {s : Slice} {pos : s.Pos}
    (h : ¬ MatchesAt pat pos) : pos.skipWhile pat = pos := by
  rw [← matchAt?_eq_none_iff, ← skip?_eq_matchAt?] at h
  rw [Pos.skipWhile, h]

theorem Pattern.Model.Pos.skipWhile_eq_iff {ρ : Type} (pat : ρ) [PatternModel pat]
    [ForwardPattern pat] [LawfulForwardPatternModel pat] {s : Slice} (startPos endPos : s.Pos) :
    startPos.skipWhile pat = endPos ↔ IsLongestMatchAtChain pat startPos endPos ∧
      (¬MatchesAt pat endPos ∨ IsLongestMatchAt pat endPos endPos) := by
  fun_induction Pos.skipWhile with
  | case1 pos nextCurr h₁ h₂ ih =>
    rw [skip?_eq_matchAt?, matchAt?_eq_some_iff] at h₁
    refine ih.trans ⟨fun ⟨hx, hy⟩ => ⟨.cons _ _ _ h₁ hx, hy⟩, fun ⟨hx, hy⟩ => ⟨?_, hy⟩⟩
    cases hx with
    | nil =>
      refine hy.elim (fun h => (h h₁.matchesAt).elim) (fun h => ?_)
      obtain rfl := h₁.eq h
      exact .nil _
    | cons _ mid _ hx hy' =>
      obtain rfl := hx.eq h₁
      exact hy'
  | case2 pos nextCurr h₁ h₂ =>
    rw [skip?_eq_matchAt?, matchAt?_eq_some_iff] at h₁
    obtain rfl := Std.le_antisymm h₁.le (Std.not_lt.1 h₂)
    refine ⟨?_, fun ⟨hx, hy⟩ => ?_⟩
    · rintro rfl
      exact ⟨.nil _, Or.inr h₁⟩
    · exact hx.eq_of_isLongestMatchAt_self h₁
  | case3 pos h =>
    rw [skip?_eq_matchAt?, matchAt?_eq_none_iff] at h
    refine ⟨?_, ?_⟩
    · rintro rfl
      exact ⟨.nil _, Or.inl h⟩
    · rintro ⟨(_|⟨_, mid, hx, hy, hz⟩), -⟩
      · rfl
      · exact (h hy.matchesAt).elim

theorem Pattern.Model.Pos.isLongestMatchAtChain_skipWhile {ρ : Type} (pat : ρ) [PatternModel pat]
    [ForwardPattern pat] [LawfulForwardPatternModel pat] {s : Slice} (pos : s.Pos) :
    IsLongestMatchAtChain pat pos (pos.skipWhile pat) :=
  ((skipWhile_eq_iff pat pos _).1 rfl).1

theorem Pattern.Model.Pos.not_matchesAt_or_isLongestMatchAt_skipWhile {ρ : Type} (pat : ρ)
    [PatternModel pat] [ForwardPattern pat] [LawfulForwardPatternModel pat] {s : Slice} (pos : s.Pos) :
    ¬ MatchesAt pat (pos.skipWhile pat) ∨ IsLongestMatchAt pat (pos.skipWhile pat) (pos.skipWhile pat) :=
  ((skipWhile_eq_iff pat pos _).1 rfl).2

theorem Pattern.Model.Pos.not_matchesAt_skipWhile {ρ : Type} (pat : ρ) [PatternModel pat]
    [StrictPatternModel pat]
    [ForwardPattern pat] [LawfulForwardPatternModel pat] {s : Slice} (pos : s.Pos) :
    ¬MatchesAt pat (pos.skipWhile pat) := by
  simpa using not_matchesAt_or_isLongestMatchAt_skipWhile pat pos

theorem Pattern.Model.Pos.skipWhile_eq_self_iff {ρ : Type} {pat : ρ} [PatternModel pat] [StrictPatternModel pat]
    [ForwardPattern pat] [LawfulForwardPatternModel pat] {s : Slice} {pos : s.Pos} :
    pos.skipWhile pat = pos ↔ ¬MatchesAt pat pos := by
  simp [skipWhile_eq_iff]

theorem Pattern.Model.Pos.skipWhile_eq_self_iff_or {ρ : Type} {pat : ρ} [PatternModel pat]
    [ForwardPattern pat] [LawfulForwardPatternModel pat] {s : Slice} {pos : s.Pos} :
    pos.skipWhile pat = pos ↔ ¬MatchesAt pat pos ∨ IsLongestMatchAt pat pos pos := by
  simp [skipWhile_eq_iff]

@[simp]
theorem Pos.le_skipWhile {ρ : Type} {pat : ρ} [PatternModel pat] [ForwardPattern pat]
    [LawfulForwardPatternModel pat] {s : Slice} {pos : s.Pos} : pos ≤ pos.skipWhile pat :=
  (Pattern.Model.Pos.isLongestMatchAtChain_skipWhile pat pos).le

theorem Pattern.Model.Pos.le_skipWhile_of_isLongestMatchAtChain {ρ : Type} (pat : ρ) [PatternModel pat]
    [ForwardPattern pat] [LawfulForwardPatternModel pat] {s : Slice} {startPos endPos : s.Pos}
    (h : IsLongestMatchAtChain pat startPos endPos) : endPos ≤ startPos.skipWhile pat := by
  induction h with
  | nil p => exact Pos.le_skipWhile
  | cons p₁ p₂ p₃ h₁ h₂ ih =>
    rw [Pos.skipWhile]
    have h₁' := h₁
    rw [← matchAt?_eq_some_iff, ← skip?_eq_matchAt?] at h₁
    simp [h₁]
    split <;> rename_i hp
    · exact ih
    · obtain rfl : p₁ = p₂ := Std.le_antisymm h₁'.le (Std.not_lt.1 hp)
      obtain rfl := h₂.eq_of_isLongestMatchAt_self h₁'
      exact Std.le_refl _

theorem skipPrefixWhile_eq_skipWhile_startPos {ρ : Type} {pat : ρ} [ForwardPattern pat] {s : Slice} :
    s.skipPrefixWhile pat = s.startPos.skipWhile pat :=
  (rfl)

@[simp]
theorem cast_skipPrefixWhile {ρ : Type} {pat : ρ} [PatternModel pat] [ForwardPattern pat]
    [LawfulForwardPatternModel pat] {s t : Slice} (hst : s.copy = t.copy) :
    (s.skipPrefixWhile pat).cast hst = t.skipPrefixWhile pat := by
  simp [skipPrefixWhile_eq_skipWhile_startPos, ← Pos.skipWhile_cast]

theorem Pattern.Model.skipPrefixWhile_eq_iff {ρ : Type} (pat : ρ) [PatternModel pat]
    [ForwardPattern pat] [LawfulForwardPatternModel pat] (s : Slice) (res : s.Pos) :
    s.skipPrefixWhile pat = res ↔ IsLongestMatchAtChain pat s.startPos res ∧
      (¬MatchesAt pat res ∨ IsLongestMatchAt pat res res) := by
  simp [skipPrefixWhile_eq_skipWhile_startPos, Pos.skipWhile_eq_iff]

theorem Pattern.Model.isLongestMatchAtChain_skipPrefixWhile {ρ : Type} (pat : ρ) [PatternModel pat]
    [ForwardPattern pat] [LawfulForwardPatternModel pat] (s : Slice) :
    IsLongestMatchAtChain pat s.startPos (s.skipPrefixWhile pat) := by
  simpa [skipPrefixWhile_eq_skipWhile_startPos] using Pos.isLongestMatchAtChain_skipWhile pat s.startPos

theorem Pattern.Model.not_matchesAt_or_isLongestMatchAt_skipPrefixWhile {ρ : Type} (pat : ρ)
    [PatternModel pat] [ForwardPattern pat] [LawfulForwardPatternModel pat] (s : Slice) :
    ¬ MatchesAt pat (s.skipPrefixWhile pat) ∨ IsLongestMatchAt pat (s.skipPrefixWhile pat) (s.skipPrefixWhile pat) := by
  simpa [skipPrefixWhile_eq_skipWhile_startPos] using Pos.not_matchesAt_or_isLongestMatchAt_skipWhile pat s.startPos

theorem Pattern.Model.not_matchesAt_skipPrefixWhile {ρ : Type} (pat : ρ) [PatternModel pat]
    [StrictPatternModel pat]
    [ForwardPattern pat] [LawfulForwardPatternModel pat] (s : Slice) :
    ¬MatchesAt pat (s.skipPrefixWhile pat) := by
  simpa [skipPrefixWhile_eq_skipWhile_startPos] using Pos.not_matchesAt_skipWhile pat s.startPos

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

theorem Pattern.Model.skipPrefixWhile_eq_startPos_iff_or {ρ : Type} {pat : ρ} [PatternModel pat]
    [ForwardPattern pat] [LawfulForwardPatternModel pat] {s : Slice} :
    s.skipPrefixWhile pat = s.startPos ↔ ¬MatchesAt pat s.startPos ∨ IsLongestMatch pat s.startPos := by
  simp [skipPrefixWhile_eq_skipWhile_startPos, Pos.skipWhile_eq_self_iff_or]

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
    matchesAt_iff_matchesAt_ofSliceFrom] using not_matchesAt_skipPrefixWhile pat s

theorem dropWhile_eq_self {ρ : Type} {pat : ρ} [PatternModel pat] [ForwardPattern pat]
    [LawfulForwardPatternModel pat] {s : Slice} (h : s.startsWith pat = false) :
    s.dropWhile pat = s := by
  simpa [dropWhile_eq_sliceFrom_skipPrefixWhile] using skipPrefixWhile_eq_startPos h

@[simp]
theorem dropWhile_eq_self_iff {ρ : Type} {pat : ρ} [PatternModel pat] [StrictPatternModel pat]
    [ForwardPattern pat] [LawfulForwardPatternModel pat] {s : Slice} :
    s.dropWhile pat = s ↔ s.startsWith pat = false := by
  simp [dropWhile_eq_sliceFrom_skipPrefixWhile]

theorem Pattern.Model.dropWhile_eq_self_iff_or {ρ : Type} {pat : ρ} [PatternModel pat] [ForwardPattern pat]
    [LawfulForwardPatternModel pat] {s : Slice} :
    s.dropWhile pat = s ↔ ¬MatchesAt pat s.startPos ∨ IsLongestMatch pat s.startPos := by
  simp [dropWhile_eq_sliceFrom_skipPrefixWhile, skipPrefixWhile_eq_startPos_iff_or]

theorem takeWhile_eq_sliceTo_skipPrefixWhile {ρ : Type} {pat : ρ} [ForwardPattern pat] {s : Slice} :
    s.takeWhile pat = s.sliceTo (s.skipPrefixWhile pat) :=
  (rfl)

@[simp]
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

theorem all_eq_skipPrefixWhile_beq {ρ : Type} {pat : ρ} [ForwardPattern pat] {s : Slice} :
    s.all pat = (s.skipPrefixWhile pat == s.endPos) :=
  (rfl)

theorem Pattern.Model.all_eq_true_iff {ρ : Type} {pat : ρ} [PatternModel pat] [ForwardPattern pat]
    [LawfulForwardPatternModel pat] {s : Slice} : s.all pat ↔ IsLongestMatchAtChain pat s.startPos s.endPos := by
  simp only [all_eq_skipPrefixWhile_beq, beq_iff_eq, skipPrefixWhile_eq_iff, and_iff_left_iff_imp]
  by_cases h : MatchesAt pat s.endPos
  · obtain ⟨pos, h⟩ := h.exists_isLongestMatchAt
    obtain rfl : pos = s.endPos := (Pos.endPos_le _).1 h.le
    simp [h]
  · simp [h]

theorem all_congr {ρ : Type} {pat : ρ} [PatternModel pat] [ForwardPattern pat]
    [LawfulForwardPatternModel pat] {s t : Slice} (hst : s.copy = t.copy) :
    s.all pat = t.all pat := by
  rw [all_eq_skipPrefixWhile_beq, ← cast_skipPrefixWhile hst.symm,
    all_eq_skipPrefixWhile_beq, Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, Pos.cast_eq_endPos]

@[simp]
theorem all_takeWhile {ρ : Type} {pat : ρ} [PatternModel pat] [ForwardPattern pat]
    [LawfulForwardPatternModel pat] {s : Slice} : (s.takeWhile pat).all pat = true := by
  rw [Pattern.Model.all_eq_true_iff, takeWhile_eq_sliceTo_skipPrefixWhile]
  apply isLongestMatchAtChain_of_ofSliceTo
  simpa using Pattern.Model.isLongestMatchAtChain_skipPrefixWhile pat s

theorem isEmpty_takeWhile_iff_dropWhile_eq_self {ρ : Type} {pat : ρ} [ForwardPattern pat] {s : Slice} :
    (s.takeWhile pat).isEmpty ↔ s.dropWhile pat = s := by
  simp [takeWhile_eq_sliceTo_skipPrefixWhile, dropWhile_eq_sliceFrom_skipPrefixWhile]

theorem isEmpty_dropWhile_iff_takeWhile_eq_self {ρ : Type} {pat : ρ} [ForwardPattern pat] {s : Slice} :
    (s.dropWhile pat).isEmpty ↔ s.takeWhile pat = s := by
  simp [takeWhile_eq_sliceTo_skipPrefixWhile, dropWhile_eq_sliceFrom_skipPrefixWhile]

@[simp]
theorem takeWhile_eq_self_iff {ρ : Type} {pat : ρ} [ForwardPattern pat] {s : Slice} :
    s.takeWhile pat = s ↔ s.all pat := by
  simp [takeWhile_eq_sliceTo_skipPrefixWhile, all_eq_skipPrefixWhile_beq]

@[simp]
theorem isEmpty_dropWhile {ρ : Type} {pat : ρ} [ForwardPattern pat] {s : Slice} :
    (s.dropWhile pat).isEmpty = s.all pat := by
  rw [Bool.eq_iff_iff, isEmpty_dropWhile_iff_takeWhile_eq_self, takeWhile_eq_self_iff]

@[simp]
theorem dropWhile_dropWhile {ρ : Type} {pat : ρ} [PatternModel pat] [ForwardPattern pat]
    [LawfulForwardPatternModel pat] {s : Slice} : (s.dropWhile pat).dropWhile pat = s.dropWhile pat := by
  conv => enter [1, 1]; rw [dropWhile_eq_sliceFrom_skipPrefixWhile]
  conv => rhs; rw [dropWhile_eq_sliceFrom_skipPrefixWhile]
  simpa [Pattern.Model.dropWhile_eq_self_iff_or, matchesAt_iff_matchesAt_ofSliceFrom,
    isLongestMatch_iff_isLongestMatchAt_ofSliceFrom] using not_matchesAt_or_isLongestMatchAt_skipPrefixWhile ..

theorem takeWhile_takeWhile {ρ : Type} {pat : ρ} [PatternModel pat] [ForwardPattern pat]
    [LawfulForwardPatternModel pat] {s : Slice} : (s.takeWhile pat).takeWhile pat = s.takeWhile pat := by
  simp

@[simp]
theorem isEmpty_takeWhile_dropWhile {ρ : Type} {pat : ρ} [PatternModel pat] [ForwardPattern pat]
    [LawfulForwardPatternModel pat] {s : Slice} : ((s.dropWhile pat).takeWhile pat).isEmpty = true := by
  simp [isEmpty_takeWhile_iff_dropWhile_eq_self]

theorem isEmpty_dropWhile_takeWhile {ρ : Type} {pat : ρ} [PatternModel pat] [ForwardPattern pat]
    [LawfulForwardPatternModel pat] {s : Slice} : ((s.takeWhile pat).dropWhile pat).isEmpty = true := by
  simp

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
  simp [Pos.revSkip?_eq_map_skipSuffix?, endsWith_eq_false_iff, revMatchesAt_iff_revMatchesAt_ofSliceTo]

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

theorem Pattern.Model.Pos.revSkipWhile_eq_self {ρ : Type} {pat : ρ} [PatternModel pat]
    [BackwardPattern pat] [LawfulBackwardPatternModel pat] {s : Slice} {pos : s.Pos}
    (h : ¬ RevMatchesAt pat pos) : pos.revSkipWhile pat = pos := by
  rw [← revMatchAt?_eq_none_iff, ← revSkip?_eq_revMatchAt?] at h
  rw [Pos.revSkipWhile, h]

theorem Pattern.Model.Pos.revSkipWhile_eq_iff {ρ : Type} (pat : ρ) [PatternModel pat]
    [BackwardPattern pat] [LawfulBackwardPatternModel pat] {s : Slice} (startPos endPos : s.Pos) :
    endPos.revSkipWhile pat = startPos ↔ IsLongestRevMatchAtChain pat startPos endPos ∧
      (¬RevMatchesAt pat startPos ∨ IsLongestRevMatchAt pat startPos startPos) := by
  fun_induction Pos.revSkipWhile with
  | case1 pos nextCurr h₁ h₂ ih =>
    rw [revSkip?_eq_revMatchAt?, revMatchAt?_eq_some_iff] at h₁
    refine ih.trans ⟨fun ⟨hx, hy⟩ => ⟨.cons _ _ _ hx h₁, hy⟩, fun ⟨hx, hy⟩ => ⟨?_, hy⟩⟩
    cases hx with
    | nil =>
      refine hy.elim (fun h => (h h₁.revMatchesAt).elim) (fun h => ?_)
      obtain rfl := h₁.eq h
      exact .nil _
    | cons mid endP hx' hy' =>
      obtain rfl := hy'.eq h₁
      exact hx'
  | case2 pos nextCurr h₁ h₂ =>
    rw [revSkip?_eq_revMatchAt?, revMatchAt?_eq_some_iff] at h₁
    obtain rfl := Std.le_antisymm h₁.le (Std.not_lt.1 h₂)
    refine ⟨?_, fun ⟨hx, hy⟩ => ?_⟩
    · rintro rfl
      exact ⟨.nil _, Or.inr h₁⟩
    · exact (hx.eq_of_isLongestRevMatchAt_self h₁).symm
  | case3 pos h =>
    rw [revSkip?_eq_revMatchAt?, revMatchAt?_eq_none_iff] at h
    refine ⟨?_, ?_⟩
    · rintro rfl
      exact ⟨.nil _, Or.inl h⟩
    · rintro ⟨(_|⟨mid, endP, hx, hy⟩), -⟩
      · rfl
      · exact (h hy.revMatchesAt).elim

theorem Pattern.Model.Pos.isLongestRevMatchAtChain_revSkipWhile {ρ : Type} (pat : ρ) [PatternModel pat]
    [BackwardPattern pat] [LawfulBackwardPatternModel pat] {s : Slice} (pos : s.Pos) :
    IsLongestRevMatchAtChain pat (pos.revSkipWhile pat) pos :=
  ((revSkipWhile_eq_iff pat _ pos).1 rfl).1

theorem Pattern.Model.Pos.not_revMatchesAt_or_isLongestRevMatchAt_revSkipWhile {ρ : Type} (pat : ρ)
    [PatternModel pat] [BackwardPattern pat] [LawfulBackwardPatternModel pat] {s : Slice} (pos : s.Pos) :
    ¬ RevMatchesAt pat (pos.revSkipWhile pat) ∨ IsLongestRevMatchAt pat (pos.revSkipWhile pat) (pos.revSkipWhile pat) :=
  ((revSkipWhile_eq_iff pat _ pos).1 rfl).2

theorem Pattern.Model.Pos.not_revMatchesAt_revSkipWhile {ρ : Type} (pat : ρ) [PatternModel pat]
    [StrictPatternModel pat]
    [BackwardPattern pat] [LawfulBackwardPatternModel pat] {s : Slice} (pos : s.Pos) :
    ¬RevMatchesAt pat (pos.revSkipWhile pat) := by
  simpa using not_revMatchesAt_or_isLongestRevMatchAt_revSkipWhile pat pos

theorem Pattern.Model.Pos.revSkipWhile_eq_self_iff {ρ : Type} {pat : ρ} [PatternModel pat] [StrictPatternModel pat]
    [BackwardPattern pat] [LawfulBackwardPatternModel pat] {s : Slice} {pos : s.Pos} :
    pos.revSkipWhile pat = pos ↔ ¬RevMatchesAt pat pos := by
  simp [revSkipWhile_eq_iff]

theorem Pattern.Model.Pos.revSkipWhile_eq_self_iff_or {ρ : Type} {pat : ρ} [PatternModel pat]
    [BackwardPattern pat] [LawfulBackwardPatternModel pat] {s : Slice} {pos : s.Pos} :
    pos.revSkipWhile pat = pos ↔ ¬RevMatchesAt pat pos ∨ IsLongestRevMatchAt pat pos pos := by
  simp [revSkipWhile_eq_iff]

@[simp]
theorem Pos.revSkipWhile_le {ρ : Type} {pat : ρ} [PatternModel pat] [BackwardPattern pat]
    [LawfulBackwardPatternModel pat] {s : Slice} {pos : s.Pos} : pos.revSkipWhile pat ≤ pos :=
  (Pattern.Model.Pos.isLongestRevMatchAtChain_revSkipWhile pat pos).le

theorem Pattern.Model.Pos.revSkipWhile_le_of_isLongestRevMatchAtChain {ρ : Type} (pat : ρ) [PatternModel pat]
    [BackwardPattern pat] [LawfulBackwardPatternModel pat] {s : Slice} {startPos endPos : s.Pos}
    (h : IsLongestRevMatchAtChain pat startPos endPos) : endPos.revSkipWhile pat ≤ startPos := by
  induction h with
  | nil => exact Pos.revSkipWhile_le
  | cons mid endP hchain hmatch ih =>
    rw [Pos.revSkipWhile]
    have hmatch' := hmatch
    rw [← revMatchAt?_eq_some_iff, ← revSkip?_eq_revMatchAt?] at hmatch
    simp [hmatch]
    split <;> rename_i hp
    · exact ih
    · obtain rfl : mid = endP := Std.le_antisymm hmatch'.le (Std.not_lt.1 hp)
      obtain rfl := hchain.eq_of_isLongestRevMatchAt_self hmatch'
      exact Std.le_refl _

theorem skipSuffixWhile_eq_revSkipWhile_endPos {ρ : Type} {pat : ρ} [BackwardPattern pat] {s : Slice} :
    s.skipSuffixWhile pat = s.endPos.revSkipWhile pat :=
  (rfl)

@[simp]
theorem cast_skipSuffixWhile {ρ : Type} {pat : ρ} [PatternModel pat] [BackwardPattern pat]
    [LawfulBackwardPatternModel pat] {s t : Slice} (hst : s.copy = t.copy) :
    (s.skipSuffixWhile pat).cast hst = t.skipSuffixWhile pat := by
  simp [skipSuffixWhile_eq_revSkipWhile_endPos, ← Pos.revSkipWhile_cast]

theorem Pattern.Model.not_revMatchesAt_skipSuffixWhile {ρ : Type} (pat : ρ) [PatternModel pat]
    [StrictPatternModel pat]
    [BackwardPattern pat] [LawfulBackwardPatternModel pat] (s : Slice) :
    ¬RevMatchesAt pat (s.skipSuffixWhile pat) := by
  simpa [skipSuffixWhile_eq_revSkipWhile_endPos] using Pos.not_revMatchesAt_revSkipWhile pat s.endPos

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

theorem Pattern.Model.skipSuffixWhile_eq_iff {ρ : Type} (pat : ρ) [PatternModel pat]
    [BackwardPattern pat] [LawfulBackwardPatternModel pat] (s : Slice) (res : s.Pos) :
    s.skipSuffixWhile pat = res ↔ IsLongestRevMatchAtChain pat res s.endPos ∧
      (¬RevMatchesAt pat res ∨ IsLongestRevMatchAt pat res res) := by
  simp [skipSuffixWhile_eq_revSkipWhile_endPos, Pos.revSkipWhile_eq_iff]

theorem Pattern.Model.isLongestRevMatchAtChain_skipSuffixWhile {ρ : Type} (pat : ρ) [PatternModel pat]
    [BackwardPattern pat] [LawfulBackwardPatternModel pat] (s : Slice) :
    IsLongestRevMatchAtChain pat (s.skipSuffixWhile pat) s.endPos := by
  simpa [skipSuffixWhile_eq_revSkipWhile_endPos] using Pos.isLongestRevMatchAtChain_revSkipWhile pat s.endPos

theorem Pattern.Model.not_revMatchesAt_or_isLongestRevMatchAt_skipSuffixWhile {ρ : Type} (pat : ρ)
    [PatternModel pat] [BackwardPattern pat] [LawfulBackwardPatternModel pat] (s : Slice) :
    ¬ RevMatchesAt pat (s.skipSuffixWhile pat) ∨ IsLongestRevMatchAt pat (s.skipSuffixWhile pat) (s.skipSuffixWhile pat) := by
  simpa [skipSuffixWhile_eq_revSkipWhile_endPos] using Pos.not_revMatchesAt_or_isLongestRevMatchAt_revSkipWhile pat s.endPos

theorem Pattern.Model.skipSuffixWhile_eq_endPos_iff_or {ρ : Type} {pat : ρ} [PatternModel pat]
    [BackwardPattern pat] [LawfulBackwardPatternModel pat] {s : Slice} :
    s.skipSuffixWhile pat = s.endPos ↔ ¬RevMatchesAt pat s.endPos ∨ IsLongestRevMatchAt pat s.endPos s.endPos := by
  simp [skipSuffixWhile_eq_revSkipWhile_endPos, Pos.revSkipWhile_eq_self_iff_or]

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
    revMatchesAt_iff_revMatchesAt_ofSliceTo] using not_revMatchesAt_skipSuffixWhile pat s

theorem dropEndWhile_eq_self {ρ : Type} {pat : ρ} [PatternModel pat] [BackwardPattern pat]
    [LawfulBackwardPatternModel pat] {s : Slice} (h : s.endsWith pat = false) :
    s.dropEndWhile pat = s := by
  simpa [dropEndWhile_eq_sliceTo_skipSuffixWhile] using skipSuffixWhile_eq_endPos h

@[simp]
theorem dropEndWhile_eq_self_iff {ρ : Type} {pat : ρ} [PatternModel pat] [StrictPatternModel pat]
    [BackwardPattern pat] [LawfulBackwardPatternModel pat] {s : Slice} :
    s.dropEndWhile pat = s ↔ s.endsWith pat = false := by
  simp [dropEndWhile_eq_sliceTo_skipSuffixWhile]

theorem Pattern.Model.dropEndWhile_eq_self_iff_or {ρ : Type} {pat : ρ} [PatternModel pat] [BackwardPattern pat]
    [LawfulBackwardPatternModel pat] {s : Slice} :
    s.dropEndWhile pat = s ↔ ¬RevMatchesAt pat s.endPos ∨ IsLongestRevMatchAt pat s.endPos s.endPos := by
  simp [dropEndWhile_eq_sliceTo_skipSuffixWhile, skipSuffixWhile_eq_endPos_iff_or]

theorem takeEndWhile_eq_sliceFrom_skipSuffixWhile {ρ : Type} {pat : ρ} [BackwardPattern pat] {s : Slice} :
    s.takeEndWhile pat = s.sliceFrom (s.skipSuffixWhile pat) :=
  (rfl)

@[simp]
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

theorem revAll_eq_skipSuffixWhile_beq {ρ : Type} {pat : ρ} [BackwardPattern pat] {s : Slice} :
    s.revAll pat = (s.skipSuffixWhile pat == s.startPos) :=
  (rfl)

theorem Pattern.Model.revAll_eq_true_iff {ρ : Type} {pat : ρ} [PatternModel pat] [BackwardPattern pat]
    [LawfulBackwardPatternModel pat] {s : Slice} : s.revAll pat ↔ IsLongestRevMatchAtChain pat s.startPos s.endPos := by
  simp only [revAll_eq_skipSuffixWhile_beq, beq_iff_eq, skipSuffixWhile_eq_iff, and_iff_left_iff_imp]
  by_cases h : RevMatchesAt pat s.startPos
  · obtain ⟨pos, h⟩ := h.exists_isLongestRevMatchAt
    obtain rfl : pos = s.startPos := Std.le_antisymm h.le (Pos.startPos_le _)
    simp [h]
  · simp [h]

theorem revAll_congr {ρ : Type} {pat : ρ} [PatternModel pat] [BackwardPattern pat]
    [LawfulBackwardPatternModel pat] {s t : Slice} (hst : s.copy = t.copy) :
    s.revAll pat = t.revAll pat := by
  rw [revAll_eq_skipSuffixWhile_beq, ← cast_skipSuffixWhile hst.symm,
    revAll_eq_skipSuffixWhile_beq, Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, Pos.cast_eq_startPos]

@[simp]
theorem revAll_takeEndWhile {ρ : Type} {pat : ρ} [PatternModel pat] [BackwardPattern pat]
    [LawfulBackwardPatternModel pat] {s : Slice} : (s.takeEndWhile pat).revAll pat = true := by
  rw [Pattern.Model.revAll_eq_true_iff, takeEndWhile_eq_sliceFrom_skipSuffixWhile]
  apply isLongestRevMatchAtChain_of_ofSliceFrom
  simpa using Pattern.Model.isLongestRevMatchAtChain_skipSuffixWhile pat s

theorem isEmpty_takeEndWhile_iff_dropEndWhile_eq_self {ρ : Type} {pat : ρ} [BackwardPattern pat] {s : Slice} :
    (s.takeEndWhile pat).isEmpty ↔ s.dropEndWhile pat = s := by
  simp [takeEndWhile_eq_sliceFrom_skipSuffixWhile, dropEndWhile_eq_sliceTo_skipSuffixWhile]

theorem isEmpty_dropEndWhile_iff_takeEndWhile_eq_self {ρ : Type} {pat : ρ} [BackwardPattern pat] {s : Slice} :
    (s.dropEndWhile pat).isEmpty ↔ s.takeEndWhile pat = s := by
  simp [takeEndWhile_eq_sliceFrom_skipSuffixWhile, dropEndWhile_eq_sliceTo_skipSuffixWhile]

@[simp]
theorem takeEndWhile_eq_self_iff {ρ : Type} {pat : ρ} [BackwardPattern pat] {s : Slice} :
    s.takeEndWhile pat = s ↔ s.revAll pat := by
  simp [takeEndWhile_eq_sliceFrom_skipSuffixWhile, revAll_eq_skipSuffixWhile_beq]

@[simp]
theorem isEmpty_dropEndWhile {ρ : Type} {pat : ρ} [BackwardPattern pat] {s : Slice} :
    (s.dropEndWhile pat).isEmpty = s.revAll pat := by
  rw [Bool.eq_iff_iff, isEmpty_dropEndWhile_iff_takeEndWhile_eq_self, takeEndWhile_eq_self_iff]

@[simp]
theorem dropEndWhile_dropEndWhile {ρ : Type} {pat : ρ} [PatternModel pat] [BackwardPattern pat]
    [LawfulBackwardPatternModel pat] {s : Slice} : (s.dropEndWhile pat).dropEndWhile pat = s.dropEndWhile pat := by
  conv => enter [1, 1]; rw [dropEndWhile_eq_sliceTo_skipSuffixWhile]
  conv => rhs; rw [dropEndWhile_eq_sliceTo_skipSuffixWhile]
  simpa [Pattern.Model.dropEndWhile_eq_self_iff_or, revMatchesAt_iff_revMatchesAt_ofSliceTo,
    isLongestRevMatch_iff_isLongestRevMatchAt_ofSliceTo] using not_revMatchesAt_or_isLongestRevMatchAt_skipSuffixWhile ..

theorem takeEndWhile_takeEndWhile {ρ : Type} {pat : ρ} [PatternModel pat] [BackwardPattern pat]
    [LawfulBackwardPatternModel pat] {s : Slice} : (s.takeEndWhile pat).takeEndWhile pat = s.takeEndWhile pat := by
  simp

@[simp]
theorem isEmpty_takeEndWhile_dropEndWhile {ρ : Type} {pat : ρ} [PatternModel pat] [BackwardPattern pat]
    [LawfulBackwardPatternModel pat] {s : Slice} : ((s.dropEndWhile pat).takeEndWhile pat).isEmpty = true := by
  simp [isEmpty_takeEndWhile_iff_dropEndWhile_eq_self]

theorem isEmpty_dropEndWhile_takeEndWhile {ρ : Type} {pat : ρ} [PatternModel pat] [BackwardPattern pat]
    [LawfulBackwardPatternModel pat] {s : Slice} : ((s.takeEndWhile pat).dropEndWhile pat).isEmpty = true := by
  simp

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

theorem Pos.skip?_eq_skip?_toSlice {ρ : Type} {pat : ρ} [ForwardPattern pat] {s : String} {pos : s.Pos} :
    pos.skip? pat = (pos.toSlice.skip? pat).map Pos.ofToSlice := (rfl)

theorem Pos.skip?_toSlice {ρ : Type} {pat : ρ} [ForwardPattern pat] {s : String} {pos : s.Pos} :
    pos.toSlice.skip? pat = (pos.skip? pat).map Pos.toSlice := by
  simp [skip?_eq_skip?_toSlice]

theorem Slice.Pos.skip?_copy {ρ : Type} {pat : ρ} [ForwardPattern pat] [PatternModel pat]
    [LawfulForwardPatternModel pat] {s : Slice} {pos : s.Pos} :
    pos.copy.skip? pat = (pos.skip? pat).map Slice.Pos.copy := by
  rw [Pos.skip?_eq_skip?_toSlice, Slice.Pos.skip?_congr (hst := String.copy_toSlice), cast_toSlice_copy, Option.map_map]
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

@[simp]
theorem Pos.skipWhile_le {ρ : Type} {pat : ρ} [ForwardPattern pat] [PatternModel pat]
    [LawfulForwardPatternModel pat] {s : String} {pos : s.Pos} : pos ≤ pos.skipWhile pat := by
  simp [skipWhile_eq_skipWhile_toSlice, Pos.le_ofToSlice_iff]

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

theorem skipPrefixWhile_eq_startPos {ρ : Type} {pat : ρ} [PatternModel pat] [ForwardPattern pat]
    [LawfulForwardPatternModel pat] {s : String} :
    s.startsWith pat = false → s.skipPrefixWhile pat = s.startPos := by
  simpa [skipPrefixWhile_eq_skipPrefixWhile_toSlice, ← startsWith_toSlice, ← Pos.toSlice_inj,
    ← startPos_toSlice] using Slice.skipPrefixWhile_eq_startPos

@[simp]
theorem skipPrefixWhile_eq_startPos_iff {ρ : Type} {pat : ρ} [PatternModel pat] [StrictPatternModel pat]
    [ForwardPattern pat] [LawfulForwardPatternModel pat] {s : String} :
    s.skipPrefixWhile pat = s.startPos ↔ s.startsWith pat = false := by
  simp [skipPrefixWhile_eq_skipPrefixWhile_toSlice, ← startsWith_toSlice, ← Pos.toSlice_inj,
    ← startPos_toSlice]

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

@[simp]
theorem startsWith_dropWhile {ρ : Type} {pat : ρ} [PatternModel pat] [StrictPatternModel pat]
    [ForwardPattern pat] [LawfulForwardPatternModel pat] {s : String} :
    (s.dropWhile pat).startsWith pat = false := by
  simp [← dropWhile_toSlice]

theorem dropWhile_eq_toSlice {ρ : Type} {pat : ρ} [PatternModel pat] [ForwardPattern pat]
    [LawfulForwardPatternModel pat] {s : String} (h : s.startsWith pat = false) :
    s.dropWhile pat = s.toSlice := by
  rw [dropWhile_eq_dropWhile_toSlice, Slice.dropWhile_eq_self (by simpa)]

@[simp]
theorem dropWhile_eq_toSlice_iff {ρ : Type} {pat : ρ} [PatternModel pat] [StrictPatternModel pat]
    [ForwardPattern pat] [LawfulForwardPatternModel pat] {s : String} :
    s.dropWhile pat = s.toSlice ↔ s.startsWith pat = false := by
  rw [dropWhile_eq_dropWhile_toSlice, Slice.dropWhile_eq_self_iff, startsWith_toSlice]

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

@[simp]
theorem takeWhile_append_dropWhile {ρ : Type} {pat : ρ} [PatternModel pat] [ForwardPattern pat]
    [LawfulForwardPattern pat] {s : String} : (s.takeWhile pat).copy ++ (s.dropWhile pat).copy = s := by
  simp [← takeWhile_toSlice, ← dropWhile_toSlice]

theorem isEmpty_takeWhile_eq_true {ρ : Type} {pat : ρ} [PatternModel pat] [ForwardPattern pat]
    [LawfulForwardPatternModel pat] {s : String} (h : s.startsWith pat = false) :
    (s.takeWhile pat).isEmpty = true := by
  rw [← takeWhile_toSlice, Slice.isEmpty_takeWhile_eq_true (by simpa)]

@[simp]
theorem isEmpty_takeWhile {ρ : Type} {pat : ρ} [PatternModel pat] [StrictPatternModel pat] [ForwardPattern pat]
    [LawfulForwardPatternModel pat] {s : String} :
    (s.takeWhile pat).isEmpty = !s.startsWith pat := by
  simp [← takeWhile_toSlice]

theorem all_eq_all_toSlice {ρ : Type} {pat : ρ} [ForwardPattern pat] {s : String} :
    s.all pat = s.toSlice.all pat :=
  (rfl)

@[simp]
theorem all_toSlice {ρ : Type} {pat : ρ} [ForwardPattern pat] {s : String} :
    s.toSlice.all pat = s.all pat := by
  simp [all_eq_all_toSlice]

@[simp]
theorem Slice.all_copy {ρ : Type} {pat : ρ} [PatternModel pat] [ForwardPattern pat]
    [LawfulForwardPatternModel pat] {s : Slice} : s.copy.all pat = s.all pat := by
  simpa [← all_toSlice] using all_congr (by simp)

@[simp]
theorem all_takeWhile {ρ : Type} {pat : ρ} [PatternModel pat] [ForwardPattern pat]
    [LawfulForwardPatternModel pat] {s : String} : (s.takeWhile pat).all pat = true := by
  simp [← takeWhile_toSlice]

@[simp]
theorem takeWhile_eq_toSlice_iff {ρ : Type} {pat : ρ} [ForwardPattern pat] {s : String} :
    s.takeWhile pat = s.toSlice ↔ s.all pat := by
  simp [← takeWhile_toSlice]

@[simp]
theorem isEmpty_dropWhile {ρ : Type} {pat : ρ} [ForwardPattern pat] {s : String} :
    (s.dropWhile pat).isEmpty = s.all pat := by
  simp [← dropWhile_toSlice]

@[simp]
theorem dropWhile_dropWhile {ρ : Type} {pat : ρ} [PatternModel pat] [ForwardPattern pat]
    [LawfulForwardPatternModel pat] {s : String} : (s.dropWhile pat).dropWhile pat = s.dropWhile pat := by
  simp [← dropWhile_toSlice]

theorem takeWhile_takeWhile {ρ : Type} {pat : ρ} [PatternModel pat] [ForwardPattern pat]
    [LawfulForwardPatternModel pat] {s : Slice} : (s.takeWhile pat).takeWhile pat = s.takeWhile pat := by
  simp

@[simp]
theorem isEmpty_takeWhile_dropWhile {ρ : Type} {pat : ρ} [PatternModel pat] [ForwardPattern pat]
    [LawfulForwardPatternModel pat] {s : String} : ((s.dropWhile pat).takeWhile pat).isEmpty = true := by
  simp [← dropWhile_toSlice]

theorem isEmpty_dropWhile_takeWhile {ρ : Type} {pat : ρ} [PatternModel pat] [ForwardPattern pat]
    [LawfulForwardPatternModel pat] {s : String} : ((s.takeWhile pat).dropWhile pat).isEmpty = true := by
  simp

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

@[simp]
theorem Pos.revSkipWhile_le {ρ : Type} {pat : ρ} [BackwardPattern pat] [PatternModel pat]
    [LawfulBackwardPatternModel pat] {s : String} {pos : s.Pos} : pos.revSkipWhile pat ≤ pos := by
  simp [Pos.revSkipWhile_eq_revSkipWhile_toSlice, Pos.ofToSlice_le_iff]

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

theorem skipSuffixWhile_eq_endPos {ρ : Type} {pat : ρ} [PatternModel pat] [BackwardPattern pat]
    [LawfulBackwardPatternModel pat] {s : String} :
    s.endsWith pat = false → s.skipSuffixWhile pat = s.endPos := by
  simpa [skipSuffixWhile_eq_skipSuffixWhile_toSlice, ← endsWith_toSlice, ← Pos.toSlice_inj,
    ← endPos_toSlice] using Slice.skipSuffixWhile_eq_endPos

@[simp]
theorem skipSuffixWhile_eq_endPos_iff {ρ : Type} {pat : ρ} [PatternModel pat] [StrictPatternModel pat]
    [BackwardPattern pat] [LawfulBackwardPatternModel pat] {s : String} :
    s.skipSuffixWhile pat = s.endPos ↔ s.endsWith pat = false := by
  simp [skipSuffixWhile_eq_skipSuffixWhile_toSlice, ← endsWith_toSlice, ← Pos.toSlice_inj,
    ← endPos_toSlice]

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

@[simp]
theorem endsWith_dropEndWhile {ρ : Type} {pat : ρ} [PatternModel pat] [StrictPatternModel pat]
    [BackwardPattern pat] [LawfulBackwardPatternModel pat] {s : String} :
    (s.dropEndWhile pat).endsWith pat = false := by
  simp [← dropEndWhile_toSlice]

theorem dropEndWhile_eq_toSlice {ρ : Type} {pat : ρ} [PatternModel pat] [BackwardPattern pat]
    [LawfulBackwardPatternModel pat] {s : String} (h : s.endsWith pat = false) :
    s.dropEndWhile pat = s.toSlice := by
  rw [dropEndWhile_eq_dropEndWhile_toSlice, Slice.dropEndWhile_eq_self (by simpa)]

@[simp]
theorem dropEndWhile_eq_toSlice_iff {ρ : Type} {pat : ρ} [PatternModel pat] [StrictPatternModel pat]
    [BackwardPattern pat] [LawfulBackwardPatternModel pat] {s : String} :
    s.dropEndWhile pat = s.toSlice ↔ s.endsWith pat = false := by
  rw [dropEndWhile_eq_dropEndWhile_toSlice, Slice.dropEndWhile_eq_self_iff, endsWith_toSlice]

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

@[simp]
theorem dropEndWhile_append_takeEndWhile {ρ : Type} {pat : ρ} [PatternModel pat] [BackwardPattern pat]
    [LawfulBackwardPattern pat] {s : String} : (s.dropEndWhile pat).copy ++ (s.takeEndWhile pat).copy = s := by
  simp [← dropEndWhile_toSlice, ← takeEndWhile_toSlice]

theorem isEmpty_takeEndWhile_eq_true {ρ : Type} {pat : ρ} [PatternModel pat] [BackwardPattern pat]
    [LawfulBackwardPatternModel pat] {s : String} (h : s.endsWith pat = false) :
    (s.takeEndWhile pat).isEmpty = true := by
  rw [← takeEndWhile_toSlice, Slice.isEmpty_takeEndWhile_eq_true (by simpa)]

@[simp]
theorem isEmpty_takeEndWhile {ρ : Type} {pat : ρ} [PatternModel pat] [StrictPatternModel pat] [BackwardPattern pat]
    [LawfulBackwardPatternModel pat] {s : String} :
    (s.takeEndWhile pat).isEmpty = !s.endsWith pat := by
  simp [← takeEndWhile_toSlice]

theorem revAll_eq_revAll_toSlice {ρ : Type} {pat : ρ} [BackwardPattern pat] {s : String} :
    s.revAll pat = s.toSlice.revAll pat :=
  (rfl)

@[simp]
theorem revAll_toSlice {ρ : Type} {pat : ρ} [BackwardPattern pat] {s : String} :
    s.toSlice.revAll pat = s.revAll pat := by
  simp [revAll_eq_revAll_toSlice]

@[simp]
theorem Slice.revAll_copy {ρ : Type} {pat : ρ} [PatternModel pat] [BackwardPattern pat]
    [LawfulBackwardPatternModel pat] {s : Slice} : s.copy.revAll pat = s.revAll pat := by
  simpa [← revAll_toSlice] using Slice.revAll_congr (by simp)

@[simp]
theorem revAll_takeEndWhile {ρ : Type} {pat : ρ} [PatternModel pat] [BackwardPattern pat]
    [LawfulBackwardPatternModel pat] {s : String} : (s.takeEndWhile pat).revAll pat = true := by
  simp [← takeEndWhile_toSlice]

@[simp]
theorem takeEndWhile_eq_toSlice_iff {ρ : Type} {pat : ρ} [BackwardPattern pat] {s : String} :
    s.takeEndWhile pat = s.toSlice ↔ s.revAll pat := by
  simp [← takeEndWhile_toSlice]

@[simp]
theorem isEmpty_dropEndWhile {ρ : Type} {pat : ρ} [BackwardPattern pat] {s : String} :
    (s.dropEndWhile pat).isEmpty = s.revAll pat := by
  simp [← dropEndWhile_toSlice]

@[simp]
theorem dropEndWhile_dropEndWhile {ρ : Type} {pat : ρ} [PatternModel pat] [BackwardPattern pat]
    [LawfulBackwardPatternModel pat] {s : String} : (s.dropEndWhile pat).dropEndWhile pat = s.dropEndWhile pat := by
  simp [← dropEndWhile_toSlice]

theorem takeEndWhile_takeEndWhile {ρ : Type} {pat : ρ} [PatternModel pat] [BackwardPattern pat]
    [LawfulBackwardPatternModel pat] {s : Slice} : (s.takeEndWhile pat).takeEndWhile pat = s.takeEndWhile pat := by
  simp

@[simp]
theorem isEmpty_takeEndWhile_dropEndWhile {ρ : Type} {pat : ρ} [PatternModel pat] [BackwardPattern pat]
    [LawfulBackwardPatternModel pat] {s : String} : ((s.dropEndWhile pat).takeEndWhile pat).isEmpty = true := by
  simp [← dropEndWhile_toSlice]

theorem isEmpty_dropEndWhile_takeEndWhile {ρ : Type} {pat : ρ} [PatternModel pat] [BackwardPattern pat]
    [LawfulBackwardPatternModel pat] {s : String} : ((s.takeEndWhile pat).dropEndWhile pat).isEmpty = true := by
  simp

end String
