/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

prelude
public import Init.Data.String.Iterate
public import Init.Data.Iterators.Consumers.Collect
public import Init.Data.String.Lemmas.Splits
import all Init.Data.String.Iterate
import Init.Data.String.Termination
import Init.Data.Iterators.Lemmas.Consumers.Collect
import Init.ByCases
import Init.Data.Iterators.Lemmas.Combinators.FilterMap
import Init.Data.String.Lemmas.Basic
import Init.Data.Iterators.Lemmas.Consumers.Loop
public import Init.Data.String.Lemmas.Order
import Init.Data.String.OrderInstances
import Init.Data.Subtype.Basic

set_option doc.verso true

public section

namespace String

namespace Slice

/--
A list of all positions starting at {name}`p`.

This function is not meant to be used in actual programs. Actual programs should use
{name}`Slice.positionsFrom` or {name}`Slice.positions`.
-/
protected def Model.positionsFrom {s : Slice} (p : s.Pos) : List { p : s.Pos // p ≠ s.endPos } :=
  if h : p.IsAtEnd then
    []
  else
    ⟨p, h⟩ :: Model.positionsFrom (p.next h)
termination_by p

@[simp]
theorem Model.positionsFrom_endPos {s : Slice} : Model.positionsFrom s.endPos = [] := by
  simp [Model.positionsFrom]

theorem Model.positionsFrom_eq_cons {s : Slice} {p : s.Pos} (hp : p ≠ s.endPos) :
    Model.positionsFrom p = ⟨p, hp⟩ :: Model.positionsFrom (p.next hp) := by
  rw [Model.positionsFrom]
  simp [hp]

@[simp]
theorem Model.mem_positionsFrom {s : Slice} {p : s.Pos} {q : { q : s.Pos // q ≠ s.endPos } } :
    q ∈ Model.positionsFrom p ↔ p ≤ q := by
  induction p using Pos.next_induction with
  | next p h ih =>
    rw [Model.positionsFrom_eq_cons h, List.mem_cons, ih]
    simp [Subtype.ext_iff, Std.le_iff_lt_or_eq (a := p), or_comm, eq_comm]
  | endPos => simp [q.property]

theorem Model.mem_positionsFrom_startPos {s : Slice} {q : { q : s.Pos // q ≠ s.endPos} } :
    q ∈ Model.positionsFrom s.startPos := by
  simp

theorem Model.map_get_positionsFrom_of_splits {s : Slice} {p : s.Pos} {t₁ t₂ : String}
    (hp : p.Splits t₁ t₂) : (Model.positionsFrom p).map (fun p => p.1.get p.2) = t₂.toList := by
  induction p using Pos.next_induction generalizing t₁ t₂ with
  | next p h ih =>
    obtain ⟨t₂, rfl⟩ := hp.exists_eq_singleton_append h
    rw [Model.positionsFrom_eq_cons h, List.map_cons, String.toList_append, toList_singleton,
      List.singleton_append, ih hp.next]
  | endPos => simpa using (splits_endPos_iff.1 hp).2

theorem Model.map_get_positionsFrom_startPos {s : Slice} :
    (Model.positionsFrom s.startPos).map (fun p => p.1.get p.2) = s.copy.toList :=
  Model.map_get_positionsFrom_of_splits (splits_startPos s)

@[cbv_eval, simp]
theorem toList_positionsFrom {s : Slice} {p : s.Pos} :
    (s.positionsFrom p).toList = Model.positionsFrom p := by
  rw [positionsFrom]
  induction p using WellFounded.induction Pos.wellFounded_gt with | h p ih
  rw [Std.Iter.toList_eq_match_step, Std.Iter.step_eq]
  simp only [ne_eq, Std.Iter.toIterM_mk, Std.IterM.internalState_mk]
  by_cases h : p = s.endPos
  · simp [h]
  · simp [h, ih (p.next h) (by simp), Model.positionsFrom_eq_cons]

@[simp]
theorem toList_positions {s : Slice} : s.positions.toList = Model.positionsFrom s.startPos := by
  simp [positions]

@[cbv_eval, simp]
theorem toList_chars {s : Slice} : s.chars.toList = s.copy.toList := by
  simp [chars, Model.map_get_positionsFrom_startPos]

theorem mem_toList_copy_iff_exists_get {s : Slice} {c : Char} :
    c ∈ s.copy.toList ↔ ∃ (p : s.Pos) (h : p ≠ s.endPos), p.get h = c := by
  simp [← Model.map_get_positionsFrom_startPos]

theorem Pos.Splits.mem_toList_left_iff {s : Slice} {pos : s.Pos} {t u : String} {c : Char}
    (hs : pos.Splits t u) :
    c ∈ t.toList ↔ ∃ pos', ∃ (h : pos' < pos), pos'.get (Pos.ne_endPos_of_lt h) = c := by
  rw [hs.eq_left pos.splits, mem_toList_copy_iff_exists_get]
  refine ⟨?_, ?_⟩
  · rintro ⟨p, hp, hpget⟩
    have hlt : Pos.ofSliceTo p < pos := by
      simpa using Pos.ofSliceTo_lt_ofSliceTo_iff.mpr ((Pos.lt_endPos_iff _).mpr hp)
    exact ⟨_, hlt, by rwa [Pos.get_eq_get_ofSliceTo] at hpget⟩
  · rintro ⟨pos', hlt, hget⟩
    exact ⟨pos.sliceTo pos' (Std.le_of_lt hlt),
      by simpa [← Pos.ofSliceTo_inj] using Std.ne_of_lt hlt,
      by rw [Slice.Pos.get_eq_get_ofSliceTo]; simpa using hget⟩

theorem Pos.Splits.mem_toList_right_iff {s : Slice} {pos : s.Pos} {t u : String} {c : Char}
    (hs : pos.Splits t u) :
    c ∈ u.toList ↔ ∃ pos', ∃ (_ : pos ≤ pos') (h : pos' ≠ s.endPos), pos'.get h = c := by
  rw [hs.eq_right pos.splits, mem_toList_copy_iff_exists_get]
  refine ⟨?_, ?_⟩
  · rintro ⟨p, hp, hpget⟩
    exact ⟨Pos.ofSliceFrom p, Pos.le_ofSliceFrom,
      fun h => hp (Pos.ofSliceFrom_inj.mp (h.trans (Pos.ofSliceFrom_endPos (pos := pos)).symm)),
      by rwa [Pos.get_eq_get_ofSliceFrom] at hpget⟩
  · rintro ⟨pos', hle, hne, hget⟩
    exact ⟨pos.sliceFrom pos' hle,
      fun h => hne (by simpa using congrArg Pos.ofSliceFrom h),
      by rw [Pos.get_eq_get_ofSliceFrom]; simpa using hget⟩

/--
A list of all positions strictly before {name}`p`, ordered from largest to smallest.

This function is not meant to be used in actual programs. Actual programs should use
{name}`Slice.revPositionsFrom` and {name}`Slice.revPositions`.
-/
protected def Model.revPositionsFrom {s : Slice} (p : s.Pos) : List { p : s.Pos // p ≠ s.endPos } :=
  if h : p = s.startPos then
    []
  else
    ⟨p.prev h, by simp⟩ :: Model.revPositionsFrom (p.prev h)
termination_by p.down

@[simp]
theorem Model.revPositionsFrom_startPos {s : Slice} : Model.revPositionsFrom s.startPos = [] := by
  simp [Model.revPositionsFrom]

theorem Model.revPositionsFrom_eq_cons {s : Slice} {p : s.Pos} (hp : p ≠ s.startPos) :
    Model.revPositionsFrom p = ⟨p.prev hp, by simp⟩ :: Model.revPositionsFrom (p.prev hp) := by
  rw [Model.revPositionsFrom]
  simp [hp]

theorem Model.map_get_revPositionsFrom_of_splits {s : Slice} {p : s.Pos} {t₁ t₂ : String}
    (hp : p.Splits t₁ t₂) : (Model.revPositionsFrom p).map (fun p => p.1.get p.2) = t₁.toList.reverse := by
  induction p using Pos.prev_induction generalizing t₁ t₂ with
  | startPos => simpa using (splits_startPos_iff.1 hp).1
  | prev p h ih =>
    obtain ⟨t₁, rfl⟩ := hp.exists_eq_append_singleton_of_ne_startPos h
    rw [Model.revPositionsFrom_eq_cons h, List.map_cons, String.toList_append, toList_singleton,
      List.reverse_append, List.reverse_singleton, List.singleton_append, ih hp.prev]

theorem Model.map_get_revPositionsFrom_endPos {s : Slice} :
    (Model.revPositionsFrom s.endPos).map (fun p => p.1.get p.2) = s.copy.toList.reverse :=
  Model.map_get_revPositionsFrom_of_splits (splits_endPos s)

@[simp]
theorem toList_revPositionsFrom {s : Slice} {p : s.Pos} :
    (s.revPositionsFrom p).toList = Model.revPositionsFrom p := by
  rw [revPositionsFrom]
  induction p using WellFounded.induction Pos.wellFounded_lt with | h p ih
  rw [Std.Iter.toList_eq_match_step, Std.Iter.step_eq]
  simp only [ne_eq, Std.Iter.toIterM_mk, Std.IterM.internalState_mk]
  by_cases h : p = s.startPos
  · simp [h]
  · simp [h, ih (p.prev h) (by simp), Model.revPositionsFrom_eq_cons]

@[simp]
theorem toList_revPositions {s : Slice} : s.revPositions.toList = Model.revPositionsFrom s.endPos := by
  simp [revPositions]

@[cbv_eval, simp]
theorem toList_revChars {s : Slice} : s.revChars.toList = s.copy.toList.reverse := by
  simp [revChars, Model.map_get_revPositionsFrom_endPos]

theorem forIn_eq_forIn_chars {m : Type u → Type v} [Monad m] {s : Slice} {b} {f : Char → β → m (ForInStep β)} :
    ForIn.forIn s b f = ForIn.forIn s.chars b f := rfl

@[cbv_eval, simp]
theorem forIn_eq_forIn_toList {m : Type u → Type v} [Monad m] [LawfulMonad m] {s : Slice} {b}
    {f : Char → β → m (ForInStep β)} :
    ForIn.forIn s b f = ForIn.forIn s.copy.toList b f := by
  rw [forIn_eq_forIn_chars, ← Std.Iter.forIn_toList, toList_chars]

@[cbv_eval, simp]
theorem foldl_eq_foldl_toList {α : Type u} {f : α → Char → α} {init : α} {s : Slice} :
    s.foldl f init = s.copy.toList.foldl f init := by
  rw [foldl, ← Std.Iter.foldl_toList, toList_chars]

@[simp]
theorem foldr_eq_foldr_toList {α : Type u} {f : Char → α → α} {init : α} {s : Slice} :
    s.foldr f init = s.copy.toList.foldr f init := by
  rw [foldr, ← Std.Iter.foldl_toList, toList_revChars, List.foldl_reverse]
  congr

end Slice

/--
A list of all positions starting at {name}`p`.

This function is not meant to be used in actual programs. Actual programs should use
{name}`Slice.positionsFrom` or {name}`Slice.positions`.
-/
protected def Model.positionsFrom {s : String} (p : s.Pos) : List { p : s.Pos // p ≠ s.endPos } :=
  if h : p.IsAtEnd then
    []
  else
    ⟨p, h⟩ :: Model.positionsFrom (p.next h)
termination_by p

@[simp]
theorem Model.positionsFrom_endPos {s : String} : Model.positionsFrom s.endPos = [] := by
  simp [Model.positionsFrom]

theorem Model.positionsFrom_eq_cons {s : String} {p : s.Pos} (hp : p ≠ s.endPos) :
    Model.positionsFrom p = ⟨p, hp⟩ :: Model.positionsFrom (p.next hp) := by
  rw [Model.positionsFrom]
  simp [hp]

@[simp]
theorem Model.mem_positionsFrom {s : String} {p : s.Pos} {q : { q : s.Pos // q ≠ s.endPos } } :
    q ∈ Model.positionsFrom p ↔ p ≤ q := by
  induction p using Pos.next_induction with
  | next p h ih =>
    rw [Model.positionsFrom_eq_cons h, List.mem_cons, ih]
    simp [Subtype.ext_iff, Std.le_iff_lt_or_eq (a := p), or_comm, eq_comm]
  | endPos => simp [q.property]

theorem Model.mem_positionsFrom_startPos {s : String} {q : { q : s.Pos // q ≠ s.endPos} } :
    q ∈ Model.positionsFrom s.startPos := by
  simp

theorem Model.positionsFrom_eq_map {s : String} {p : s.Pos} :
    Model.positionsFrom p = (Slice.Model.positionsFrom p.toSlice).map
      (fun p => ⟨Pos.ofToSlice p.1, by simpa [← Pos.toSlice_inj] using p.2⟩) := by
  induction p using Pos.next_induction with
  | next p h ih =>
    rw [positionsFrom_eq_cons h, Slice.Model.positionsFrom_eq_cons (by simpa [Pos.toSlice_inj])]
    simp [ih, Pos.toSlice_next]
  | endPos => simp [← endPos_toSlice]

theorem Model.map_get_positionsFrom_of_splits {s : String} {p : s.Pos} {t₁ t₂ : String}
    (hp : p.Splits t₁ t₂) : (Model.positionsFrom p).map (fun p => p.1.get p.2) = t₂.toList := by
  simp [Model.positionsFrom_eq_map,
    ← Slice.Model.map_get_positionsFrom_of_splits (Pos.splits_toSlice_iff.2 hp)]

theorem Model.map_get_positionsFrom_startPos {s : String} :
    (Model.positionsFrom s.startPos).map (fun p => p.1.get p.2) = s.toList :=
  Model.map_get_positionsFrom_of_splits (splits_startPos s)

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem toList_positionsFrom {s : String} {p : s.Pos} :
    (s.positionsFrom p).toList = Model.positionsFrom p := by
  simp [positionsFrom, Internal.ofToSliceWithProof, Model.positionsFrom_eq_map]

@[cbv_eval]
theorem toList_positions {s : String} : s.positions.toList = Model.positionsFrom s.startPos := by
  simp [positions]

@[cbv_eval, simp]
theorem toList_chars {s : String} : s.chars.toList = s.toList := by
  simp [chars]

theorem mem_toList_iff_exists_get {s : String} {c : Char} :
    c ∈ s.toList ↔ ∃ (p : s.Pos) (h : p ≠ s.endPos), p.get h = c := by
  simp [← Model.map_get_positionsFrom_startPos]

theorem Pos.Splits.mem_toList_left_iff {s : String} {pos : s.Pos} {t u : String} {c : Char}
    (hs : pos.Splits t u) :
    c ∈ t.toList ↔ ∃ pos', ∃ (h : pos' < pos), pos'.get (Pos.ne_endPos_of_lt h) = c := by
  rw [hs.eq_left pos.splits, Slice.mem_toList_copy_iff_exists_get]
  refine ⟨?_, ?_⟩
  · rintro ⟨p, hp, hpget⟩
    have hlt : Pos.ofSliceTo p < pos := by
      simpa using Pos.ofSliceTo_lt_ofSliceTo_iff.mpr ((Slice.Pos.lt_endPos_iff _).mpr hp)
    exact ⟨_, hlt, by rwa [Pos.get_eq_get_ofSliceTo] at hpget⟩
  · rintro ⟨pos', hlt, hget⟩
    exact ⟨pos.sliceTo pos' (Std.le_of_lt hlt),
      fun h => Std.ne_of_lt hlt (by simpa using congrArg Pos.ofSliceTo h),
      by rw [Pos.get_eq_get_ofSliceTo]; simpa using hget⟩

theorem Pos.Splits.mem_toList_right_iff {s : String} {pos : s.Pos} {t u : String} {c : Char}
    (hs : pos.Splits t u) :
    c ∈ u.toList ↔ ∃ pos', ∃ (_ : pos ≤ pos') (h : pos' ≠ s.endPos), pos'.get h = c := by
  rw [hs.eq_right pos.splits, Slice.mem_toList_copy_iff_exists_get]
  refine ⟨?_, ?_⟩
  · rintro ⟨p, hp, hpget⟩
    exact ⟨Pos.ofSliceFrom p, Pos.le_ofSliceFrom,
      fun h => hp (Pos.ofSliceFrom_inj.mp (h.trans Pos.ofSliceFrom_endPos.symm)),
      by rwa [Pos.get_eq_get_ofSliceFrom] at hpget⟩
  · rintro ⟨pos', hle, hne, hget⟩
    exact ⟨pos.sliceFrom pos' hle,
      fun h => hne (by simpa using congrArg Pos.ofSliceFrom h),
      by rw [Pos.get_eq_get_ofSliceFrom]; simpa using hget⟩

/--
A list of all positions strictly before {name}`p`, ordered from largest to smallest.

This function is not meant to be used in actual programs. Actual programs should use
{name}`Slice.revPositionsFrom` and {name}`Slice.revPositions`.
-/
protected def Model.revPositionsFrom {s : String} (p : s.Pos) : List { p : s.Pos // p ≠ s.endPos } :=
  if h : p = s.startPos then
    []
  else
    ⟨p.prev h, by simp⟩ :: Model.revPositionsFrom (p.prev h)
termination_by p.down

@[simp]
theorem Model.revPositionsFrom_startPos {s : String} : Model.revPositionsFrom s.startPos = [] := by
  simp [Model.revPositionsFrom]

theorem Model.revPositionsFrom_eq_cons {s : String} {p : s.Pos} (hp : p ≠ s.startPos) :
    Model.revPositionsFrom p = ⟨p.prev hp, by simp⟩ :: Model.revPositionsFrom (p.prev hp) := by
  rw [Model.revPositionsFrom]
  simp [hp]

theorem Model.revPositionsFrom_eq_map {s : String} {p : s.Pos} :
    Model.revPositionsFrom p = (Slice.Model.revPositionsFrom p.toSlice).map
      (fun p => ⟨Pos.ofToSlice p.1, by simpa [← Pos.toSlice_inj] using p.2⟩) := by
  induction p using Pos.prev_induction with
  | prev p h ih =>
    rw [revPositionsFrom_eq_cons h, Slice.Model.revPositionsFrom_eq_cons (by simpa [Pos.toSlice_inj])]
    simp only [ne_eq, ih, List.map_cons, List.cons.injEq, Subtype.mk.injEq]
    simp [Pos.prev_toSlice]
  | startPos => simp [← startPos_toSlice]

theorem Model.map_get_revPositionsFrom_of_splits {s : String} {p : s.Pos} {t₁ t₂ : String}
    (hp : p.Splits t₁ t₂) : (Model.revPositionsFrom p).map (fun p => p.1.get p.2) = t₁.toList.reverse := by
  simp [Model.revPositionsFrom_eq_map,
    ← Slice.Model.map_get_revPositionsFrom_of_splits (Pos.splits_toSlice_iff.2 hp)]

theorem Model.map_get_revPositionsFrom_endPos {s : String} :
    (Model.revPositionsFrom s.endPos).map (fun p => p.1.get p.2) = s.toList.reverse :=
  Model.map_get_revPositionsFrom_of_splits (splits_endPos s)

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem toList_revPositionsFrom {s : String} {p : s.Pos} :
    (s.revPositionsFrom p).toList = Model.revPositionsFrom p := by
  simp [revPositionsFrom, Internal.ofToSliceWithProof, Model.revPositionsFrom_eq_map]

@[simp]
theorem toList_revPositions {s : String} :
    s.revPositions.toList = Model.revPositionsFrom s.endPos := by
  simp [revPositions]

@[cbv_eval, simp]
theorem toList_revChars {s : String} : s.revChars.toList = s.toList.reverse := by
  simp [revChars]

theorem forIn_eq_forIn_chars {m : Type u → Type v} [Monad m] {s : String} {b} {f : Char → β → m (ForInStep β)} :
    ForIn.forIn s b f = ForIn.forIn s.chars b f := (rfl)

@[simp]
theorem forIn_eq_forIn_toList {m : Type u → Type v} [Monad m] [LawfulMonad m] {s : String} {b}
    {f : Char → β → m (ForInStep β)} :
    ForIn.forIn s b f = ForIn.forIn s.toList b f := by
  rw [forIn_eq_forIn_chars, ← Std.Iter.forIn_toList, toList_chars]

@[simp]
theorem foldl_eq_foldl_toList {α : Type u} {f : α → Char → α} {init : α} {s : String} :
    s.foldl f init = s.toList.foldl f init := by
  simp [foldl]

@[simp]
theorem foldr_eq_foldr_toList {α : Type u} {f : Char → α → α} {init : α} {s : String} :
    s.foldr f init = s.toList.foldr f init := by
  simp [foldr]

end String
