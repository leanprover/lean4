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

set_option doc.verso true

public section

namespace String

namespace Slice

/--
A list of all positions starting at {name}`p`.

This function is not meant to be used in actual progams. Actual programs should use
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

@[simp]
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

@[simp]
theorem toList_chars {s : Slice} : s.chars.toList = s.copy.toList := by
  simp [chars, Model.map_get_positionsFrom_startPos]

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

@[simp]
theorem toList_revChars {s : Slice} : s.revChars.toList = s.copy.toList.reverse := by
  simp [revChars, Model.map_get_revPositionsFrom_endPos]

theorem forIn_eq_forIn_chars {m : Type u → Type v} [Monad m] {s : Slice} {b} {f : Char → β → m (ForInStep β)} :
    ForIn.forIn s b f = ForIn.forIn s.chars b f := rfl

@[simp]
theorem forIn_eq_forIn_toList {m : Type u → Type v} [Monad m] [LawfulMonad m] {s : Slice} {b}
    {f : Char → β → m (ForInStep β)} :
    ForIn.forIn s b f = ForIn.forIn s.copy.toList b f := by
  rw [forIn_eq_forIn_chars, ← Std.Iter.forIn_toList, toList_chars]

end Slice

/--
A list of all positions starting at {name}`p`.

This function is not meant to be used in actual progams. Actual programs should use
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

@[simp]
theorem toList_positionsFrom {s : String} {p : s.Pos} :
    (s.positionsFrom p).toList = Model.positionsFrom p := by
  simp [positionsFrom, Internal.ofToSliceWithProof, Model.positionsFrom_eq_map]

theorem toList_positions {s : String} : s.positions.toList = Model.positionsFrom s.startPos := by
  simp [positions]

@[simp]
theorem toList_chars {s : String} : s.chars.toList = s.toList := by
  simp [chars]

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

@[simp]
theorem toList_revPositionsFrom {s : String} {p : s.Pos} :
    (s.revPositionsFrom p).toList = Model.revPositionsFrom p := by
  simp [revPositionsFrom, Internal.ofToSliceWithProof, Model.revPositionsFrom_eq_map]

@[simp]
theorem toList_revPositions {s : String} :
    s.revPositions.toList = Model.revPositionsFrom s.endPos := by
  simp [revPositions]

@[simp]
theorem toList_revChars {s : String} : s.revChars.toList = s.toList.reverse := by
  simp [revChars]

theorem forIn_eq_forIn_chars {m : Type u → Type v} [Monad m] {s : String} {b} {f : Char → β → m (ForInStep β)} :
    ForIn.forIn s b f = ForIn.forIn s.chars b f := (rfl)

@[simp]
theorem forIn_eq_forIn_toList {m : Type u → Type v} [Monad m] [LawfulMonad m] {s : String} {b}
    {f : Char → β → m (ForInStep β)} :
    ForIn.forIn s b f = ForIn.forIn s.toList b f := by
  rw [forIn_eq_forIn_chars, ← Std.Iter.forIn_toList, toList_chars]

end String
