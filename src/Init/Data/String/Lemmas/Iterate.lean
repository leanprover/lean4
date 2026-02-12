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

end Slice

@[simp]
theorem toList_chars {s : String} : s.chars.toList = s.toList := by
  simp [chars]

end String
