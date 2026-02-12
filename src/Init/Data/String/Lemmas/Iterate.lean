/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

prelude
public import Init.Data.String.Iterate
public import Init.Data.Iterators.Consumers.Collect
import all Init.Data.String.Iterate
import Init.Data.String.Termination
import Init.Data.Iterators.Lemmas.Consumers.Collect
import Init.ByCases

public section

namespace String

namespace Slice

/-- -/
def Internal.positionsListFrom {s : Slice} (p : s.Pos) : List { p : s.Pos // p ≠ s.endPos } :=
  if h : p.IsAtEnd then
    []
  else
    ⟨p, h⟩ :: positionsListFrom (p.next h)
termination_by p

@[simp]
theorem Internal.positionsListFrom_endPos {s : Slice} : Internal.positionsListFrom s.endPos = [] := by
  simp [Internal.positionsListFrom]

theorem Internal.positionsListFrom_eq_cons {s : Slice} {p : s.Pos} (hp : p ≠ s.endPos) :
    Internal.positionsListFrom p = ⟨p, hp⟩ :: Internal.positionsListFrom (p.next hp) := by
  rw [Internal.positionsListFrom]
  simp [hp]

theorem Internal.map_get_positionsListFrom {s : Slice} :
    (Internal.positionsListFrom s.startPos).map (fun p => p.1.get p.2) = s.copy.toList := sorry

@[simp]
theorem toList_positions {s : Slice} : s.positions.toList = Internal.positionsListFrom s.startPos := by
  suffices ∀ (p : s.Pos), (Std.Iter.mk (PosIterator.mk p)).toList = Internal.positionsListFrom p by
    simp [positions, this]
  intro p
  induction p using WellFounded.induction Pos.wellFounded_gt with | h p ih
  rw [Std.Iter.toList_eq_match_step, Std.Iter.step_eq]
  simp only [ne_eq, Std.Iter.toIterM_mk, Std.IterM.internalState_mk]
  by_cases h : p = s.endPos
  · simp [h]
  · simp [h, ih (p.next h) (by simp), Internal.positionsListFrom_eq_cons]

end Slice

end String
