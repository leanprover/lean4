/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import all Init.Data.Iterators.Combinators.ULift
public import Init.Data.Iterators.Lemmas.Combinators.Monadic.ULift
public import Init.Data.Iterators.Lemmas.Consumers.Collect

public section

namespace Std.Iterators

variable {α : Type u} {β : Type u}

theorem Iter.uLift_eq_toIter_uLift_toIterM {it : Iter (α := α) β} :
    it.uLift = (it.toIterM.uLift Id).toIter :=
  rfl

theorem Iter.step_uLift [Iterator α Id β] {it : Iter (α := α) β} :
    it.uLift.step =
      ⟨Types.ULiftIterator.modifyStep it.step.val,
        it.step.val.mapIterator Iter.toIterM, it.step.property,
        by simp [Types.ULiftIterator.modifyStep]⟩ := by
  rw [Subtype.ext_iff]
  simp only [uLift_eq_toIter_uLift_toIterM, step, IterM.Step.toPure, toIterM_toIter,
    IterM.step_uLift, bind_pure_comp, Id.run_map, toIter_toIterM]
  simp [Types.ULiftIterator.modifyStep, monadLift]

@[simp]
theorem Iter.toList_uLift [Iterator α Id β] {it : Iter (α := α) β}
    [Finite α Id] [IteratorCollect α Id Id]
    [LawfulIteratorCollect α Id Id] :
    it.uLift.toList = it.toList.map ULift.up := by
  simp only [monadLift, uLift_eq_toIter_uLift_toIterM, IterM.toList_toIter]
  rw [IterM.toList_uLift]
  simp [monadLift, Iter.toList_eq_toList_toIterM]

@[simp]
theorem Iter.toListRev_uLift [Iterator α Id β] {it : Iter (α := α) β}
    [Finite α Id] [IteratorCollect α Id Id]
    [LawfulIteratorCollect α Id Id] :
    it.uLift.toListRev = it.toListRev.map ULift.up := by
  rw [toListRev_eq, toListRev_eq, toList_uLift, List.map_reverse]

@[simp]
theorem Iter.toArray_uLift [Iterator α Id β] {it : Iter (α := α) β}
    [Finite α Id] [IteratorCollect α Id Id]
    [LawfulIteratorCollect α Id Id] :
    it.uLift.toArray = it.toArray.map ULift.up := by
  rw [← toArray_toList, ← toArray_toList, toList_uLift]
  simp

end Std.Iterators
