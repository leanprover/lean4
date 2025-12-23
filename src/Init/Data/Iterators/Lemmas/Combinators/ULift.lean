/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Iterators.Combinators.ULift
import all Init.Data.Iterators.Combinators.ULift
public import Init.Data.Iterators.Lemmas.Combinators.Monadic.ULift
public import Init.Data.Iterators.Lemmas.Consumers.Collect
public import Init.Data.Iterators.Lemmas.Consumers.Loop

public section

namespace Std
open Std.Iterators

variable {α : Type u} {β : Type u}

theorem Iter.uLift_eq_toIter_uLift_toIterM {it : Iter (α := α) β} :
    it.uLift = (it.toIterM.uLift Id).toIter :=
  rfl

theorem Iter.step_uLift [Iterator α Id β] {it : Iter (α := α) β} :
    it.uLift.step = match it.step with
      | .yield it' out h => .yield it'.uLift (.up out) ⟨_, h, rfl⟩
      | .skip it' h => .skip it'.uLift ⟨_, h, rfl⟩
      | .done h => .done ⟨_, h, rfl⟩ := by
  rw [Subtype.ext_iff]
  simp only [uLift_eq_toIter_uLift_toIterM, step, IterM.Step.toPure, toIterM_toIter,
    IterM.step_uLift, toIter_toIterM]
  simp only [monadLift, ULiftT.run_pure, PlausibleIterStep.yield, PlausibleIterStep.skip,
    PlausibleIterStep.done, pure_bind]
  cases it.toIterM.step.run.inflate using PlausibleIterStep.casesOn <;> simp

@[simp]
theorem Iter.toList_uLift [Iterator α Id β] {it : Iter (α := α) β}
    [Finite α Id] :
    it.uLift.toList = it.toList.map ULift.up := by
  simp only [monadLift, uLift_eq_toIter_uLift_toIterM, IterM.toList_toIter]
  rw [IterM.toList_uLift]
  simp [monadLift, Iter.toList_eq_toList_toIterM]

@[simp]
theorem Iter.toListRev_uLift [Iterator α Id β] {it : Iter (α := α) β}
    [Finite α Id] :
    it.uLift.toListRev = it.toListRev.map ULift.up := by
  rw [toListRev_eq, toListRev_eq, toList_uLift, List.map_reverse]

@[simp]
theorem Iter.toArray_uLift [Iterator α Id β] {it : Iter (α := α) β}
    [Finite α Id] :
    it.uLift.toArray = it.toArray.map ULift.up := by
  rw [← toArray_toList, ← toArray_toList, toList_uLift]
  simp [-toArray_toList]

@[simp]
theorem Iter.count_uLift [Iterator α Id β] {it : Iter (α := α) β}
    [Finite α Id] [IteratorLoop α Id Id] [LawfulIteratorLoop α Id Id] :
    it.uLift.count = it.count := by
  simp only [monadLift, uLift_eq_toIter_uLift_toIterM, count_eq_count_toIterM, toIterM_toIter]
  rw [IterM.count_uLift]
  simp [monadLift]

end Std
