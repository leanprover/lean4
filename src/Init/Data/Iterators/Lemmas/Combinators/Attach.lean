/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
import all Init.Data.Iterators.Combinators.Attach
import all Init.Data.Iterators.Combinators.Monadic.Attach
import Init.Data.Iterators.Lemmas.Combinators.Monadic.Attach
import Init.Data.Iterators.Lemmas.Consumers.Collect

namespace Std.Iterators

theorem Iter.unattach_eq_toIter_unattach_toIterM [Iterator α Id β] {it : Iter (α := α) β} {hP} :
    it.attachWith P hP =
      (it.toIterM.attachWith P (fun out h =>
          hP out (isPlausibleIndirectOutput_iff_isPlausibleIndirectOutput_toIterM.mpr h))).toIter := by
  rfl

-- theorem Iter.step_attachWith [Iterator α Id β] {it : Iter (α := α) β} {hP} :
--     (it.attachWith P hP).step =
--       (⟨Types.Attach.modifyStep (it.attachWith P hP) it.step, it.step.toMonadic,
--         (by simp only [Types.Attach.modifyStep])⟩) := by
--   rw [Subtype.ext_iff]
--   simp only [attachWith, IterM.attachWith, step, IterM.Step.toPure, toIterM_toIter, IterM.step,
--     Iterator.step, Id.run_map, Types.Attach.modifyStep, Step.toMonadic, toIter_toIterM,
--     IterStep.mapIterator_mapIterator, toIterM_comp_toIter, IterStep.mapIterator_id]
--   rfl

theorem Iter.unattach_toList_attachWith [Iterator α Id β]
    {it : Iter (α := α) β} {hP}
    [Finite α Id] [IteratorCollect α Id Id]
    [LawfulIteratorCollect α Id Id] :
    (it.attachWith P hP).toList.unattach = it.toList := by
  simp [Iter.unattach_eq_toIter_unattach_toIterM,
    ← Id.run_map (f := List.unattach), IterM.map_unattach_toList_attachWith,
    Iter.toList_eq_toList_toIterM]

@[simp]
theorem Iter.toList_attachWith [Iterator α Id β]
    {it : Iter (α := α) β} {hP}
    [Finite α Id] [IteratorCollect α Id Id]
    [LawfulIteratorCollect α Id Id] :
    (it.attachWith P hP).toList = it.toList.attachWith P
        (fun out h => hP out (isPlausibleIndirectOutput_of_mem_toList h)) := by
  apply List.ext_getElem
  · rw [List.length_attachWith, ← unattach_toList_attachWith (it := it) (hP := hP), List.length_unattach]
  · intro i h₁ h₂
    apply Subtype.ext
    simp only [List.getElem_attachWith, ← unattach_toList_attachWith (it := it) (hP := hP),
      List.getElem_unattach]

theorem Iter.unattach_toListRev_attachWith [Iterator α Id β]
    {it : Iter (α := α) β} {hP}
    [Finite α Id] [IteratorCollect α Id Id]
    [LawfulIteratorCollect α Id Id] :
    (it.attachWith P hP).toListRev.unattach = it.toListRev := by
  simp [toListRev_eq]

@[simp]
theorem Iter.toListRev_attachWith [Iterator α Id β]
    {it : Iter (α := α) β} {hP}
    [Finite α Id] [IteratorCollect α Id Id]
    [LawfulIteratorCollect α Id Id] :
    (it.attachWith P hP).toListRev = it.toListRev.attachWith P
        (fun out h => hP out (isPlausibleIndirectOutput_of_mem_toListRev h)) := by
  simp [toListRev_eq]

@[simp]
theorem Iter.unattach_toArray_attachWith [Iterator α Id β]
    {it : Iter (α := α) β} {hP}
    [Finite α Id] [IteratorCollect α Id Id]
    [LawfulIteratorCollect α Id Id] :
    (it.attachWith P hP).toListRev.unattach = it.toListRev := by
  simp [toListRev_eq]

end Std.Iterators
