/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Iterators.Combinators.Attach
import all Init.Data.Iterators.Combinators.Attach
import all Init.Data.Iterators.Combinators.Monadic.Attach
public import Init.Data.Iterators.Lemmas.Combinators.Monadic.Attach
public import Init.Data.Iterators.Lemmas.Consumers.Collect
public import Init.Data.Iterators.Lemmas.Consumers.Loop
public import Init.Data.Array.Attach

public section

namespace Std
open Std.Iterators

theorem Iter.unattach_eq_toIter_unattach_toIterM [Iterator α Id β] {it : Iter (α := α) β} {hP} :
    it.attachWith P hP =
      (it.toIterM.attachWith P (fun out h =>
          hP out (isPlausibleIndirectOutput_iff_isPlausibleIndirectOutput_toIterM.mpr h))).toIter := by
  rfl

theorem Iter.unattach_toList_attachWith [Iterator α Id β]
    {it : Iter (α := α) β} {hP}
    [Finite α Id] :
    (it.attachWith P hP).toList.unattach = it.toList := by
  simp [Iter.unattach_eq_toIter_unattach_toIterM,
    ← Id.run_map (f := List.unattach), IterM.map_unattach_toList_attachWith,
    Iter.toList_eq_toList_toIterM]

@[simp]
theorem Iter.toList_attachWith [Iterator α Id β]
    {it : Iter (α := α) β} {hP}
    [Finite α Id] :
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
    [Finite α Id] :
    (it.attachWith P hP).toListRev.unattach = it.toListRev := by
  simp [toListRev_eq]

@[simp]
theorem Iter.toListRev_attachWith [Iterator α Id β]
    {it : Iter (α := α) β} {hP}
    [Finite α Id] :
    (it.attachWith P hP).toListRev = it.toListRev.attachWith P
        (fun out h => hP out (isPlausibleIndirectOutput_of_mem_toListRev h)) := by
  simp [toListRev_eq]

@[simp]
theorem Iter.unattach_toArray_attachWith [Iterator α Id β]
    {it : Iter (α := α) β} {hP}
    [Finite α Id] :
    (it.attachWith P hP).toListRev.unattach = it.toListRev := by
  simp [toListRev_eq]

@[simp]
theorem Iter.toArray_attachWith [Iterator α Id β]
    {it : Iter (α := α) β} {hP}
    [Finite α Id] :
    (it.attachWith P hP).toArray = it.toArray.attachWith P
        (fun out h => hP out (isPlausibleIndirectOutput_of_mem_toArray h)) := by
  suffices (it.attachWith P hP).toArray.toList = (it.toArray.attachWith P
      (fun out h => hP out (isPlausibleIndirectOutput_of_mem_toArray h))).toList by
    simpa only [Array.toList_inj]
  simp [Iter.toList_toArray]

@[simp]
theorem Iter.count_attachWith [Iterator α Id β]
    {it : Iter (α := α) β} {hP}
    [Finite α Id] [IteratorLoop α Id Id]
    [LawfulIteratorLoop α Id Id] :
    (it.attachWith P hP).count = it.count := by
  rw [← Iter.length_toList_eq_count, toList_attachWith]
  simp

end Std
