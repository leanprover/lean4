/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import all Init.Data.Iterators.Combinators.Monadic.Attach
public import Init.Data.Iterators.Lemmas.Consumers.Monadic.Collect

public section

namespace Std.Iterators

variable {α : Type w} {m : Type w → Type w'} {β : Type w} {P : β → Prop}

theorem IterM.step_attachWith [Iterator α m β] [Monad m] {it : IterM (α := α) m β} {hP} :
    (it.attachWith P hP).step =
      (fun s => ⟨Types.Attach.Monadic.modifyStep (it.attachWith P hP) s, s, rfl⟩) <$> it.step :=
  rfl

@[simp]
theorem IterM.map_unattach_toList_attachWith [Iterator α m β] [Monad m]
    {it : IterM (α := α) m β} {hP}
    [Finite α m] [IteratorCollect α m m]
    [LawfulMonad m] [LawfulIteratorCollect α m m] :
    List.unattach <$> (it.attachWith P hP).toList = it.toList := by
  induction it using IterM.inductSteps with | step it ihy ihs
  rw [IterM.toList_eq_match_step, IterM.toList_eq_match_step, step_attachWith]
  simp only [bind_pure_comp, bind_map_left, map_bind]
  apply bind_congr
  intro step
  cases step using PlausibleIterStep.casesOn
  · rename_i it' out hp
    simp only [IterM.attachWith] at ihy
    simp [Types.Attach.Monadic.modifyStep,
      ← ihy ‹_› (hP := fun out h => hP out (.indirect ⟨_, rfl, hp⟩ h))]
  · simp only [IterM.attachWith] at ihs
    simp [Types.Attach.Monadic.modifyStep, ihs ‹_›]
  · simp [Types.Attach.Monadic.modifyStep]

@[simp]
theorem IterM.map_unattach_toListRev_attachWith [Iterator α m β] [Monad m] [Monad n]
    {it : IterM (α := α) m β} {hP}
    [Finite α m] [IteratorCollect α m m]
    [LawfulMonad m] [LawfulIteratorCollect α m m] :
    List.unattach <$> (it.attachWith P hP).toListRev = it.toListRev := by
  rw [toListRev_eq, toListRev_eq, ← map_unattach_toList_attachWith (it := it) (hP := hP)]
  simp [-map_unattach_toList_attachWith]

@[simp]
theorem IterM.map_unattach_toArray_attachWith [Iterator α m β] [Monad m] [Monad n]
    {it : IterM (α := α) m β} {hP}
    [Finite α m] [IteratorCollect α m m]
    [LawfulMonad m] [LawfulIteratorCollect α m m] :
    (·.map Subtype.val) <$> (it.attachWith P hP).toArray = it.toArray := by
  rw [← toArray_toList, ← toArray_toList, ← map_unattach_toList_attachWith (it := it) (hP := hP)]
  simp [-map_unattach_toList_attachWith]

end Std.Iterators
