/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Iterators.Combinators.Monadic.ULift
public import Init.Data.Iterators.Lemmas.Consumers.Monadic.Collect
public import Init.Data.Iterators.Lemmas.Consumers.Monadic.Loop

public section

namespace Std
open Std.Iterators

variable {α : Type u} {m : Type u → Type u'} {n : Type max u v → Type v'}
    {β : Type u}

theorem IterM.step_uLift [Iterator α m β] [Monad n] {it : IterM (α := α) m β}
    [MonadLiftT m (ULiftT n)] :
    (it.uLift n).step = (do
      match (← (monadLift it.step : ULiftT n _).run).down.inflate with
      | .yield it' out h => return .deflate (.yield (it'.uLift n) (.up out) ⟨_, h, rfl⟩)
      | .skip it' h => return .deflate (.skip (it'.uLift n) ⟨_, h, rfl⟩)
      | .done h => return .deflate (.done ⟨_, h, rfl⟩)) := by
  simp only [IterM.step, Iterator.step, IterM.uLift]
  apply bind_congr; intro step
  split <;> simp [Types.ULiftIterator.Monadic.modifyStep, *]

@[simp]
theorem IterM.toList_uLift [Iterator α m β] [Monad m] [Monad n] {it : IterM (α := α) m β}
    [MonadLiftT m (ULiftT n)] [Finite α m]
    [LawfulMonad m] [LawfulMonad n]
    [LawfulMonadLiftT m (ULiftT n)] :
    (it.uLift n).toList =
      (fun l => l.down.map ULift.up) <$> (monadLift it.toList : ULiftT n _).run := by
  induction it using IterM.inductSteps with | step it ihy ihs
  rw [IterM.toList_eq_match_step, IterM.toList_eq_match_step, step_uLift]
  simp only [bind_assoc, map_eq_pure_bind, monadLift_bind, ULiftT.run_bind]
  apply bind_congr; intro step
  cases step.down.inflate using PlausibleIterStep.casesOn
  · simp [ihy ‹_›]
  · simp [ihs ‹_›]
  · simp

@[simp]
theorem IterM.toListRev_uLift [Iterator α m β] [Monad m] [Monad n] {it : IterM (α := α) m β}
    [MonadLiftT m (ULiftT n)] [Finite α m]
    [LawfulMonad m] [LawfulMonad n]
    [LawfulMonadLiftT m (ULiftT n)] :
    (it.uLift n).toListRev =
      (fun l => l.down.map ULift.up) <$> (monadLift it.toListRev : ULiftT n _).run := by
  rw [toListRev_eq, toListRev_eq, toList_uLift, monadLift_map]
  simp

@[simp]
theorem IterM.toArray_uLift [Iterator α m β] [Monad m] [Monad n] {it : IterM (α := α) m β}
    [MonadLiftT m (ULiftT n)] [Finite α m]
    [LawfulMonad m] [LawfulMonad n]
    [LawfulMonadLiftT m (ULiftT n)] :
    (it.uLift n).toArray =
      (fun l => l.down.map ULift.up) <$> (monadLift it.toArray : ULiftT n _).run := by
  rw [← toArray_toList, ← toArray_toList, toList_uLift, monadLift_map]
  simp

@[simp]
theorem IterM.count_uLift [Iterator α m β] [Monad m] [Monad n] {it : IterM (α := α) m β}
    [MonadLiftT m (ULiftT n)] [Finite α m] [IteratorLoop α m m]
    [LawfulMonad m] [LawfulMonad n] [LawfulIteratorLoop α m m]
    [LawfulMonadLiftT m (ULiftT n)] :
    (it.uLift n).count =
      (.up ·.down.down) <$> (monadLift (n := ULiftT n) it.count).run := by
  induction it using IterM.inductSteps with | step it ihy ihs
  rw [count_eq_match_step, count_eq_match_step, monadLift_bind, map_eq_pure_bind, step_uLift]
  simp only [bind_assoc, ULiftT.run_bind]
  apply bind_congr; intro step
  cases step.down.inflate using PlausibleIterStep.casesOn
  · simp [ihy ‹_›]
  · simp [ihs ‹_›]
  · simp

end Std
