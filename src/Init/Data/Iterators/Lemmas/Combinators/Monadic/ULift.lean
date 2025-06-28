/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import all Init.Data.Iterators.Combinators.Monadic.ULift
public import Init.Data.Iterators.Lemmas.Consumers.Monadic.Collect

public section

namespace Std.Iterators

variable {α : Type u} {m : Type u → Type u'} {n : Type max u v → Type v'}
    {β : Type u}

theorem IterM.step_uLift [Iterator α m β] [Monad n] {it : IterM (α := α) m β}
    [MonadLiftT m (ULiftT n)] :
    (it.uLift n).step = (do
      let step := (← (monadLift it.step : ULiftT n _).run).down
      return ⟨Types.ULiftIterator.Monadic.modifyStep step.val, step.val, step.property, rfl⟩) :=
  rfl

@[simp]
theorem IterM.toList_uLift [Iterator α m β] [Monad m] [Monad n] {it : IterM (α := α) m β}
    [MonadLiftT m (ULiftT n)] [Finite α m] [IteratorCollect α m m]
    [LawfulMonad m] [LawfulMonad n] [LawfulIteratorCollect α m m]
    [LawfulMonadLiftT m (ULiftT n)] :
    (it.uLift n).toList =
      (fun l => l.down.map ULift.up) <$> (monadLift it.toList : ULiftT n _).run := by
  induction it using IterM.inductSteps with | step it ihy ihs
  rw [IterM.toList_eq_match_step, IterM.toList_eq_match_step, step_uLift]
  simp only [bind_pure_comp, bind_map_left, liftM_bind, ULiftT.run_bind, map_bind]
  apply bind_congr
  intro step
  simp [Types.ULiftIterator.Monadic.modifyStep]
  cases step.down using PlausibleIterStep.casesOn
  · simp only [uLift] at ihy
    simp [ihy ‹_›]
  · exact ihs ‹_›
  · simp

@[simp]
theorem IterM.toListRev_uLift [Iterator α m β] [Monad m] [Monad n] {it : IterM (α := α) m β}
    [MonadLiftT m (ULiftT n)] [Finite α m] [IteratorCollect α m m]
    [LawfulMonad m] [LawfulMonad n] [LawfulIteratorCollect α m m]
    [LawfulMonadLiftT m (ULiftT n)] :
    (it.uLift n).toListRev =
      (fun l => l.down.map ULift.up) <$> (monadLift it.toListRev : ULiftT n _).run := by
  rw [toListRev_eq, toListRev_eq, toList_uLift, monadLift_map]
  simp

@[simp]
theorem IterM.toArray_uLift [Iterator α m β] [Monad m] [Monad n] {it : IterM (α := α) m β}
    [MonadLiftT m (ULiftT n)] [Finite α m] [IteratorCollect α m m]
    [LawfulMonad m] [LawfulMonad n] [LawfulIteratorCollect α m m]
    [LawfulMonadLiftT m (ULiftT n)] :
    (it.uLift n).toArray =
      (fun l => l.down.map ULift.up) <$> (monadLift it.toArray : ULiftT n _).run := by
  rw [← toArray_toList, ← toArray_toList, toList_uLift, monadLift_map]
  simp

end Std.Iterators
