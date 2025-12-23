/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Iterators.Combinators.Monadic.Take
public import Init.Data.Iterators.Lemmas.Consumers.Monadic

@[expose] public section

namespace Std
open Std.Iterators Std.Iterators.Types

namespace Iterators.Types

theorem Take.isPlausibleStep_take_yield [Monad m] [Iterator α m β] {n : Nat}
    {it : IterM (α := α) m β} (h : it.IsPlausibleStep (.yield it' out)) :
    (it.take (n + 1)).IsPlausibleStep (.yield (it'.take n) out) :=
  (.yield h (by simp [IterM.take]))

theorem Take.isPlausibleStep_take_skip [Monad m] [Iterator α m β] {n : Nat}
    {it : IterM (α := α) m β} (h : it.IsPlausibleStep (.skip it')) :
    (it.take (n + 1)).IsPlausibleStep (.skip (it'.take (n + 1))) :=
  (.skip h (by simp [IterM.take]))

end Iterators.Types

theorem IterM.step_take {α m β} [Monad m] [Iterator α m β] {n : Nat}
    {it : IterM (α := α) m β} :
    (it.take n).step = (match n with
      | 0 => pure <| .deflate <| .done (.depleted rfl)
      | k + 1 => do
        match (← it.step).inflate with
        | .yield it' out h => pure <| .deflate <| .yield (it'.take k) out (Take.isPlausibleStep_take_yield h)
        | .skip it' h => pure <| .deflate <| .skip (it'.take (k + 1)) (Take.isPlausibleStep_take_skip h)
        | .done h => pure <| .deflate <| .done (.done h)) := by
  simp only [take, step, Iterator.step, internalState_toIterM]
  cases n
  case zero => rfl
  case succ k =>
    apply bind_congr
    intro step
    cases step.inflate using PlausibleIterStep.casesOn <;> rfl

theorem IterM.toList_take_zero {α m β} [Monad m] [LawfulMonad m] [Iterator α m β]
    [Finite (Take α m) m]
    {it : IterM (α := α) m β} :
    (it.take 0).toList = pure [] := by
  rw [toList_eq_match_step]
  simp [step_take]

theorem IterM.step_toTake {α m β} [Monad m] [Iterator α m β] [Finite α m]
    {it : IterM (α := α) m β} :
    it.toTake.step = (do
        match (← it.step).inflate with
        | .yield it' out h => pure <| .deflate <| .yield it'.toTake out (.yield h Nat.zero_ne_one)
        | .skip it' h => pure <| .deflate <| .skip it'.toTake (.skip h Nat.zero_ne_one)
        | .done h => pure <| .deflate <| .done (.done h)) := by
  simp only [toTake, step, Iterator.step, internalState_toIterM]
  apply bind_congr
  intro step
  cases step.inflate using PlausibleIterStep.casesOn <;> rfl

@[simp]
theorem IterM.toList_toTake {α m β} [Monad m] [LawfulMonad m] [Iterator α m β] [Finite α m]
    {it : IterM (α := α) m β} :
    it.toTake.toList = it.toList := by
  induction it using IterM.inductSteps with | step it ihy ihs
  rw [toList_eq_match_step, toList_eq_match_step]
  simp only [step_toTake, bind_assoc]
  apply bind_congr; intro step
  cases step.inflate using PlausibleIterStep.casesOn
  · simp [ihy ‹_›]
  · simp [ihs ‹_›]
  · simp

end Std
