/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Std.Data.Iterators.Combinators.Monadic.TakeWhile
public import Std.Data.Iterators.Lemmas.Consumers.Monadic

@[expose] public section

namespace Std
open Std.Iterators

theorem IterM.step_takeWhileWithPostcondition {α m β} [Monad m] [Iterator α m β]
    {it : IterM (α := α) m β} {P} :
    (it.takeWhileWithPostcondition P).step = (do
      match (← it.step).inflate with
      | .yield it' out h => match ← (P out).operation with
        | ⟨.up true, h'⟩ => pure <| .deflate <| .yield (it'.takeWhileWithPostcondition P) out (.yield h h')
        | ⟨.up false, h'⟩ => pure <| .deflate <| .done (.rejected h h')
      | .skip it' h => pure <| .deflate <| .skip (it'.takeWhileWithPostcondition P) (.skip h)
      | .done h => pure <| .deflate <| .done (.done h)) := by
  simp only [takeWhileWithPostcondition, step, Iterator.step, internalState_toIterM]
  apply bind_congr
  intro step
  cases step.inflate using PlausibleIterStep.casesOn <;> rfl

theorem IterM.step_takeWhileM {α m β} [Monad m] [MonadAttach m] [LawfulMonad m] [Iterator α m β]
    {it : IterM (α := α) m β} {P} :
    (it.takeWhileM P).step = (do
      match (← it.step).inflate with
      | .yield it' out h => match ← MonadAttach.attach (P out) with
        | ⟨.up true, hP⟩ => pure <| .deflate <| .yield (it'.takeWhileM P) out (.yield h hP)
        | ⟨.up false, hP⟩ => pure <| .deflate <| .done (.rejected h hP)
      | .skip it' h => pure <| .deflate <| .skip (it'.takeWhileM P) (.skip h)
      | .done h => pure <| .deflate <| .done (.done h)) := by
  simp only [takeWhileM, step_takeWhileWithPostcondition]
  apply bind_congr
  intro step
  cases step.inflate using PlausibleIterStep.casesOn
  · simp only [Function.comp_apply, PostconditionT.operation_attachLift, PlausibleIterStep.yield,
    PlausibleIterStep.done]
    apply bind_congr
    rintro ⟨⟨x⟩, hx⟩
    cases x <;> rfl
  · simp
  · simp

theorem IterM.step_takeWhile {α m β} [Monad m] [LawfulMonad m] [Iterator α m β]
    {it : IterM (α := α) m β} {P} :
    (it.takeWhile P).step = (do
      match (← it.step).inflate with
      | .yield it' out h => match hP : P out with
        | true => pure <| .deflate <| .yield (it'.takeWhile P) out (.yield h (by simpa))
        | false => pure <| .deflate <| .done (.rejected h (by simpa))
      | .skip it' h => pure <| .deflate <| .skip (it'.takeWhile P) (.skip h)
      | .done h => pure <| .deflate <| .done (.done h)) := by
  simp only [takeWhile, step_takeWhileWithPostcondition]
  apply bind_congr
  intro step
  cases step.inflate using PlausibleIterStep.casesOn
  · simp only [Function.comp_apply, PlausibleIterStep.yield, PlausibleIterStep.done,
      PostconditionT.operation_pure, pure_bind]
    split <;> split <;> simp_all
  · simp
  · simp

end Std
