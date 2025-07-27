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

namespace Std.Iterators

theorem IterM.step_takeWhileWithPostcondition {α m β} [Monad m] [Iterator α m β]
    {it : IterM (α := α) m β} {P} :
    (it.takeWhileWithPostcondition P).step = (do
      match ← it.step with
      | .yield it' out h => match ← (P out).operation with
        | ⟨.up true, h'⟩ => pure <| .yield (it'.takeWhileWithPostcondition P) out (.yield h h')
        | ⟨.up false, h'⟩ => pure <| .done (.rejected h h')
      | .skip it' h => pure <| .skip (it'.takeWhileWithPostcondition P) (.skip h)
      | .done h => pure <| .done (.done h)) := by
  simp only [takeWhileWithPostcondition, step, Iterator.step, internalState_toIterM]
  apply bind_congr
  intro step
  cases step using PlausibleIterStep.casesOn <;> rfl

theorem IterM.step_takeWhileM {α m β} [Monad m] [LawfulMonad m] [Iterator α m β]
    {it : IterM (α := α) m β} {P} :
    (it.takeWhileM P).step = (do
      match ← it.step with
      | .yield it' out h => match ← P out with
        | .up true => pure <| .yield (it'.takeWhileM P) out (.yield h True.intro)
        | .up false => pure <| .done (.rejected h True.intro)
      | .skip it' h => pure <| .skip (it'.takeWhileM P) (.skip h)
      | .done h => pure <| .done (.done h)) := by
  simp only [takeWhileM, step_takeWhileWithPostcondition]
  apply bind_congr
  intro step
  cases step using PlausibleIterStep.casesOn
  · simp only [Function.comp_apply, PostconditionT.operation_lift, PlausibleIterStep.yield,
    PlausibleIterStep.done, bind_map_left]
    apply bind_congr
    rintro ⟨x⟩
    cases x <;> rfl
  · simp
  · simp

theorem IterM.step_takeWhile {α m β} [Monad m] [LawfulMonad m] [Iterator α m β]
    {it : IterM (α := α) m β} {P} :
    (it.takeWhile P).step = (do
      match ← it.step with
      | .yield it' out h => match P out with
        | true => pure <| .yield (it'.takeWhile P) out (.yield h True.intro)
        | false => pure <| .done (.rejected h True.intro)
      | .skip it' h => pure <| .skip (it'.takeWhile P) (.skip h)
      | .done h => pure <| .done (.done h)) := by
  simp only [takeWhile, step_takeWhileM]
  apply bind_congr
  intro step
  cases step using PlausibleIterStep.casesOn
  · simp only [Function.comp_apply, PlausibleIterStep.yield, PlausibleIterStep.done, pure_bind]
    cases P _ <;> rfl
  · simp
  · simp

end Std.Iterators
