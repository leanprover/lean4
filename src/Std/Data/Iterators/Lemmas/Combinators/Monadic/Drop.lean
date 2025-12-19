/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Std.Data.Iterators.Combinators.Monadic.Drop
public import Init.Data.Iterators.Lemmas.Consumers.Monadic

@[expose] public section

namespace Std

theorem IterM.step_drop {α m β} [Monad m] [Iterator α m β] {n : Nat}
    {it : IterM (α := α) m β} :
    (it.drop n).step = (do
      match (← it.step).inflate with
      | .yield it' out h =>
        match n with
        | 0 => pure <| .deflate <| .yield (it'.drop 0) out (.yield h rfl)
        | k + 1 => pure <| .deflate <| .skip (it'.drop k) (.drop h rfl)
      | .skip it' h => pure <| .deflate <| .skip (it'.drop n) (.skip h)
      | .done h => pure <| .deflate <| .done (.done h)) := by
  simp only [drop, step, Iterator.step, internalState_toIterM, Nat.succ_eq_add_one]
  apply bind_congr
  intro step
  cases step.inflate using PlausibleIterStep.casesOn
  · cases n <;> rfl
  · rfl
  · rfl

end Std
