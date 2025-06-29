/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Std.Data.Iterators.Combinators.Monadic.Take
import Init.Data.Iterators.Lemmas.Consumers.Monadic

namespace Std.Iterators

theorem IterM.step_take {α m β} [Monad m] [Iterator α m β] {n : Nat}
    {it : IterM (α := α) m β} :
    (it.take n).step = (match n with
      | 0 => pure <| .done (.depleted rfl)
      | k + 1 => do
        match ← it.step with
        | .yield it' out h => pure <| .yield (it'.take k) out (.yield h rfl)
        | .skip it' h => pure <| .skip (it'.take (k + 1)) (.skip h rfl)
        | .done h => pure <| .done (.done h)) := by
  simp only [take, step, Iterator.step, internalState_toIterM, Nat.succ_eq_add_one]
  cases n
  case zero => rfl
  case succ k =>
    apply bind_congr
    intro step
    obtain ⟨step, h⟩ := step
    cases step <;> rfl

theorem IterM.toList_take_zero {α m β} [Monad m] [LawfulMonad m] [Iterator α m β]
    [Finite (Take α m β) m]
    [IteratorCollect (Take α m β) m m] [LawfulIteratorCollect (Take α m β) m m]
    {it : IterM (α := α) m β} :
    (it.take 0).toList = pure [] := by
  rw [toList_eq_match_step]
  simp [step_take]

end Std.Iterators
