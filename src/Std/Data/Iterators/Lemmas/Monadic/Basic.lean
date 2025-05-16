/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Std.Data.Iterators.Basic

namespace Std.Iterators

/--
Induction principle for finite monadic iterators: One can define a function `f` that maps every
iterator `it` to an element of `motive it` by defining `f it` in terms of the values of `f` on
the plausible successors of `it'.
-/
@[specialize]
def IterM.induct {α m β} [Iterator α m β] [Finite α m]
  (motive : IterM (α := α) m β → Sort x)
  (step : (it : IterM (α := α) m β) →
    (ih_yield : ∀ {it' : IterM (α := α) m β} {out : β},
      it.plausible_step (.yield it' out) → motive it') →
    (ih_skip : ∀ {it' : IterM (α := α) m β}, it.plausible_step (.skip it') → motive it' ) →
    motive it)
  (it : IterM (α := α) m β) : motive it :=
  step it
    (fun {it' _} _ => IterM.induct motive step it')
    (fun {it'} _ => IterM.induct motive step it')
termination_by it.finitelyManySteps

end Std.Iterators
