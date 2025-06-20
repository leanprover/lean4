/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
import Init.Data.Iterators.Basic

namespace Std.Iterators

inductive IterM.IsPlausibleNthOutput {α β : Type w} {m : Type w → Type w'} [Iterator α m β] :
    Nat → IterM (α := α) m β → IterStep (IterM (α := α) m β) β → Prop where
  | zero_yield {it : IterM (α := α) m β} : it.IsPlausibleStep (.yield it' out) →
      it.IsPlausibleNthOutput 0 (.yield it' out)
  | done {it : IterM (α := α) m β} : it.IsPlausibleStep .done →
      it.IsPlausibleNthOutput n .done
  | yield {it it' : IterM (α := α) m β} {out step} : it.IsPlausibleStep (.yield it' out) →
      it'.IsPlausibleNthOutput n step → it.IsPlausibleNthOutput (n + 1) step
  | skip {it it' : IterM (α := α) m β} {step} : it.IsPlausibleStep (.skip it') →
      it'.IsPlausibleNthOutput n step → it.IsPlausibleNthOutput n step

class IteratorAccess (α : Type w) (m : Type w → Type w') {β : Type w} [Iterator α m β] where
  nextAtIdx? (it : IterM (α := α) m β) (n : Nat) : m (PlausibleIterStep (it.IsPlausibleNthOutput n))

@[always_inline, inline]
def IterM.nextAtIdx? [Iterator α m β] [IteratorAccess α m] (it : IterM (α := α) m β)
    (n : Nat) : m (PlausibleIterStep (it.IsPlausibleNthOutput n)) :=
  IteratorAccess.nextAtIdx? it n

end Std.Iterators
