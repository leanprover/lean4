/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Std.Data.Iterators.Consumers.Monadic
import Std.Data.Iterators.Internal.Termination

/-!
# Function-unfolding iterator

This module provides an infinite iterator that given an initial value `init`  function `f` emits
the iterates `init`, `f init`, `f (f init)`, ... .
-/

namespace Std.Iterators

universe u v

variable {α : Type w} {m : Type w → Type w'} {f : α → α}

@[unbox]
structure UnfoldIterator (α : Type u) (f : α → α) where
  next : α

@[always_inline, inline]
instance : Iterator (UnfoldIterator α f) Id α where
  IsPlausibleStep it
    | .yield it' out => out = it.internalState.next ∧ it' = ⟨⟨f it.internalState.next⟩⟩
    | .skip _ => False
    | .done => False
  step it := pure <| .yield ⟨⟨f it.internalState.next⟩⟩ it.internalState.next (by simp)

/--
Creates an infinite iterator from an initial value `init` and a function `f : α → α`.
First it yields `init`, and in each successive step, the iterator applies `f` to the previous value.
So the iterator just emitted `a`, in the next step it will yield `f a`.

For example, if `f := (· + 1)` and `init := 0`, then the iterator emits all natural numbers in
order.

**Termination properties:**

* `Finite` instance: not available and can never be proved
* `Productive` instance: always
-/
@[always_inline, inline]
def Iter.unfold {α : Type w} (init : α) (f : α → α) :=
  (⟨UnfoldIterator.mk (f := f) init⟩ : Iter α)

private def UnfoldIterator.instProductivenessRelation :
    ProductivenessRelation (UnfoldIterator α f) Id where
  rel := emptyWf.rel
  wf := emptyWf.wf
  subrelation {it it'} h := by cases h

instance UnfoldIterator.instProductive :
    Productive (UnfoldIterator α f) Id :=
  Productive.of_productivenessRelation instProductivenessRelation

instance UnfoldIterator.instIteratorLoop {α : Type w} {f : α → α} {n : Type w → Type w'} [Monad n] :
    IteratorLoop (UnfoldIterator α f) Id n :=
  .defaultImplementation

instance UnfoldIterator.instIteratorLoopPartial {α : Type w} {f : α → α} {n : Type w → Type w'}
    [Monad n] : IteratorLoopPartial (UnfoldIterator α f) Id n :=
  .defaultImplementation

instance UnfoldIterator.instIteratorCollect {α : Type w} {f : α → α} {n : Type w → Type w'}
    [Monad n] : IteratorCollect (UnfoldIterator α f) Id n :=
  .defaultImplementation

instance UnfoldIterator.instIteratorCollectPartial {α : Type w} {f : α → α} {n : Type w → Type w'}
    [Monad n] : IteratorCollectPartial (UnfoldIterator α f) Id n :=
  .defaultImplementation

end Std.Iterators
