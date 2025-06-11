/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
import Init.Data.Iterators.Consumers.Monadic
import Init.Data.Iterators.Internal.Termination

/-!
# Function-unfolding iterator

This module provides an infinite iterator that, given an initial value `init` and a function `f`,
emits the iterates `init`, `f init`, `f (f init)`, and so on.
-/

namespace Std.Iterators

universe u v

variable {α : Type w} {m : Type w → Type w'} {f : α → Option α}

/--
Internal state of the `repeat` combinator. Do not depend on its internals.
-/
@[unbox]
structure RepeatIterator (α : Type u) (f : α → Option α) where
  /-- Internal implementation detail of the iterator library. -/
  next : α

@[always_inline, inline]
instance : Iterator (RepeatIterator α f) Id α where
  IsPlausibleStep it
    | .yield it' out => out = it.internalState.next ∧ ∃ a, f it.internalState.next = some a ∧ it' = ⟨⟨a⟩⟩
    | .skip _ => False
    | .done => f it.internalState.next = none
  step it := match f it.internalState.next with
    | none => pure <| .done rfl
    | some a => pure <| .yield ⟨⟨a⟩⟩ it.internalState.next (by simp)

/--
Creates an iterator from an initial value `init` and a function `f : α → Option α`.
First it yields `init`, and in each successive step, the iterator applies `f` to the previous value.
If `f` returns `some a`, the iterator emits `a`, and otherwise terminates.

**Termination properties:**

* `Finite` instance: not available but provable in some cases
* `Productive` instance: always
-/
@[always_inline, inline]
def Iter.repeatUntilNone {α : Type w} (f : α → Option α) (init : α) :=
  (⟨RepeatIterator.mk (f := f) init⟩ : Iter α)

/--
Creates an infinite iterator from an initial value `init` and a function `f : α → α`.
First it yields `init`, and in each successive step, the iterator applies `f` to the previous value.
So if the iterator just emitted `a`, in the next step it will yield `f a`. In other words, the
`n`-th value is `Nat.repeat f n init`.

For example, if `f := (· + 1)` and `init := 0`, then the iterator emits all natural numbers in
order.

**Termination properties:**

* `Finite` instance: not available and never possible
* `Productive` instance: always
-/
@[always_inline, inline]
def Iter.repeat {α : Type w} (f : α → α) (init : α) :=
  Iter.repeatUntilNone (fun a => some (f a)) init

private def RepeatIterator.instProductivenessRelation :
    ProductivenessRelation (RepeatIterator α f) Id where
  rel := emptyWf.rel
  wf := emptyWf.wf
  subrelation {it it'} h := by cases h

instance RepeatIterator.instProductive :
    Productive (RepeatIterator α f) Id := by
  exact Productive.of_productivenessRelation instProductivenessRelation

instance RepeatIterator.instIteratorLoop {α : Type w} {f : α → Option α} {n : Type w → Type w'} [Monad n] :
    IteratorLoop (RepeatIterator α f) Id n :=
  .defaultImplementation

instance RepeatIterator.instIteratorLoopPartial {α : Type w} {f : α → Option α} {n : Type w → Type w'}
    [Monad n] : IteratorLoopPartial (RepeatIterator α f) Id n :=
  .defaultImplementation

instance RepeatIterator.instIteratorCollect {α : Type w} {f : α → Option α} {n : Type w → Type w'}
    [Monad n] : IteratorCollect (RepeatIterator α f) Id n :=
  .defaultImplementation

instance RepeatIterator.instIteratorCollectPartial {α : Type w} {f : α → Option α} {n : Type w → Type w'}
    [Monad n] : IteratorCollectPartial (RepeatIterator α f) Id n :=
  .defaultImplementation

theorem RepeatIterator.Monadic.next_eq_some_of_isPlausibleSuccessorOf {f : α → Option α}
    {it' it : IterM (α := RepeatIterator α f) Id α} (h : it'.IsPlausibleSuccessorOf it) :
    f it.internalState.next = some it'.internalState.next := by
  rcases h with ⟨step, h, h'⟩
  cases step
  · cases h
    rcases h' with ⟨rfl, a, ha, h'⟩
    simp_all [Iter.toIterM]
  · cases h'
  · cases h

theorem RepeatIterator.next_eq_some_of_isPlausibleSuccessorOf {f : α → Option α}
    {it' it : Iter (α := RepeatIterator α f) α} (h : it'.IsPlausibleSuccessorOf it) :
    f it.internalState.next = some it'.internalState.next := by
  exact RepeatIterator.Monadic.next_eq_some_of_isPlausibleSuccessorOf h

end Std.Iterators
