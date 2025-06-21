/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Init.Data.Nat.Lemmas
import Init.RCases
import Init.Data.Iterators.Consumers
import Init.Data.Iterators.Internal.Termination

/-!
# List iterator

This module provides an iterator for lists that is accessible via `List.iterM`.
-/

namespace Std.Iterators

variable {α : Type w} {m : Type w → Type w'} {n : Type w → Type w''}

/--
The underlying state of a list iterator. Its contents are internal and should
not be used by downstream users of the library.
-/
@[ext]
structure ListIterator (α : Type w) where
  list : List α

/--
Returns a finite iterator for the given list.
The iterator yields the elements of the list in order and then terminates.
-/
@[always_inline, inline]
def _root_.List.iterM {α : Type w} (l : List α) (m : Type w → Type w') [Pure m] :
    IterM (α := ListIterator α) m α :=
  toIterM { list := l } m α

@[always_inline, inline]
instance {α : Type w} [Pure m] : Iterator (ListIterator α) m α where
  IsPlausibleStep it
    | .yield it' out => it.internalState.list = out :: it'.internalState.list
    | .skip _ => False
    | .done => it.internalState.list = []
  step it := pure (match it with
        | ⟨⟨[]⟩⟩ => ⟨.done, rfl⟩
        | ⟨⟨x :: xs⟩⟩ => ⟨.yield (toIterM ⟨xs⟩ m α) x, rfl⟩)

private def ListIterator.finitenessRelation [Pure m] :
    FinitenessRelation (ListIterator α) m where
  rel := InvImage WellFoundedRelation.rel (ListIterator.list ∘ IterM.internalState)
  wf := InvImage.wf _ WellFoundedRelation.wf
  subrelation {it it'} h := by
    simp_wf
    obtain ⟨step, h, h'⟩ := h
    cases step <;> simp_all [IterStep.successor, IterM.IsPlausibleStep, Iterator.IsPlausibleStep]

instance [Pure m] : Finite (ListIterator α) m :=
  Finite.of_finitenessRelation ListIterator.finitenessRelation

@[always_inline, inline]
instance {α : Type w} [Monad m] [Monad n] : IteratorCollect (ListIterator α) m n :=
  .defaultImplementation

@[always_inline, inline]
instance {α : Type w} [Monad m] [Monad n] : IteratorCollectPartial (ListIterator α) m n :=
  .defaultImplementation

@[always_inline, inline]
instance {α : Type w} [Monad m] [Monad n] : IteratorLoop (ListIterator α) m n :=
  .defaultImplementation

@[always_inline, inline]
instance {α : Type w} [Monad m] [Monad n] : IteratorLoopPartial (ListIterator α) m n :=
  .defaultImplementation

end Std.Iterators
