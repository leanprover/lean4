/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Iterators.Consumers

@[expose] public section

/-!
# List iterator

This module provides an iterator for lists that is accessible via `List.iterM`.
-/

namespace Std

namespace Iterators.Types

/--
The underlying state of a list iterator. Its contents are internal and should
not be used by downstream users of the library.
-/
@[ext]
structure ListIterator (α : Type w) where
  list : List α

end Iterators.Types

open Std.Iterators Std.Iterators.Types

variable {α : Type w} {m : Type w → Type w'}

/--
Returns a finite iterator for the given list.
The iterator yields the elements of the list in order and then terminates.

The non-monadic version of this iterator is `List.iter`.

**Termination properties:**

* `Finite` instance: always
* `Productive` instance: always
-/
@[always_inline, inline]
def _root_.List.iterM {α : Type w} (l : List α) (m : Type w → Type w') [Pure m] :
    IterM (α := ListIterator α) m α :=
  .mk { list := l } m α

namespace Iterators.Types

@[always_inline, inline]
instance ListIterator.instIterator {α : Type w} [Pure m] : Iterator (ListIterator α) m α where
  IsPlausibleStep it
    | .yield it' out => it.internalState.list = out :: it'.internalState.list
    | .skip _ => False
    | .done => it.internalState.list = []
  step it := pure (match it with
        | ⟨⟨[]⟩⟩ => .deflate ⟨.done, rfl⟩
        | ⟨⟨x :: xs⟩⟩ => .deflate ⟨.yield (.mk ⟨xs⟩ m α) x, rfl⟩)

private def ListIterator.instFinitenessRelation [Pure m] :
    FinitenessRelation (ListIterator α) m where
  Rel := InvImage WellFoundedRelation.rel (ListIterator.list ∘ IterM.internalState)
  wf := InvImage.wf _ WellFoundedRelation.wf
  subrelation {it it'} h := by
    simp_wf
    obtain ⟨step, h, h'⟩ := h
    cases step <;> simp_all [IterStep.successor, IterM.IsPlausibleStep, Iterator.IsPlausibleStep]

instance ListIterator.instFinite [Pure m] : Finite (ListIterator α) m :=
  by exact Finite.of_finitenessRelation ListIterator.instFinitenessRelation

@[always_inline, inline]
instance ListIterator.instIteratorLoop {α : Type w} [Monad m] {n : Type x → Type x'} [Monad n] :
    IteratorLoop (ListIterator α) m n :=
  .defaultImplementation

end Std.Iterators.Types
