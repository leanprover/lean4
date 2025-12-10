/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Iterators.Consumers
public import Init.Data.Iterators.Internal.Termination
import Init.Control.Lawful.MonadAttach.Lemmas

@[expose] public section

/-!
# List iterator

This module provides an iterator for lists that is accessible via `List.iterM`.
-/

namespace Std.Iterators

variable {α : Type w} {m : Type w → Type w'}

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

The non-monadic version of this iterator is `List.iter`.

**Termination properties:**

* `Finite` instance: always
* `Productive` instance: always
-/
@[always_inline, inline]
def _root_.List.iterM {α : Type w} (l : List α) (m : Type w → Type w') [Pure m] :
    IterM (α := ListIterator α) m α :=
  toIterM { list := l } m α

@[always_inline, inline]
instance {α : Type w} [Pure m] : Iterator (ListIterator α) m α where
  step it := pure (match it with
        | ⟨⟨[]⟩⟩ => .done
        | ⟨⟨x :: xs⟩⟩ => .yield (toIterM ⟨xs⟩ m α) x)

private def ListIterator.instFinitenessRelation
    [Monad m] [MonadAttach m] [LawfulMonad m] [LawfulMonadAttach m] :
    FinitenessRelation (ListIterator α) m where
  rel := InvImage WellFoundedRelation.rel (ListIterator.list ∘ IterM.internalState)
  wf := InvImage.wf _ WellFoundedRelation.wf
  subrelation {it it'} h := by
    simp_wf
    obtain ⟨step, hs, h⟩ := h
    cases LawfulMonadAttach.eq_of_canReturn_pure h
    split at hs
    · nomatch hs
    · cases hs
      simp

instance ListIterator.instFinite
    [Monad m] [MonadAttach m] [LawfulMonad m] [LawfulMonadAttach m] :
    Finite (ListIterator α) m :=
  by exact Finite.of_finitenessRelation ListIterator.instFinitenessRelation

@[always_inline, inline]
instance {α : Type w} [Monad m] [MonadAttach m] {n : Type w → Type w''} [Monad n] :
    IteratorCollect (ListIterator α) m n :=
  .defaultImplementation

@[always_inline, inline]
instance {α : Type w} [Monad m] [MonadAttach m] {n : Type x → Type x'} [Monad n] [MonadAttach n] :
    IteratorLoop (ListIterator α) m n :=
  .defaultImplementation

end Std.Iterators
