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
# Array iterator

This module provides an iterator for arrays that is accessible via `Array.iterM`.
-/

namespace Std.Iterators

variable {α : Type w} {m : Type w → Type w'}

/--
The underlying state of a list iterator. Its contents are internal and should
not be used by downstream users of the library.
-/
@[unbox, ext]
structure ArrayIterator (α : Type w) where
  /-- Internal implementation detail of the iterator library. -/
  array : Array α
  /-- Internal implementation detail of the iterator library. -/
  pos : Nat

theorem ArrayIterator.exists_iff {α : Type w} {P : ArrayIterator α → Prop} :
    (∃ s, P s) ↔ ∃ array pos, P ⟨array, pos⟩ := by
  constructor
  · rintro ⟨⟨array, pos⟩, h⟩
    exact ⟨array, pos, h⟩
  · rintro ⟨array, pos, h⟩
    exact ⟨⟨array, pos⟩, h⟩

/--
Returns a finite monadic iterator for the given array starting at the given index.
The iterator yields the elements of the array in order and then terminates.

The pure version of this iterator is `Array.iterFromIdx`.

**Termination properties:**

* `Finite` instance: always
* `Productive` instance: always
-/
@[always_inline, inline, match_pattern]
def _root_.Array.iterFromIdxM {α : Type w} (array : Array α) (m : Type w → Type w') (pos : Nat)
    [Pure m] :
    IterM (α := ArrayIterator α) m α :=
  toIterM { array := array, pos := pos } m α

/--
Returns a finite monadic iterator for the given array.
The iterator yields the elements of the array in order and then terminates. There are no side
effects.

The pure version of this iterator is `Array.iter`.

**Termination properties:**

* `Finite` instance: always
* `Productive` instance: always
-/
@[always_inline, inline]
def _root_.Array.iterM {α : Type w} (array : Array α) (m : Type w → Type w') [Pure m] :
    IterM (α := ArrayIterator α) m α :=
  array.iterFromIdxM m 0

@[always_inline, inline]
instance {α : Type w} [Pure m] : Iterator (ArrayIterator α) m α where
  IsPlausibleStep it
    | .yield it' out => it.internalState.array = it'.internalState.array ∧
      it'.internalState.pos = it.internalState.pos + 1 ∧
      ∃ _ : it.internalState.pos < it.internalState.array.size,
      it.internalState.array[it.internalState.pos] = out
    | .skip _ => False
    | .done => it.internalState.pos ≥ it.internalState.array.size
  step it := pure <| if h : it.internalState.pos < it.internalState.array.size then
        .yield
          ⟨⟨it.internalState.array, it.internalState.pos + 1⟩⟩
          it.internalState.array[it.internalState.pos]
          ⟨rfl, rfl, h, rfl⟩
      else
        .done (Nat.not_lt.mp h)

private def ArrayIterator.finitenessRelation [Pure m] :
    FinitenessRelation (ArrayIterator α) m where
  rel := InvImage WellFoundedRelation.rel
      (fun it => it.internalState.array.size - it.internalState.pos)
  wf := InvImage.wf _ WellFoundedRelation.wf
  subrelation {it it'} h := by
    simp_wf
    obtain ⟨step, h, h'⟩ := h
    cases step
    · cases h
      obtain ⟨h, h', h'', rfl⟩ := h'
      rw [h] at h''
      rw [h, h']
      omega
    · cases h'
    · cases h

instance [Pure m] : Finite (ArrayIterator α) m :=
  Finite.of_finitenessRelation ArrayIterator.finitenessRelation

@[always_inline, inline]
instance {α : Type w} [Monad m] [Monad n] : IteratorCollect (ArrayIterator α) m n :=
  .defaultImplementation

@[always_inline, inline]
instance {α : Type w} [Monad m] [Monad n] : IteratorCollectPartial (ArrayIterator α) m n :=
  .defaultImplementation

@[always_inline, inline]
instance {α : Type w} [Monad m] [Monad n] : IteratorLoop (ArrayIterator α) m n :=
  .defaultImplementation

@[always_inline, inline]
instance {α : Type w} [Monad m] [Monad n] : IteratorLoopPartial (ArrayIterator α) m n :=
  .defaultImplementation

end Std.Iterators
