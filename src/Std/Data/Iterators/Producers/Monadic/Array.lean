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
# Array iterator

This module provides an iterator for arrays that is accessible via `Array.iterM`.
-/

namespace Std.Iterators.Types

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
  .mk { array := array, pos := pos } m α

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
instance ArrayIterator.instIterator {α : Type w} [Pure m] : Iterator (ArrayIterator α) m α where
  IsPlausibleStep it
    | .yield it' out => it.internalState.array = it'.internalState.array ∧
      it'.internalState.pos = it.internalState.pos + 1 ∧
      ∃ _ : it.internalState.pos < it.internalState.array.size,
      it.internalState.array[it.internalState.pos] = out
    | .skip _ => False
    | .done => it.internalState.pos ≥ it.internalState.array.size
  step it := pure <| .deflate <| if h : it.internalState.pos < it.internalState.array.size then
        .yield
          ⟨⟨it.internalState.array, it.internalState.pos + 1⟩⟩
          it.internalState.array[it.internalState.pos]
          ⟨rfl, rfl, h, rfl⟩
      else
        .done (Nat.not_lt.mp h)

private def ArrayIterator.instFinitenessRelation [Pure m] :
    FinitenessRelation (ArrayIterator α) m where
  Rel := InvImage WellFoundedRelation.rel
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

instance ArrayIterator.instFinite [Pure m] : Finite (ArrayIterator α) m := by
  exact Finite.of_finitenessRelation ArrayIterator.instFinitenessRelation

@[always_inline, inline]
instance ArrayIterator.instIteratorLoop {α : Type w} [Monad m] {n : Type x → Type x'} [Monad n] :
    IteratorLoop (ArrayIterator α) m n :=
  .defaultImplementation

end Std.Iterators.Types
