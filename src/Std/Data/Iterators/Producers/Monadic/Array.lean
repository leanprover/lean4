/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Iterators.Consumers
import Init.Omega
meta import Init.ByCases

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
  ⟨{ array := array, pos := pos }⟩

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

instance : IteratorAccess (ArrayIterator α) Id where
  nextAtIdx? it n :=
    let step : IterStep (IterM (α := ArrayIterator α) Id α) α :=
      if h : it.internalState.pos + n < it.internalState.array.size then
        .yield
          ⟨⟨it.internalState.array, it.internalState.pos + n + 1⟩⟩
          it.internalState.array[it.internalState.pos + n]
      else
        .done
    haveI : IterM.IsPlausibleNthOutputStep n it step := by
      simp only [step]
      induction n generalizing it
      · split
        · refine .zero_yield ?_
          simpa [IterM.IsPlausibleStep, Iterator.IsPlausibleStep, ArrayIterator.instIterator, *] -- TODO: remove `inst...` argument as soon as possible
        · refine .done ?_
          simp_all [IterM.IsPlausibleStep, Iterator.IsPlausibleStep, ArrayIterator.instIterator] -- TODO: remove `inst...` argument as soon as possible
      · rename_i n ih
        by_cases h : it.internalState.pos < it.internalState.array.size
        · refine .yield (it' := ?it') (out := ?_) ?_ ?_
          · exact ⟨⟨it.internalState.array, it.internalState.pos + 1⟩⟩
          · exact it.internalState.array[it.internalState.pos]
          · simpa [IterM.IsPlausibleStep, Iterator.IsPlausibleStep, ArrayIterator.instIterator] -- TODO: remove `inst...` argument as soon as possible
          · specialize ih ?it'
            simp only [Nat.add_comm 1, Nat.add_assoc] at ih ⊢
            split
            · rw [dif_pos (by omega)] at ih
              apply ih
            · rw [dif_neg (by omega)] at ih
              apply ih
        · rw [dif_neg (by omega)]
          refine .done (α := ArrayIterator α) (m := Id) ?_
          simpa [IterM.IsPlausibleStep, Iterator.IsPlausibleStep] using h
    pure ⟨step, this⟩

end Std.Iterators.Types
