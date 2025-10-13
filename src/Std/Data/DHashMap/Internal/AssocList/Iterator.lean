/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
import Init.Data.Nat.Lemmas

public import Init.Data.Iterators.Consumers
import Init.Data.Iterators.Internal.Termination

public import Std.Data.DHashMap.Internal.AssocList.Basic

/-!
# Iterators on associative lists
-/

namespace Std.DHashMap.Internal.AssocList

open Std.Iterators

/-- Internal implementation detail of the hash map -/
@[ext, unbox]
public structure AssocListIterator (α : Type u) (β : α → Type v) where
  l : AssocList α β

public instance : Iterator (α := AssocListIterator α β) Id ((a : α) × β a) where
  IsPlausibleStep it
    | .yield it' out => it.internalState.l = .cons out.1 out.2 it'.internalState.l
    | .skip _ => False
    | .done => it.internalState.l = .nil
  step it := pure (match it with
        | ⟨⟨.nil⟩⟩ => ⟨.done, rfl⟩
        | ⟨⟨.cons k v l⟩⟩ => ⟨.yield (toIterM ⟨l⟩ Id _) ⟨k, v⟩, rfl⟩)

def AssocListIterator.finitenessRelation :
    FinitenessRelation (AssocListIterator α β) Id where
  rel := InvImage WellFoundedRelation.rel (AssocListIterator.l ∘ IterM.internalState)
  wf := InvImage.wf _ WellFoundedRelation.wf
  subrelation {it it'} h := by
    simp_wf
    obtain ⟨step, h, h'⟩ := h
    cases step <;> simp_all [IterStep.successor, IterM.IsPlausibleStep, Iterator.IsPlausibleStep]

public instance : Finite (AssocListIterator α β) Id :=
  by exact Finite.of_finitenessRelation AssocListIterator.finitenessRelation

public instance {α : Type u} {β : α → Type v} {m : Type (max u v) → Type w''} [Monad m] :
    IteratorCollect (AssocListIterator α β) Id m :=
  .defaultImplementation

public instance {α : Type u} {β : α → Type v} {m : Type (max u v) → Type w''} [Monad m] :
    IteratorCollectPartial (AssocListIterator α β) Id m :=
  .defaultImplementation

public instance {α : Type u} {β : α → Type v} {m : Type (max u v) → Type w''} [Monad m] :
    IteratorLoop (AssocListIterator α β) Id m :=
  .defaultImplementation

public instance {α : Type u} {β : α → Type v} {m : Type (max u v) → Type w''} [Monad m] :
    IteratorLoopPartial (AssocListIterator α β) Id m :=
  .defaultImplementation

public instance : IteratorSize (AssocListIterator α β) Id :=
  .defaultImplementation

public instance : IteratorSizePartial (AssocListIterator α β) Id :=
  .defaultImplementation

/--
Internal implementation detail of the hash map. Returns a finite iterator on an associative list.
-/
@[expose]
public def iter {α : Type u} {β : α → Type v} (l : AssocList α β) :
    Iter (α := AssocListIterator α β) ((a : α) × β a) :=
  ⟨⟨l⟩⟩

end Std.DHashMap.Internal.AssocList
