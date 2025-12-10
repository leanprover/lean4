/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
import Init.Data.Nat.Lemmas
import Init.Control.Lawful.MonadAttach.Lemmas

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
  step it := pure (match it with
        | ⟨⟨.nil⟩⟩ => .done
        | ⟨⟨.cons k v l⟩⟩ => .yield (toIterM ⟨l⟩ Id _) ⟨k, v⟩)

def AssocListIterator.finitenessRelation :
    FinitenessRelation (AssocListIterator α β) Id where
  rel := InvImage WellFoundedRelation.rel (AssocListIterator.l ∘ IterM.internalState)
  wf := InvImage.wf _ WellFoundedRelation.wf
  subrelation {it it'} h := by
    simp_wf
    obtain ⟨step, hs, h⟩ := h
    cases LawfulMonadAttach.eq_of_canReturn_pure h
    split at hs
    · nomatch hs
    · cases hs
      simp

public instance : Finite (AssocListIterator α β) Id :=
  Finite.of_finitenessRelation AssocListIterator.finitenessRelation

public instance {α : Type u} {β : α → Type v} {m : Type (max u v) → Type w''} [Monad m] :
    IteratorCollect (AssocListIterator α β) Id m :=
  .defaultImplementation

public instance {α : Type u} {β : α → Type v} {m : Type (max u v) → Type w''}
    [Monad m] [MonadAttach m] : IteratorLoop (AssocListIterator α β) Id m :=
  .defaultImplementation

/--
Internal implementation detail of the hash map. Returns a finite iterator on an associative list.
-/
@[expose]
public def iter {α : Type u} {β : α → Type v} (l : AssocList α β) :
    Iter (α := AssocListIterator α β) ((a : α) × β a) :=
  ⟨⟨l⟩⟩

end Std.DHashMap.Internal.AssocList
