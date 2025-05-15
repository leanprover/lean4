/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Init.Data.Nat.Lemmas
import Init.RCases
import Std.Data.Iterators.Consumers
import Std.Data.Iterators.Workbench.Termination

namespace Std.Iterators

variable {α : Type w} {m : Type w → Type w'}

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
  plausible_step it
    | .yield it' out => it.inner.list = out :: it'.inner.list
    | .skip _ => False
    | .done => it.inner.list = []
  step it := pure (match it with
        | ⟨⟨[]⟩⟩ => ⟨.done, rfl⟩
        | ⟨⟨x :: xs⟩⟩ => ⟨.yield (toIterM ⟨xs⟩ m α) x, rfl⟩)

instance [Pure m] : FinitenessRelation (ListIterator α) m where
  rel := InvImage WellFoundedRelation.rel (ListIterator.list ∘ IterM.inner)
  wf := InvImage.wf _ WellFoundedRelation.wf
  subrelation {it it'} h := by
    simp_wf
    obtain ⟨step, h, h'⟩ := h
    cases step <;> simp_all [IterStep.successor, IterM.plausible_step, Iterator.plausible_step]

instance {α : Type w} [Monad m] : IteratorCollect (ListIterator α) m :=
  .defaultImplementation

instance {α : Type w} [Monad m] : IteratorCollectPartial (ListIterator α) m :=
  .defaultImplementation

instance {α : Type w} [Monad m] [Monad n] : IteratorLoop (ListIterator α) m n :=
  .defaultImplementation

instance {α : Type w} [Monad m] [Monad n] : IteratorLoopPartial (ListIterator α) m n :=
  .defaultImplementation

end Std.Iterators
