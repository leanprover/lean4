/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Std.Data.Iterators.Combinators.Monadic.FilterMap

namespace Std.Iterators

@[always_inline, inline]
def Iter.filterMapWithProof {α β γ : Type w} [Iterator α Id β] {m : Type w → Type w'}
    [Monad m] (f : β → PostconditionT m (Option γ)) (it : Iter (α := α) β) :=
  (letI : MonadLift Id m := ⟨pure⟩; it.toIterM.filterMapWithProof f : IterM m γ)

@[always_inline, inline]
def Iter.filterWithProof {α β : Type w} [Iterator α Id β] {m : Type w → Type w'}
    [Monad m] (f : β → PostconditionT m (ULift Bool)) (it : Iter (α := α) β) :=
  (letI : MonadLift Id m := ⟨pure⟩; it.toIterM.filterWithProof f : IterM m β)

@[always_inline, inline]
def Iter.mapWithProof {α β γ : Type w} [Iterator α Id β] {m : Type w → Type w'}
    [Monad m] (f : β → PostconditionT m γ) (it : Iter (α := α) β) :=
  (letI : MonadLift Id m := ⟨pure⟩; it.toIterM.mapWithProof f : IterM m γ)

@[always_inline, inline]
def Iter.filterMapM {α β γ : Type w} [Iterator α Id β] {m : Type w → Type w'}
    [Monad m] (f : β → m (Option γ)) (it : Iter (α := α) β) :=
  (letI : MonadLift Id m := ⟨pure⟩; it.toIterM.filterMapM f : IterM m γ)

@[always_inline, inline]
def Iter.filterM {α β : Type w} [Iterator α Id β] {m : Type w → Type w'}
    [Monad m] (f : β → m (ULift Bool)) (it : Iter (α := α) β) :=
  (letI : MonadLift Id m := ⟨pure⟩; it.toIterM.filterM f : IterM m β)

@[always_inline, inline]
def Iter.mapM {α β γ : Type w} [Iterator α Id β] {m : Type w → Type w'}
    [Monad m] (f : β → m γ) (it : Iter (α := α) β) :=
  (letI : MonadLift Id m := ⟨pure⟩; it.toIterM.mapM f : IterM m γ)

@[always_inline, inline]
def Iter.filterMap {α : Type w} {β : Type w} {γ : Type w} [Iterator α Id β]
    (f : β → Option γ) (it : Iter (α := α) β) :=
  ((it.toIterM.filterMap f).toIter : Iter γ)

@[always_inline, inline]
def Iter.filter {α : Type w} {β : Type w} [Iterator α Id β]
    (f : β → Bool) (it : Iter (α := α) β) :=
  ((it.toIterM.filter f).toIter : Iter β)

@[always_inline, inline]
def Iter.map {α : Type w} {β : Type w} {γ : Type w} [Iterator α Id β]
    (f : β → γ) (it : Iter (α := α) β) :=
  ((it.toIterM.map f).toIter : Iter γ)

end Std.Iterators
