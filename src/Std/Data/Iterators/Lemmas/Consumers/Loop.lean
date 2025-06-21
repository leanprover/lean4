/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Init.Data.List.Control
import Init.Data.Iterators.Lemmas.Basic
import Init.Data.Iterators.Lemmas.Consumers.Loop
import Std.Data.Iterators.Lemmas.Consumers.Collect
import Std.Data.Iterators.Lemmas.Consumers.Monadic.Loop
import Init.Data.Iterators.Consumers.Collect
import Init.Data.Iterators.Consumers.Loop

namespace Std.Iterators

theorem Iter.Equiv.forIn_eq {α₁ α₂ β γ : Type w} {m : Type w → Type w'}
    [Iterator α₁ Id β] [Iterator α₂ Id β] [Finite α₁ Id] [Finite α₂ Id]
    [Monad m] [LawfulMonad m] [IteratorLoop α₁ Id m] [LawfulIteratorLoop α₁ Id m]
    [IteratorLoop α₂ Id m] [LawfulIteratorLoop α₂ Id m] {init : γ} {f : β → γ → m (ForInStep γ)}
    {ita : Iter (α := α₁) β} {itb : Iter (α := α₂) β} (h : Iter.Equiv ita itb) :
    ForIn.forIn (m := m) ita init f = ForIn.forIn (m := m) itb init f := by
  letI : MonadLift Id m := ⟨Std.Internal.idToMonad (α := _)⟩
  letI := Std.Internal.LawfulMonadLiftFunction.idToMonad (m := m)
  simp [Iter.forIn_eq_forIn_toIterM, h.toIterM.forIn_eq]

theorem Iter.Equiv.foldM_eq {α₁ α₂ β γ : Type w} {m : Type w → Type w'}
    [Iterator α₁ Id β] [Iterator α₂ Id β][Iterator α₁ Id β] [Iterator α₂ Id β]
    [Finite α₁ Id] [Finite α₂ Id] [Monad m] [LawfulMonad m]
    [IteratorLoop α₁ Id m] [LawfulIteratorLoop α₁ Id m]
    [IteratorLoop α₂ Id m] [LawfulIteratorLoop α₂ Id m]
    {init : γ} {f : γ → β → m γ}
    {ita : Iter (α := α₁) β} {itb : Iter (α := α₂) β} (h : Iter.Equiv ita itb) :
    ita.foldM (init := init) f = itb.foldM (init := init) f := by
  simp [Iter.foldM_eq_forIn, h.forIn_eq]

theorem Iter.Equiv.fold_eq {α₁ α₂ β γ : Type w} {m : Type w → Type w'}
    [Iterator α₁ Id β] [Iterator α₂ Id β][Iterator α₁ Id β] [Iterator α₂ Id β]
    [Finite α₁ Id] [Finite α₂ Id] [Monad m] [LawfulMonad m]
    [IteratorLoop α₁ Id Id] [LawfulIteratorLoop α₁ Id Id]
    [IteratorLoop α₂ Id Id] [LawfulIteratorLoop α₂ Id Id]
    {init : γ} {f : γ → β → γ}
    {ita : Iter (α := α₁) β} {itb : Iter (α := α₂) β} (h : Iter.Equiv ita itb) :
    ita.fold (init := init) f = itb.fold (init := init) f := by
  simp [Iter.fold_eq_foldM, h.foldM_eq]

end Std.Iterators
