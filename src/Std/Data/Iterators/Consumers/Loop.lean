/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Std.Data.Iterators.Basic
import Std.Data.Iterators.Consumers.Monadic.Loop
import Std.Data.Iterators.Consumers.Partial

namespace Std.Iterators

instance (α : Type w) (β : Type w) (n : Type w → Type w') [Monad n]
    [Iterator α Id β] [Finite α Id] [IteratorLoop α Id n] :
    ForIn n (Iter (α := α) β) β where
  forIn it init f :=
    IteratorLoop.finiteForIn (fun δ (c : Id δ) => pure c.run) |>.forIn it.toIterM init f

instance (α : Type w) (β : Type w) (n : Type w → Type w') [Monad n]
    [Iterator α Id β] [IteratorLoopPartial α Id n] :
    ForIn n (Iter.Partial (α := α) β) β where
  forIn it init f :=
    letI : MonadLift Id n := ⟨pure⟩
    ForIn.forIn it.it.toIterM.allowNontermination init f

@[always_inline, inline]
def Iter.foldM {n : Type w → Type w} [Monad n]
    {α : Type w} {β : Type w} {γ : Type w} [Iterator α Id β] [Finite α Id]
    [IteratorLoop α Id n] (f : γ → β → n γ)
    (init : γ) (it : Iter (α := α) β) : n γ :=
  ForIn.forIn it init (fun x acc => ForInStep.yield <$> f acc x)

@[always_inline, inline]
def Iter.Partial.foldM {n : Type w → Type w} [Monad n]
    {α : Type w} {β : Type w} {γ : Type w} [Iterator α Id β]
    [IteratorLoopPartial α Id n] (f : γ → β → n γ)
    (init : γ) (it : Iter.Partial (α := α) β) : n γ :=
  ForIn.forIn it init (fun x acc => ForInStep.yield <$> f acc x)

@[always_inline, inline]
def Iter.count {α : Type w} {β : Type w} [Iterator α Id β] [Finite α Id]
    (it : Iter (α := α) β) : Nat :=
  it.toIterM.count

@[always_inline, inline]
def Iter.Partial.count {α : Type w} {β : Type w} [Iterator α Id β]
    (it : Iter.Partial (α := α) β) : Nat :=
  it.it.toIterM.allowNontermination.count

end Std.Iterators
