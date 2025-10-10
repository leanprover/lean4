/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Iterators.Basic
public import Init.Data.Iterators.Consumers.Collect
public import Init.Data.Iterators.Consumers.Loop
public import Init.Data.Iterators.Combinators.FilterMap
public import Init.Data.Iterators.Combinators.Monadic.FlatMap
public import Init.Data.Iterators.PostconditionMonad
public import Init.Data.Iterators.Internal.Termination
public import Init.Data.Option.Lemmas

public import Std.Data.Iterators.Producers.List

set_option doc.verso true

/-!
# {lit}`flatMap` combinator

This file provides the {lit}`flatMap` iterator and variants of it.

If `it` is any iterator, `it.flatMap f` maps each output of `it` to an iterator using `f`.
The `flatMap` first emits all outputs of the first iterator, then of the second, and so on.
In other words, `it` flattens the iterator of iterators obtained by mapping with `f`.
-/

namespace Std.Iterators

-- @[always_inline]
-- def IterM.flattenAfter {α α₂ β : Type w} {m : Type w → Type w'} [Monad m]
--     [Iterator α m (IterM (α := α₂) m β)] [Iterator α₂ m β]
--     (it₁ : IterM (α := α) m (IterM (α := α₂) m β)) (it₂ : Option (IterM (α := α₂) m β)) :=
--   (toIterM (α := Flatten α α₂ β m) ⟨it₁, it₂⟩ m β : IterM m β)

@[always_inline]
public def Iter.flatMapAfterM {α : Type w} {β : Type w} {α₂ : Type w}
    {γ : Type w} {m : Type w → Type w'} [Monad m] [Iterator α Id β] [Iterator α₂ m γ]
    (f : β → m (IterM (α := α₂) m γ)) (it₁ : Iter (α := α) β) (it₂ : Option (IterM (α := α₂) m γ)) :=
  ((it₁.mapM pure).flatMapAfterM f it₂ : IterM m γ)

@[always_inline, expose]
public def Iter.flatMapM {α : Type w} {β : Type w} {α₂ : Type w}
    {γ : Type w} {m : Type w → Type w'} [Monad m] [Iterator α Id β] [Iterator α₂ m γ]
    (f : β → m (IterM (α := α₂) m γ)) (it : Iter (α := α) β) :=
  (it.flatMapAfterM f none : IterM m γ)

@[always_inline]
public def Iter.flatMapAfter {α : Type w} {β : Type w} {α₂ : Type w}
    {γ : Type w} [Iterator α Id β] [Iterator α₂ Id γ]
    (f : β → Iter (α := α₂) γ) (it₁ : Iter (α := α) β) (it₂ : Option (Iter (α := α₂) γ)) :=
  ((it₁.toIterM.flatMapAfter (fun b => (f b).toIterM) (Iter.toIterM <$> it₂)).toIter : Iter γ)

@[always_inline, expose]
public def Iter.flatMap {α : Type w} {β : Type w} {α₂ : Type w}
    {γ : Type w} [Iterator α Id β] [Iterator α₂ Id γ]
    (f : β → Iter (α := α₂) γ) (it : Iter (α := α) β) :=
  (it.flatMapAfter f none : Iter γ)

end Std.Iterators
