/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Iterators.Combinators.FilterMap
public import Init.Data.Iterators.Combinators.Monadic.FlatMap

set_option doc.verso true

/-!
# {lit}`flatMap` combinator

This file provides the {lit}`flatMap` iterator combinator and variants of it.

If {lit}`it` is any iterator, {lit}`it.flatMap f` maps each output of {lit}`it` to an iterator using
{lit}`f`.

{lit}`it.flatMap f` first emits all outputs of the first obtained iterator, then of the second,
and so on. In other words, {lit}`it` flattens the iterator of iterators obtained by mapping with
{lit}`f`.
-/

namespace Std

@[always_inline, inherit_doc IterM.flatMapAfterM]
public def Iter.flatMapAfterM {α : Type w} {β : Type w} {α₂ : Type w}
    {γ : Type w} {m : Type w → Type w'} [Monad m] [MonadAttach m] [Iterator α Id β] [Iterator α₂ m γ]
    (f : β → m (IterM (α := α₂) m γ)) (it₁ : Iter (α := α) β) (it₂ : Option (IterM (α := α₂) m γ)) :=
  ((it₁.mapWithPostcondition pure).flatMapAfterM f it₂ : IterM m γ)

@[always_inline, expose, inherit_doc IterM.flatMapM]
public def Iter.flatMapM {α : Type w} {β : Type w} {α₂ : Type w}
    {γ : Type w} {m : Type w → Type w'} [Monad m] [MonadAttach m] [Iterator α Id β] [Iterator α₂ m γ]
    (f : β → m (IterM (α := α₂) m γ)) (it : Iter (α := α) β) :=
  (it.flatMapAfterM f none : IterM m γ)

@[always_inline, inherit_doc IterM.flatMapAfter]
public def Iter.flatMapAfter {α : Type w} {β : Type w} {α₂ : Type w}
    {γ : Type w} [Iterator α Id β] [Iterator α₂ Id γ]
    (f : β → Iter (α := α₂) γ) (it₁ : Iter (α := α) β) (it₂ : Option (Iter (α := α₂) γ)) :=
  ((it₁.toIterM.flatMapAfter (fun b => (f b).toIterM) (Iter.toIterM <$> it₂)).toIter : Iter γ)

@[always_inline, expose, inherit_doc IterM.flatMap]
public def Iter.flatMap {α : Type w} {β : Type w} {α₂ : Type w}
    {γ : Type w} [Iterator α Id β] [Iterator α₂ Id γ]
    (f : β → Iter (α := α₂) γ) (it : Iter (α := α) β) :=
  (it.flatMapAfter f none : Iter γ)
