/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Iterators.Consumers.Loop

public section

/-!
This module provides the typeclass `ToIterator`, which is implemented by types that can be
converted into iterators.
-/

namespace Std

/-- This typeclass provides an iterator for elements of type `γ`. -/
class ToIterator (γ : Type u) (m : Type w → Type w') (α β : outParam (Type w)) where
  iterMInternal (x : γ) : IterM (α := α) m β

/-- Converts `x` into a monadic iterator. -/
@[always_inline, inline, expose]
def ToIterator.iterM (x : γ) [ToIterator γ m α β] : IterM (α := α) m β :=
  ToIterator.iterMInternal (x := x)

/-- Converts `x` into a pure iterator. -/
@[always_inline, inline, expose]
def ToIterator.iter [ToIterator γ Id α β] (x : γ) : Iter (α := α) β :=
  ToIterator.iterM x |>.toIter

/-- Creates a monadic `ToIterator` instance. -/
@[always_inline, inline, expose]
def ToIterator.ofM (α : Type w)
    (iterM : γ → IterM (α := α) m β) :
    ToIterator γ m α β where
  iterMInternal x := iterM x

/-- Creates a pure `ToIterator` instance. -/
@[always_inline, inline, expose]
def ToIterator.of (α : Type w)
    (iter : γ → Iter (α := α) β) :
    ToIterator γ Id α β where
  iterMInternal x := iter x |>.toIterM

/-- Replaces `ToIterator.iterM` with its definition. -/
theorem ToIterator.iterM_eq {γ : Type u} {α β : Type v}
    {it : γ → IterM (α := α) Id β} {x} :
    letI : ToIterator γ Id α β := .ofM α it
    ToIterator.iterM x = it x :=
  rfl

/-- Replaces `ToIterator.iter` with its definition. -/
theorem ToIterator.iter_eq {γ : Type u} {x : γ} {α β : Type v} {it} :
    letI : ToIterator γ Id α β := .ofM α it
    ToIterator.iter x = (it x).toIter :=
  rfl

end Std
