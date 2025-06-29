/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Iterators.Consumers

public section

/-!
This module provides the typeclass `ToIterator`, which is implemented by types that can be
converted into iterators.
-/

open Std.Iterators

namespace Std.Iterators

/--
This typeclass provides an iterator for the given element `x : γ`. Usually, instances are provided
for all elements of a type `γ`.
-/
class ToIterator {γ : Type u} (x : γ) (m : Type w → Type w') (β : outParam (Type w)) where
  State : Type w
  iterMInternal : IterM (α := State) m β

/-- Converts `x` into a monadic iterator. -/
@[always_inline, inline, expose]
def ToIterator.iterM (x : γ) [ToIterator x m β] : IterM (α := ToIterator.State x m) m β :=
  ToIterator.iterMInternal (x := x)

/-- Converts `x` into a pure iterator. -/
@[always_inline, inline, expose]
def ToIterator.iter (x : γ) [ToIterator x Id β] : Iter (α := ToIterator.State x Id) β :=
  ToIterator.iterM x |>.toIter

/-- Creates a monadic `ToIterator` instance. -/
@[always_inline, inline, expose]
def ToIterator.ofM {x : γ} (State : Type w)
    (iterM : IterM (α := State) m β) :
    ToIterator x m β where
  State := State
  iterMInternal := iterM

/-- Creates a pure `ToIterator` instance. -/
@[always_inline, inline, expose]
def ToIterator.of {x : γ} (State : Type w)
    (iter : Iter (α := State) β) :
    ToIterator x Id β where
  State := State
  iterMInternal := iter.toIterM

theorem ToIterator.iterM_eq {γ : Type u} {x : γ} {State : Type v} {β : Type v} {it} :
    letI : ToIterator x Id β := .ofM State it
    ToIterator.iterM x = it :=
  rfl

theorem ToIterator.iter_eq {γ : Type u} {x : γ} {State : Type v} {β : Type v} {it} :
    letI : ToIterator x Id β := .ofM State it
    ToIterator.iter x = it.toIter :=
  rfl

/-!
## Instance forwarding

If the type defined as `ToIterator.State` implements an iterator typeclass, then this typeclass
should also be available when the type is syntactically visible as `ToIteratorState`. The following
instances are responsible for this forwarding.
-/

instance {x : γ} {State : Type w} {iter}
    [Iterator State m β] :
    letI i : ToIterator x m β := .ofM State iter
    Iterator (α := i.State) m β :=
  inferInstanceAs <| Iterator State m β

instance {x : γ} {State : Type w} {iter}
    [Iterator (α := State) m β] [Finite State m] :
    letI i : ToIterator x m β := .ofM State iter
    Finite (α := i.State) m :=
  inferInstanceAs <| Finite (α := State) m

instance {x : γ} {State : Type w} {iter}
    [Iterator (α := State) m β] [IteratorCollect State m n] :
    letI i : ToIterator x m β := .ofM State iter
    IteratorCollect (α := i.State) m n :=
  inferInstanceAs <| IteratorCollect (α := State) m n

instance {x : γ} {State : Type w} {iter}
    [Iterator (α := State) m β] [IteratorCollectPartial State m n] :
    letI i : ToIterator x m β := .ofM State iter
    IteratorCollectPartial (α := i.State) m n :=
  inferInstanceAs <| IteratorCollectPartial (α := State) m n

instance {x : γ} {State : Type w} {iter}
    [Iterator (α := State) m β] [IteratorLoop State m n] :
    letI i : ToIterator x m β := .ofM State iter
    IteratorLoop (α := i.State) m n :=
  inferInstanceAs <| IteratorLoop (α := State) m n

instance {x : γ} {State : Type w} {iter}
    [Iterator (α := State) m β] [IteratorLoopPartial State m n] :
    letI i : ToIterator x m β := .ofM State iter
    IteratorLoopPartial (α := i.State) m n :=
  inferInstanceAs <| IteratorLoopPartial (α := State) m n

instance {x : γ} {State : Type w} {iter}
    [Iterator (α := State) m β] [IteratorSize State m] :
    letI i : ToIterator x m β := .ofM State iter
    IteratorSize (α := i.State) m :=
  inferInstanceAs <| IteratorSize (α := State) m

instance {x : γ} {State : Type w} {iter}
    [Iterator (α := State) m β] [IteratorSizePartial State m] :
    letI i : ToIterator x m β := .ofM State iter
    IteratorSizePartial (α := i.State) m :=
  inferInstanceAs <| IteratorSizePartial (α := State) m

end Std.Iterators
