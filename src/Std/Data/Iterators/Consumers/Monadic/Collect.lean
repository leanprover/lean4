/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Std.Data.Iterators.Consumers.Monadic.Partial

namespace Std.Iterators

section ToArray

@[always_inline, inline]
def IterM.DefaultConsumers.toArrayMapped {α : Type w} {m : Type w → Type w'} [Monad m] {β : Type w}
    [Iterator α m β] [Finite α m] {γ : Type w} (f : β → m γ) (it : IterM (α := α) m β) : m (Array γ) :=
  go it #[]
where
  @[specialize]
  go [Monad m] [Finite α m] (it : IterM (α := α) m β) a := do
    match ← it.step with
    | .yield it' b _ => go it' (a.push (← f b))
    | .skip it' _ => go it' a
    | .done _ => return a
  termination_by it.finitelyManySteps

@[always_inline, inline]
partial def IterM.DefaultConsumers.toArrayMappedPartial {α : Type w} {m : Type w → Type w'} [Monad m] {β : Type w}
    [Iterator α m β] {γ : Type w} (f : β → m γ) (it : IterM (α := α) m β) : m (Array γ) :=
  go it #[]
where
  @[specialize]
  go [Monad m] (it : IterM (α := α) m β) a := do
    match ← it.step with
    | .yield it' b _ => go it' (a.push (← f b))
    | .skip it' _ => go it' a
    | .done _ => return a

class IteratorCollect (α : Type w) (m : Type w → Type w') {β : Type w} [Iterator α m β] where
  toArrayMapped : ∀ {γ : Type w}, (β → m γ) → IterM (α := α) m β → m (Array γ)

class IteratorCollectPartial
  (α : Type w) (m : Type w → Type w') {β : Type w} [Iterator α m β] where
    toArrayMappedPartial : ∀ {γ : Type w}, (β → m γ) → IterM (α := α) m β → m (Array γ)

class LawfulIteratorCollect (α : Type w) (m : Type w → Type w') [Monad m] [Iterator α m β] [IteratorCollect α m] where
  finite : Finite α m
  lawful : ∀ γ, IteratorCollect.toArrayMapped (α := α) (m := m) (β := β) (γ := γ) =
    IterM.DefaultConsumers.toArrayMapped (α := α) (m := m) (γ := γ)

instance (α : Type w) (m : Type w → Type w') [Monad m] [Iterator α m β] [IteratorCollect α m]
    [LawfulIteratorCollect α m] : Finite α m :=
  LawfulIteratorCollect.finite

def IteratorCollect.defaultImplementation {α : Type w} {m : Type w → Type w'}
    [Monad m] [Iterator α m β] [Finite α m] : IteratorCollect α m where
  toArrayMapped := IterM.DefaultConsumers.toArrayMapped

def IteratorCollectPartial.defaultImplementation {α : Type w} {m : Type w → Type w'}
    [Monad m] [Iterator α m β] : IteratorCollectPartial α m where
  toArrayMappedPartial := IterM.DefaultConsumers.toArrayMappedPartial

instance (α : Type w) (m : Type w → Type w') [Monad m] [Iterator α m β]
    [Monad m] [Iterator α m β] [Finite α m] :
    haveI : IteratorCollect α m := .defaultImplementation
    LawfulIteratorCollect α m :=
  letI : IteratorCollect α m := .defaultImplementation
  ⟨inferInstance, fun _ => rfl⟩

@[always_inline, inline]
def IterM.toArray {α : Type w} {m : Type w → Type w'} {β : Type w} [Monad m]
    [Iterator α m β] (it : IterM (α := α) m β) [IteratorCollect α m] : m (Array β) :=
  IteratorCollect.toArrayMapped pure it

@[always_inline, inline]
def IterM.Partial.toArray {α : Type w} {m : Type w → Type w'} {β : Type w} [Monad m]
    [Iterator α m β] (it : IterM.Partial (α := α) m β) [IteratorCollectPartial α m] : m (Array β) :=
  IteratorCollectPartial.toArrayMappedPartial pure it.it

end ToArray

@[inline]
def IterM.toListRev {α : Type w} {m : Type w → Type w'} [Monad m] {β : Type w}
    [Iterator α m β] [Finite α m] (it : IterM (α := α) m β) : m (List β) :=
  go it []
where
  @[specialize]
  go [Finite α m] it bs := do
    match ← it.step with
    | .yield it' b _ => go it' (b :: bs)
    | .skip it' _ => go it' bs
    | .done _ => return bs
  termination_by it.finitelyManySteps

@[always_inline, inline]
partial def IterM.Partial.toListRev {α : Type w} {m : Type w → Type w'} [Monad m] {β : Type w}
    [Iterator α m β] (it : IterM.Partial (α := α) m β) : m (List β) :=
  go it.it []
where
  @[specialize]
  go it bs := do
    match ← it.step with
    | .yield it' b _ => go it' (b :: bs)
    | .skip it' _ => go it' bs
    | .done _ => return bs

@[always_inline, inline]
def IterM.toList {α : Type w} {m : Type w → Type w'} [Monad m] {β : Type w}
    [Iterator α m β] (it : IterM (α := α) m β) [IteratorCollect α m] : m (List β) :=
  Array.toList <$> IterM.toArray it

@[always_inline, inline]
def IterM.Partial.toList {α : Type w} {m : Type w → Type w'} [Monad m] {β : Type w}
    [Iterator α m β] (it : IterM.Partial (α := α) m β) [IteratorCollectPartial α m] : m (List β) :=
  Array.toList <$> it.toArray

end Std.Iterators
