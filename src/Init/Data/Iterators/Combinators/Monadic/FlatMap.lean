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
public import Init.Data.Iterators.PostconditionMonad
public import Init.Data.Iterators.Internal.Termination

public section

set_option doc.verso true

/-!
# Monadic {lit}`flatMap` combinator

This file provides the {lit}`flatMap` iterator and variants of it.

If `it` is any iterator, `it.flatMap f` maps each output of `it` to an iterator using `f`.
The `flatMap` first emits all outputs of the first iterator, then of the second, and so on.
In other words, `it` flattens the iterator of iterators obtained by mapping with `f`.

Several variants of `flatMap` are provided:

* `M` suffix: monadic mapping function that can have side effects
* `D` suffix: dependently typed mapping function
-/

namespace Std.Iterators

@[unbox]
structure FlatMap (α : Type w) [Iterator α m β]
    (f : (it : IterM (α := α) m β) → (out : β) → it.IsPlausibleOutput out → IterM (α := α₂) m γ) where
  it₁ : IterM (α := α) m β
  it₂ : Option (IterM (α := α₂) m γ)



end Std.Iterators
