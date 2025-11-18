/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Iterators.Combinators.Monadic.Sigma
public import Init.Data.Iterators.Combinators.FilterMap

public section

namespace Std.Iterators

@[always_inline, inline, expose, inherit_doc IterM.sigma]
def Iter.sigma {γ : Type w} {α : γ → Type w}
    [∀ x : γ, Iterator (α x) Id β] {param : γ} (it : Iter (α := α param) β):
    Iter (α := Types.SigmaIterator γ α) β :=
  it.toIterM.sigma.toIter

end Std.Iterators
