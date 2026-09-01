/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Iterators.Combinators.Monadic.Append

public section

namespace Std
open Std.Iterators Std.Iterators.Types

/--
Given two iterators `it₁` and `it₂`, `it₁.append it₂` is an iterator that first outputs all values
of `it₁` in order and then all values of `it₂` in order.

**Marble diagram:**

```text
it₁                 ---a----b---c--⊥
it₂                                 --d--e--⊥
it₁.append it₂      ---a----b---c-----d--e--⊥
```

**Termination properties:**

* `Finite` instance: only if `it₁` and `it₂` are finite
* `Productive` instance: only if `it₁` and `it₂` are productive

Note: If `it₁` is not finite, then `it₁.append it₂` can be productive while `it₂` is not.
The standard library does not provide a `Productive` instance for this case.

**Performance:**

This combinator incurs an additional O(1) cost with each output of `it₁` and `it₂`.
-/
@[cbv_opaque, inline, expose]
def Iter.append {α₁ : Type w} {α₂ : Type w} {β : Type w}
    [Iterator α₁ Id β] [Iterator α₂ Id β]
    (it₁ : Iter (α := α₁) β) (it₂ : Iter (α := α₂) β) :
    Iter (α := Append α₁ α₂ Id β) β :=
  (it₁.toIterM.append it₂.toIterM).toIter

/--
This combinator is only useful for advanced use cases.

Given an iterator `it₂`, returns an iterator that behaves exactly like `it₂` but is of the same
type as `it₁.append it₂` (after `it₁` has been exhausted).
This is useful for constructing intermediate states of the append iterator.

**Marble diagram:**

```text
it₂                        --a--b--⊥
Iter.appendSnd α₁ it₂      --a--b--⊥
```

**Termination properties:**

* `Finite` instance: only if `it₂` and iterators of type `α₁` are finite
* `Productive` instance: only if `it₂` and iterators of type `α₁` are productive

Note: If iterators of type `α₁` are not finite, then `append α₁ it₂` can be productive while `it₂` is not.
The standard library does not provide a `Productive` instance for this case.

**Performance:**

This combinator incurs an additional O(1) cost with each output of `it₂`.
-/
@[inline, expose]
def Iter.Intermediate.appendSnd {α₂ : Type w} {β : Type w}
    [Iterator α₂ Id β] (α₁ : Type w) (it₂ : Iter (α := α₂) β) :
    Iter (α := Append α₁ α₂ Id β) β :=
  (IterM.Intermediate.appendSnd α₁ it₂.toIterM).toIter

end Std
