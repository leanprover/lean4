/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Std.Data.Iterators.Combinators.Monadic.DropWhile

@[expose] public section

namespace Std

/--
Constructs intermediate states of an iterator created with the combinator `Iter.dropWhile`.
When `it.dropWhile P` has stopped dropping elements, its new state cannot be created
directly with `Iter.dropWhile` but only with `Intermediate.dropWhile`.

`Intermediate.dropWhile` is meant to be used only for internally or for verification purposes.
-/
@[always_inline, inline]
def Iter.Intermediate.dropWhile (P : β → Bool) (dropping : Bool)
    (it : Iter (α := α) β) :=
  ((IterM.Intermediate.dropWhile P dropping it.toIterM).toIter : Iter β)

/--
Given an iterator `it` and a predicate `P`, `it.dropWhile P` is an iterator that
emits the values emitted by `it` starting from the first value that is rejected by `P`.
The elements before are dropped.

In situations where `P` is monadic, use `dropWhileM` instead.

**Marble diagram:**

Assuming that the predicate `P` accepts `a` and `b` but rejects `c`:

```text
it               ---a----b---c--d-e--⊥
it.dropWhile P   ------------c--d-e--⊥

it               ---a----⊥
it.dropWhile P   --------⊥
```

**Termination properties:**

* `Finite` instance: only if `it` is finite
* `Productive` instance: only if `it` is finite

Depending on `P`, it is possible that `it.dropWhileM P` is productive although
`it` is not. In this case, the `Productive` instance needs to be proved manually.

**Performance:**

This combinator calls `P` on each output of `it` until the predicate evaluates to false. After
that, the combinator incurs an additional O(1) cost for each value emitted by `it`.
-/
@[always_inline, inline]
def Iter.dropWhile {α : Type w} {β : Type w} (P : β → Bool) (it : Iter (α := α) β) :=
  (it.toIterM.dropWhile P |>.toIter : Iter β)

end Std
