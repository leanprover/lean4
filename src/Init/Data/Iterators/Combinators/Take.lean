/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Iterators.Combinators.Monadic.Take

@[expose] public section

namespace Std.Iterators

/--
Given an iterator `it` and a natural number `n`, `it.take n` is an iterator that outputs
up to the first `n` of `it`'s values in order and then terminates.

**Marble diagram:**

```text
it          ---a----b---c--d-e--⊥
it.take 3   ---a----b---c⊥

it          ---a--⊥
it.take 3   ---a--⊥
```

**Termination properties:**

* `Finite` instance: only if `it` is productive
* `Productive` instance: only if `it` is productive

**Performance:**

This combinator incurs an additional O(1) cost with each output of `it`.
-/
@[always_inline, inline]
def Iter.take {α : Type w} {β : Type w} (n : Nat) (it : Iter (α := α) β) :
    Iter (α := Take α Id β) β :=
  it.toIterM.take n |>.toIter

end Std.Iterators
