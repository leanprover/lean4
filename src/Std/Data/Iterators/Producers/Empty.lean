/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Std.Data.Iterators.Producers.Monadic.Empty

@[expose] public section

namespace Std

/--
Returns an iterator that terminates immediately.

**Termination properties:**

* `Finite` instance: always
* `Productive` instance: always
-/
@[always_inline, inline]
def Iter.empty (β : Type w) :=
  ((IterM.empty Id β).toIter : Iter β)

end Std
