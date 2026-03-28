/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Std.Data.HashMap.Iterator
public import Std.Data.HashSet.Basic
public import Std.Data.HashSet.Raw
import Init.Data.Iterators.Combinators.FilterMap

/-!
# Iterators on `HashSet` and `HashSet.Raw`
-/

namespace Std.HashSet.Raw

/--
Returns a finite iterator over the elements of a hash set.
The iterator yields the elements of the set in order and then terminates.

**Termination properties:**

* `Finite` instance: always
* `Productive` instance: always
-/
@[inline]
public def iter {α : Type u} (m : Raw α) :=
  (m.inner.inner.iter.map fun e => e.1 : Iter α)

end Std.HashSet.Raw

namespace Std.HashSet

@[inline, inherit_doc Raw.iter]
public def iter {α : Type u} [BEq α] [Hashable α] (m : HashSet α) :=
  (m.inner.inner.iter.map fun e => e.1 : Iter α)

end Std.HashSet
