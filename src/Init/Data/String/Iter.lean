/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

prelude
public import Init.Data.Iterators.Combinators.FilterMap

set_option doc.verso true

namespace Std

/--
Convenience function for turning an iterator into a list of strings, provided the output of the
iterator implements {name}`ToString`.
-/
@[inline]
public abbrev Iter.toStringList {α β : Type} [Iterator α Id β] [ToString β]
    (it : Iter (α := α) β) : List String :=
  it.map toString |>.toList

/--
Convenience function for turning an iterator into an array of strings, provided the output of the
iterator implements {name}`ToString`.
-/
@[inline]
public abbrev Iter.toStringArray {α β : Type} [Iterator α Id β] [ToString β]
    (it : Iter (α := α) β) : Array String :=
  it.map toString |>.toArray

end Std
