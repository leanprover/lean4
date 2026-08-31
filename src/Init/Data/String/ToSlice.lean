/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

prelude
public import Init.Data.String.Defs

/-!
# The `ToSlice` typeclass
-/

public section

namespace String

/--
Typeclass for types that have a conversion function to `String.Slice`. This typeclass is used to
make some `String`/`String.Slice` functions polymorphic. As such, for now it is not intended that
there instances of this beyond `ToSlice String` and `ToSlice String.Slice`.

To convert arbitrary data into a string representation, see `ToString` and `Repr`.
-/
class ToSlice (α : Type u) where
  toSlice : α → String.Slice

@[inline]
instance : ToSlice String.Slice where
  toSlice := id

@[inline]
instance : ToSlice String where
  toSlice := toSlice

end String
