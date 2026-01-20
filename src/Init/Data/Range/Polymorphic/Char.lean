/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Markus Himmel
-/
module

prelude
public import Init.Data.Char.Ordinal
public import Init.Data.Range.Polymorphic.Lemmas
import Init.Data.Range.Polymorphic.Map
import Init.Data.Range.Polymorphic.Fin

open Std Std.PRange Std.PRange.UpwardEnumerable

namespace Char

public instance : UpwardEnumerable Char where
  succ?
  succMany?

def map : Map Char (Fin Char.numCodePoints) where
  toFun := Char.ordinal
  injective := sorry
  succ?_toFun := sorry
  succMany?_toFun := sorry

end Char
