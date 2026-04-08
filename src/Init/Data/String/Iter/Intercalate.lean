/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julia Markus Himmel
-/
module

prelude
public import Init.Data.Iterators.Combinators.Monadic.FilterMap
public import Init.Data.String.Basic
import Init.Data.String.Slice

set_option doc.verso true

namespace Std

/--
Appends all the elements in the iterator, in order.
-/
@[inline]
public def Iter.joinString {α β : Type} [Iterator α Id β] [ToString β]
    (it : Std.Iter (α := α) β) : String :=
  (it.map toString).fold (init := "") (· ++ ·)

/--
Appends the elements of the iterator into a string, placing the separator {name}`s` between them.
-/
@[inline]
public def Iter.intercalateString {α β : Type} [Iterator α Id β] [ToString β]
    (s : String.Slice) (it : Std.Iter (α := α) β) : String :=
  it.map toString
    |>.fold (init := none) (fun
      | none, sl => some sl
      | some str, sl => some (str ++ s ++ sl))
    |>.getD ""

end Std
