/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
module

prelude
public import Init.Data.String.Defs
public import Init.Data.Int.Repr

public section

/--
Converts a list into a string, using `ToString.toString` to convert its elements.

The resulting string resembles list literal syntax, with the elements separated by `", "` and
enclosed in square brackets.

The resulting string may not be valid Lean syntax, because there's no such expectation for
`ToString` instances.

Examples:
* `[1, 2, 3].toString = "[1, 2, 3]"`
* `["cat", "dog"].toString = "[cat, dog]"`
* `["cat", "dog", ""].toString = "[cat, dog, ]"`
-/
protected def List.toString [ToString α] : List α → String
  | [] => "[]"
  | [x] => "[" ++ toString x ++ "]"
  | x::xs => String.push (xs.foldl (fun l r => l ++ ", " ++ toString r) ("[" ++ (toString x))) ']'

instance {α : Type u} [ToString α] : ToString (List α) :=
  ⟨List.toString⟩

instance [ToString α] : ToString (Array α) where
  toString xs := "#" ++ (toString xs.toList)

instance : ToString ByteArray := ⟨fun bs => bs.toList.toString⟩

instance : ToString Int where
  toString := Int.repr
