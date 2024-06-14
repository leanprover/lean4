/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/
prelude
import Init.Data.List.Basic
import Init.Data.Char.Basic
import Init.Data.Option.Basic

namespace StringBis

/--
`String` is the type of (UTF-8 encoded) strings.

The compiler overrides the data representation of this type to a byte sequence,
and both `String.utf8ByteSize` and `String.length` are cached and O(1).
-/
structure String where
  /-- Pack a `List Char` into a `String`. This function is overridden by the
  compiler and is O(n) in the length of the list. -/
  mk ::
  /-- Unpack `String` into a `List Char`. This function is overridden by the
  compiler and is O(n) in the length of the list. -/
  data : List Char

attribute [extern "lean_string_mk"] String.mk
attribute [extern "lean_string_data"] String.data

end StringBis
