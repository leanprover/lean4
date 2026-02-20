/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Internal.Async.ContextAsync
public import Std.Internal.Http.Data.Headers
public import Std.Internal.Http.Data.Body.Length

public section

/-!
# Body

This module defines shared types for HTTP body handling.
-/

namespace Std.Http.Body

set_option linter.all true

/--
Typeclass for types that can be converted to a `ByteArray`.
-/
class ToByteArray (α : Type) where

  /--
  Transforms into a `ByteArray`
  -/
  toByteArray : α → ByteArray

instance : ToByteArray ByteArray where
  toByteArray := id

instance : ToByteArray String where
  toByteArray := String.toUTF8

/--
Typeclass for types that can be decoded from a `ByteArray`. The conversion may fail with an error
message if the bytes are not valid for the target type.
-/
class FromByteArray (α : Type) where

  /--
  Attempts to decode a `ByteArray` into the target type, returning an error message on failure.
  -/
  fromByteArray : ByteArray → Except String α

instance : FromByteArray ByteArray where
  fromByteArray := .ok

instance : FromByteArray String where
  fromByteArray bs :=
    match String.fromUTF8? bs with
    | some s => .ok s
    | none => .error "invalid UTF-8 encoding"

end Std.Http.Body
