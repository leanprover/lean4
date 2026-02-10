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

end Std.Http.Body
