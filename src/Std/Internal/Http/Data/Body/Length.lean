/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Init.Data.Repr

public section

/-!
# Length

This module defines the `Length` type, that represents the Content-Length or Transfer-Encoding
of an HTTP request or response.
-/

namespace Std.Http.Body

set_option linter.all true

/--
Size of the body of a response or request.
-/
inductive Length
  /--
  Indicates that the HTTP message body uses **chunked transfer encoding**.
  -/
  | chunked

  /--
  Indicates that the HTTP message body has a **fixed, known length**, as specified by the
  `Content-Length` header.
  -/
  | fixed (n : Nat)
deriving Repr, BEq

namespace Length

/--
Checks if the `Length` is chunked.
-/
def isChunked : Length → Bool
  | .chunked => true
  | _ => false

end Std.Http.Body.Length
