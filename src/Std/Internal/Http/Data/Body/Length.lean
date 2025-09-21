/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Init.Data.Repr

public section

namespace Std
namespace Http
namespace Body

/--
Size of the body of a response or request.
-/
inductive Length
  | chunked
  | fixed (n : Nat)
deriving Repr, BEq

namespace Length

/--
Checks if the `Length` is chunked.
-/
def isChunked : Length → Bool
  | .chunked => true
  | _ => false

end Length
