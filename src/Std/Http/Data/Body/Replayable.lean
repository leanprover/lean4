/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Http.Data.Body.Basic

public section

/-!
# Body.Replayable

A typeclass for HTTP body types whose content can be re-read from the start.

`Body.Full` implements `Replayable`; `Body.Stream` does not because its bytes come from a live
producer that has already been consumed and cannot be rewound.
-/

namespace Std.Http.Body
open Std Async

set_option linter.all true

/--
A body that can be re-read from the start.
-/
class Replayable (α : Type) where

  /--
  Resets this body's read state in place so it can be read from the start again.
  -/
  resetInPlace : α → Async Unit

end Std.Http.Body
