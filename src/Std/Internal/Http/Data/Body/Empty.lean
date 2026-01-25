/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Internal.Async
public import Std.Internal.Http.Data.Chunk
public import Std.Internal.Http.Data.Request
public import Std.Internal.Http.Data.Response
public import Std.Internal.Http.Data.Body.Length

public section

/-!
# Empty

An `Empty` represents an HTTP body with no content. This is useful for requests and responses
that do not carry a body, such as GET requests or 204 No Content responses.
-/

namespace Std.Http.Body
open Std Internal IO Async

set_option linter.all true

/--
An empty HTTP body type that contains no data.
-/
structure Empty where
  private mk ::
deriving Inhabited, Nonempty

namespace Empty

/--
The singleton empty body value.
-/
def val : Empty := Empty.mk

/--
Creates a new empty body.
-/
def new : Async Empty :=
  pure val

/--
Non-blocking receive. Always returns `none` since there is no data.
-/
def recv? (_ : Empty) : Async (Option ByteArray) :=
  pure none

/--
Blocking receive. Always returns `none` since there is no data.
-/
def recv (_ : Empty) (_ : Option UInt64) : Async (Option ByteArray) :=
  pure none

/--
Sending to an empty body is a no-op.
-/
def send (_ : Empty) (_ : ByteArray) : Async Unit :=
  pure ()

/--
An empty body is always closed.
-/
def isClosed (_ : Empty) : Async Bool :=
  pure true

/--
Returns `none` since an empty body has no size.
-/
def size? (_ : Empty) : Async (Option Body.Length) :=
  pure (some (.fixed 0))

/--
Closing an empty body is a no-op.
-/
def close (_ : Empty) : Async Unit :=
  pure ()

/--
Creates a `Selector` that immediately resolves to `none`.
-/
def recvSelector (_ : Empty) : Selector (Option Chunk) where
  tryFn := pure (some none)
  registerFn waiter := do
    let lose := return ()
    let win promise := promise.resolve (.ok none)
    waiter.race lose win
  unregisterFn := pure ()

instance : EmptyCollection Empty where
  emptyCollection := val

end Empty

end Std.Http.Body

namespace Std.Http.Request.Builder

/--
Builds a request with an empty body.
-/
def blank (builder : Builder) : Request Body.Empty :=
  { head := builder.head, body := Body.Empty.val }

end Std.Http.Request.Builder

namespace Std.Http.Response.Builder

/--
Builds a response with an empty body.
-/
def blank (builder : Builder) : Response Body.Empty :=
  { head := builder.head, body := Body.Empty.val }

end Std.Http.Response.Builder
