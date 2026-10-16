/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Async
public import Std.Http.Data

public section

/-!
# Cookie Handling

This module defines `CookieHandler`, the policy a client consults to attach cookies to outgoing
requests and to retain the ones responses set.

Reference: https://www.rfc-editor.org/rfc/rfc6265.html
-/

namespace Std.Http.Client

open Std.Async

set_option linter.all true

/--
Stores cookies received from responses and supplies them back on later requests. The client calls
`store` on every response it receives and `load` on every request it sends, including each hop of a
redirect chain, so a handler sees cross-origin hops as separate origins.

Cookies are exchanged as raw header values rather than a parsed cookie type: it is the handler that
decides how `Set-Cookie` attributes are interpreted.
-/
structure CookieHandler where

  /--
  The `Cookie` header values to attach to a request for `origin` and `target`.
  -/
  load : URI.Origin → RequestTarget → Async (Array Header.Value)

  /--
  Records the `Set-Cookie` headers of a response received from `origin` for `target`. The full
  response header block is passed so that attributes can be interpreted against headers such as
  `Date`.
  -/
  store : URI.Origin → RequestTarget → Headers → Async Unit

end Std.Http.Client
