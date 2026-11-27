/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Async
public import Std.Http.Data
public import Std.Http.Client.Error

public section

/-!
# Interceptors

An `Interceptor` sees every hop a client sends: each redirect, retry and authenticated retry is one
hop. It can rewrite a request before it goes, or fail it, and it is told of every response head the
client receives, informational ones included.
-/

namespace Std.Http.Client

open Std.Async

set_option linter.all true

/--
Hooks a client runs around each hop. Each gets the origin the hop is addressed to.

The request a hook sees and returns is the request as the caller and the redirect rules built it:
the client then completes it for the connection (the target form a proxy needs, `Host`, cookies).
A hook that adds credentials should check the origin, since a redirect can lead anywhere.
-/
structure Interceptor where
  /--
  Runs before each hop is sent, and returns the request to send, or the error that fails the request.
  A failure is never retried.
  -/
  onRequest : URI.Origin → Request.Head → Async (Except Error Request.Head) := fun _ head =>
    pure (.ok head)

  /--
  Runs when the final response head of each hop arrives, before the client acts on it: redirects
  and challenges the client answers itself included.
  -/
  onResponse : URI.Origin → Request.Head → Response.Head → Async Unit := fun _ _ _ => pure ()

  /--
  Runs for each informational (`1xx`) response a hop receives, such as `103 Early Hints`.
  -/
  onInformational : URI.Origin → Request.Head → Response.Head → Async Unit := fun _ _ _ => pure ()

end Std.Http.Client
