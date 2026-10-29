/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Async
public import Std.Http.Data
public import Std.Http.Client.Proxy

public section

/-!
# Authentication

This module defines `Challenge`, the `401`/`407` challenge a peer issues, and `Authenticator`, the
policy that answers it with credentials.

Reference: https://www.rfc-editor.org/rfc/rfc9110.html#section-11
-/

namespace Std.Http.Client

open Std.Async

set_option linter.all true

/--
Whether an authentication challenge came from the origin server or from a proxy.
-/
inductive Challenge.Kind where

  /--
  A `401 Unauthorized` from the origin server, answered in `Authorization`.
  -/
  | server

  /--
  A `407 Proxy Authentication Required` from a proxy, answered in `Proxy-Authorization`.
  -/
  | proxy
deriving Inhabited, Repr, BEq

/--
An authentication challenge an `Authenticator` is asked to answer.
-/
structure Challenge where

  /--
  Whether the origin server or a proxy issued the challenge.
  -/
  kind : Challenge.Kind

  /--
  The origin the challenged request was sent to.
  -/
  origin : URI.Origin

  /--
  The method of the challenged request. Schemes whose response covers the request line, such as
  `Digest`, need it.
  -/
  method : Method

  /--
  The request target that was challenged.
  -/
  target : RequestTarget

  /--
  Headers of the challenging response. The challenge itself is carried by `challengeHeader`, which
  may appear more than once when the peer offers a choice of schemes.
  -/
  headers : Headers

  /--
  The proxy the challenged request went through, `.direct` when it went straight to `origin`. A
  proxy challenge always comes with a proxy here.
  -/
  proxy : Proxy := .direct

  /--
  The origin the caller addressed, before any redirect. It differs from `origin` when a redirect
  took the request to another origin, which the caller's credentials may not be meant for.
  -/
  initialOrigin : URI.Origin := origin
deriving Repr

namespace Challenge

/--
The response header carrying this challenge.
-/
def challengeHeader : Challenge → Header.Name
  | { kind := .server, .. } => .wwwAuthenticate
  | { kind := .proxy, .. } => .proxyAuthenticate

/--
The request header an answer to this challenge is sent in.
-/
def credentialHeader : Challenge → Header.Name
  | { kind := .server, .. } => .authorization
  | { kind := .proxy, .. } => .proxyAuthorization

/--
The challenges offered by the peer, in the order they were received.
-/
def offered (challenge : Challenge) : Array Header.Value :=
  challenge.headers.getAll? challenge.challengeHeader
  |>.getD #[]

end Challenge

/--
Supplies credentials in response to a `401` or `407`. The client retries the request once with the
returned value in `Challenge.credentialHeader`; returning `none` declines the challenge and reports
the response as-is.

The result is the full credential field value (`"Basic dXNlcjpwdw=="`, `"Bearer …"`, a `Digest`
response, …), so an authenticator is free to implement any scheme.
-/
structure Authenticator where

  /--
  The credentials answering `challenge`, or `none` to decline it.
  -/
  authenticate : Challenge → Async (Option Header.Value)

namespace Authenticator

/--
Answers with the same credential every proxy challenge, and every server challenge from the origin
the caller addressed. A server challenge from an origin a redirect led to is declined, so the
credential does not follow the request to another host. Use `restrict` to narrow it further, for
instance to server challenges only.
-/
def const (credential : Header.Value) : Authenticator where
  authenticate challenge :=
    if challenge.kind == .server ∧ challenge.origin != challenge.initialOrigin then pure none
    else pure (some credential)

/--
Declines the challenges rejected by `accepts`, deferring to `authenticator` for the rest. Use it to
scope credentials to one origin or to server challenges only.
-/
def restrict (authenticator : Authenticator) (accepts : Challenge → Bool) : Authenticator where
  authenticate challenge :=
    if accepts challenge then authenticator.authenticate challenge else pure none

end Authenticator

end Std.Http.Client
