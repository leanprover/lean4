/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Http.Data

public section

/-!
# Proxy Selection

This module defines `Proxy`, the transport endpoint a request is dispatched to, and `ProxySelector`,
the policy that picks one per origin.
-/

namespace Std.Http.Client

set_option linter.all true

/--
Where a request's transport connection is established.
-/
inductive Proxy where

  /--
  Connect straight to the request's own origin.
  -/
  | direct

  /--
  Connect to an HTTP proxy at `host:port` instead of the origin.
  -/
  | http (host : String) (port : UInt16)
deriving Inhabited, Repr, BEq

/--
Chooses the proxy to use for each origin the client connects to. Selection is a pure function of the
origin, so a selector that consults the environment or a configuration file should read it once
while being built.
-/
structure ProxySelector where

  /--
  The proxy to route connections to `origin` through.
  -/
  select : URI.Origin → Proxy

namespace ProxySelector

/--
Connects every origin directly.
-/
def direct : ProxySelector where
  select _ := .direct

instance : Inhabited ProxySelector := ⟨direct⟩

/--
Routes every origin through the HTTP proxy at `host:port`.
-/
def of (host : String) (port : UInt16) : ProxySelector where
  select _ := .http host port

/--
Connects directly to the origins satisfying `bypass`, deferring to `selector` for the rest.
-/
def bypassing (selector : ProxySelector) (bypass : URI.Origin → Bool) : ProxySelector where
  select origin := if bypass origin then .direct else selector.select origin

end ProxySelector

end Std.Http.Client
