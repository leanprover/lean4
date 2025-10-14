/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Time
public import Std.Internal.Http.Protocol.H1

public section

/-!
# Config

This module exposes the `Config` that is a structure that describes all the timeout, request, headers
configuration of a HTTP Server.
-/

namespace Std.Http

set_option linter.all true

/--
Connection limits configuration with validation.
-/
structure Config where
  /--
  Maximum number of requests per connection.
  -/
  maxRequests : Nat := 100

  /--
  Maximum number of headers allowed per request.
  -/
  maxHeaders : Nat := 50

  /--
  Maximum size of a single header value.
  -/
  maxHeaderSize : Nat := 8192

  /--
  Maximum waiting time for more data.
  -/
  lingeringTimeout : Time.Millisecond.Offset := 5000

  /--
  Timeout for keep-alive connections
  -/
  keepAliveTimeout : { x : Time.Millisecond.Offset // 0 < x } :=  ⟨45000, by decide⟩

  /--
  Maximum timeout time for request more data.
  -/
  requestTimeout : { x : Time.Millisecond.Offset // 0 < x } := ⟨10000, by decide⟩

  /--
  Whether to enable keep-alive connections by default.
  -/
  enableKeepAlive : Bool := true

  /--
  Size threshold for flushing output buffer.
  -/
  highMark : Nat := 4096

  /--
  The maximum size that the connection can receive in a single recv call.
  -/
  maximumRecvSize : Nat := 8192

  /--
  Default buffer size for the connection
  -/
  defaultPayloadBytes : Nat := 8192

  /--
  The server name.
  -/
  serverName : Option HeaderValue := some (.new "LeanHTTP/1.1")

namespace Config

/--
Converts to HTTP 1.1 config
-/
def toH1Config (config : Config) : Protocol.H1.Machine.Config :=
  { maxMessages := config.maxRequests
    maxHeaders := config.maxHeaders
    maxHeaderSize := config.maxHeaderSize
    enableKeepAlive := config.enableKeepAlive
    highMark := config.highMark
    identityHeader := config.serverName
  }

end Std.Http.Config
