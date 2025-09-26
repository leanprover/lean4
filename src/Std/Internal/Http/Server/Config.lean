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

namespace Std
namespace Http

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
  Connection timeout in milliseconds.
  -/
  timeoutMilliseconds : Time.Millisecond.Offset := 1000

  /--
  Whether to enable keep-alive connections by default.
  -/
  enableKeepAlive : Bool := true

  /--
  Size threshold for flushing output buffer.
  -/
  highMark : Nat := 4096

  /--
  Default buffer size for the connection.
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
  { maxRequests := config.maxRequests
    maxHeaders := config.maxHeaders
    maxHeaderSize := config.maxHeaderSize
    timeoutMilliseconds := config.timeoutMilliseconds
    enableKeepAlive := config.enableKeepAlive
    highMark := config.highMark
    serverName := config.serverName
  }
