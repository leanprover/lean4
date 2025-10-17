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

This module exposes the `Config` structure describing timeouts, connection,
and header configurations for an HTTP client.
-/

namespace Std.Http.Client

set_option linter.all true

/--
Client connection configuration with validation.
-/
structure Config where
  /--
  Maximum number of requests per connection (for keep-alive).
  -/
  maxRequestsPerConnection : Nat := 100

  /--
  Maximum number of headers allowed per response.
  -/
  maxResponseHeaders : Nat := 50

  /--
  Maximum size of a single header value in bytes.
  -/
  maxHeaderValueSize : Nat := 8192

  /--
  Maximum waiting time for additional data before timing out.
  -/
  readTimeout : Time.Millisecond.Offset := 5000

  /--
  Timeout duration for keep-alive connections.
  -/
  keepAliveTimeout : { x : Time.Millisecond.Offset // 0 < x } := ⟨45000, by decide⟩

  /--
  Timeout for the entire request lifecycle (connect + read + write).
  -/
  requestTimeout : { x : Time.Millisecond.Offset // 0 < x } := ⟨10000, by decide⟩

  /--
  Whether to enable keep-alive connections.
  -/
  enableKeepAlive : Bool := true

  /--
  Output buffer flush threshold in bytes.
  -/
  writeBufferHighWatermark : Nat := 4096

  /--
  Maximum number of bytes to receive in a single read call.
  -/
  maxRecvChunkSize : Nat := 8192

  /--
  Default buffer size for request payloads.
  -/
  defaultRequestBufferSize : Nat := 8192

  /--
  The user-agent string to send by default.
  -/
  userAgent : Option HeaderValue := some (.new "LeanHTTPClient/1.1")

namespace Config

/--
Convert this client config into an HTTP/1.1 protocol configuration.
-/
def toH1Config (config : Config) : Protocol.H1.Machine.Config :=
  { maxMessages := config.maxRequestsPerConnection
    maxHeaders := config.maxResponseHeaders
    maxHeaderSize := config.maxHeaderValueSize
    enableKeepAlive := config.enableKeepAlive
    highMark := config.writeBufferHighWatermark
    identityHeader := config.userAgent
  }

end Config
end Std.Http.Client
