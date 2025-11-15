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
  maxRequestsPerConnection : Nat := 1000

  /--
  Maximum number of headers allowed per response.
  -/
  maxResponseHeaders : Nat := 200

  /--
  Maximum waiting time for additional data before timing out.
  -/
  readTimeout : Time.Millisecond.Offset := 30000

  /--
  Timeout duration for keep-alive connections.
  -/
  keepAliveTimeout : { x : Time.Millisecond.Offset // 0 < x } := ⟨60000, by decide⟩

  /--
  Timeout for the entire request lifecycle (connect + read + write).
  -/
  requestTimeout : { x : Time.Millisecond.Offset // 0 < x } := ⟨120000, by decide⟩

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
  maxRecvChunkSize : Nat := 16384

  /--
  Default buffer size for request payloads.
  -/
  defaultRequestBufferSize : Nat := 16384

  /--
  The user-agent string to send by default.
  -/
  userAgent : Option HeaderValue := some (.new "lean-http/1.1")

  /--
  Maximum length of HTTP method token (default: 16 bytes)
  -/
  maxMethodLength : Nat := 16

  /--
  Maximum length of request URI (default: 8192 bytes)
  -/
  maxUriLength : Nat := 8192

  /--
  Maximum length of header field name (default: 256 bytes)
  -/
  maxHeaderNameLength : Nat := 256

  /--
  Maximum length of header field value (default: 8192 bytes)
  -/
  maxHeaderValueLength : Nat := 8192

  /--
  Maximum number of spaces in delimiter sequences (default: 256)
  -/
  maxSpaceSequence : Nat := 256

  /--
  Maximum length of chunk extension name (default: 256 bytes)
  -/
  maxChunkExtNameLength : Nat := 256

  /--
  Maximum length of chunk extension value (default: 256 bytes)
  -/
  maxChunkExtValueLength : Nat := 256

  /--
  Maximum length of reason phrase (default: 512 bytes)
  -/
  maxReasonPhraseLength : Nat := 512

  /--
  Maximum number of trailer headers (default: 100)
  -/
  maxTrailerHeaders : Nat := 100

namespace Config

/--
Convert this client config into an HTTP/1.1 protocol configuration.
-/
def toH1Config (config : Config) : Protocol.H1.Config where
  maxMessages := config.maxRequestsPerConnection
  maxHeaders := config.maxResponseHeaders
  maxMethodLength := config.maxMethodLength
  maxUriLength := config.maxUriLength
  maxHeaderNameLength := config.maxHeaderNameLength
  maxHeaderValueLength := config.maxHeaderValueLength
  maxSpaceSequence := config.maxSpaceSequence
  maxChunkExtNameLength := config.maxChunkExtNameLength
  maxChunkExtValueLength := config.maxChunkExtValueLength
  maxReasonPhraseLength := config.maxReasonPhraseLength
  maxTrailerHeaders := config.maxTrailerHeaders
  enableKeepAlive := config.enableKeepAlive
  identityHeader := config.userAgent

end Config
end Std.Http.Client
