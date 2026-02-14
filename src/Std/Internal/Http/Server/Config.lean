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

This module exposes the `Config`, a structure that describes timeout, request and headers
configuration of an HTTP Server.
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
  Maximum waiting time for more data.
  -/
  lingeringTimeout : Time.Millisecond.Offset := 10000

  /--
  Timeout for keep-alive connections
  -/
  keepAliveTimeout : { x : Time.Millisecond.Offset // 0 < x } :=  ⟨12000, by decide⟩

  /--
  Maximum time for requesting more data.
  -/
  requestTimeout : { x : Time.Millisecond.Offset // 0 < x } := ⟨13000, by decide⟩

  /--
  Whether to enable keep-alive connections by default.
  -/
  enableKeepAlive : Bool := true

  /--
  The maximum size that the connection can receive in a single recv call.
  -/
  maximumRecvSize : Nat := 8192

  /--
  Default buffer size for the connection
  -/
  defaultPayloadBytes : Nat := 8192

  /--
  Whether to automatically generate the `Date` header in responses.
  -/
  generateDate : Bool := true

  /--
  The server name.
  -/
  serverName : Option Header.Value := some (.mk "LeanHTTP/1.1")

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
Converts to HTTP 1.1 config
-/
def toH1Config (config : Config) : Protocol.H1.Config where
  maxMessages := config.maxRequests
  maxHeaders := config.maxHeaders
  maxUriLength := config.maxUriLength
  maxHeaderNameLength := config.maxHeaderNameLength
  maxHeaderValueLength := config.maxHeaderValueLength
  maxSpaceSequence := config.maxSpaceSequence
  maxChunkExtNameLength := config.maxChunkExtNameLength
  maxChunkExtValueLength := config.maxChunkExtValueLength
  maxReasonPhraseLength := config.maxReasonPhraseLength
  maxTrailerHeaders := config.maxTrailerHeaders
  enableKeepAlive := config.enableKeepAlive
  identityHeader := config.serverName

end Std.Http.Config
