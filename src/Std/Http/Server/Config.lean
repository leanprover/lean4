/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Time
public import Std.Http.Protocol.H1

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
  Maximum number of simultaneous active connections (default: 1024).
  Setting this to `0` disables the limit entirely: the server will accept any number of
  concurrent connections and no semaphore-based cap is enforced. Use with care — an
  unconstrained server may exhaust file descriptors or memory under adversarial load.
  -/
  maxConnections : Nat := 1024

  /--
  Maximum number of requests per connection.
  -/
  maxRequests : Nat := 100

  /--
  Maximum number of headers allowed per request.
  -/
  maxHeaders : Nat := 50

  /--
  Maximum aggregate byte size of all header field lines in a single message
  (name + value bytes plus 4 bytes per line for `: ` and `\r\n`). Default: 64 KiB.
  -/
  maxHeaderBytes : Nat := 65536

  /--
  Timeout (in milliseconds) for receiving additional data while a request is actively being
  processed (e.g. reading the request body). Applies after the request headers have been parsed
  and replaces the keep-alive timeout for the duration of the request.
  -/
  lingeringTimeout : Time.Millisecond.Offset := 10000

  /--
  Timeout for keep-alive connections
  -/
  keepAliveTimeout : { x : Time.Millisecond.Offset // x > 0 } :=  ⟨12000, by decide⟩

  /--
  Maximum time (in milliseconds) allowed to receive the complete request headers after the first
  byte of a new request arrives. This prevents Slowloris-style attacks where a client sends bytes
  at a slow rate to hold a connection slot open without completing a request. Once a request starts,
  each individual read must complete within this window. Default: 5 seconds.
  -/
  headerTimeout : Time.Millisecond.Offset := 5000

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
  The `Server` header value injected into outgoing responses.
  `none` suppresses the header entirely.
  -/
  serverName : Option Header.Value := some (.mk "LeanHTTP/1.1")

  /--
  Maximum length of request URI (default: 8192 bytes)
  -/
  maxUriLength : Nat := 8192

  /--
  Maximum number of bytes consumed while parsing request start-lines (default: 8192 bytes).
  -/
  maxStartLineLength : Nat := 8192

  /--
  Maximum length of header field name (default: 256 bytes)
  -/
  maxHeaderNameLength : Nat := 256

  /--
  Maximum length of header field value (default: 8192 bytes)
  -/
  maxHeaderValueLength : Nat := 8192

  /--
  Maximum number of spaces in delimiter sequences (default: 16)
  -/
  maxSpaceSequence : Nat := 16

  /--
  Maximum number of leading empty lines (bare CRLF) to skip before a request-line
  (RFC 9112 §2.2 robustness). Default: 8.
  -/
  maxLeadingEmptyLines : Nat := 8

  /--
  Maximum length of chunk extension name (default: 256 bytes)
  -/
  maxChunkExtNameLength : Nat := 256

  /--
  Maximum length of chunk extension value (default: 256 bytes)
  -/
  maxChunkExtValueLength : Nat := 256

  /--
  Maximum number of bytes consumed while parsing one chunk-size line with extensions (default: 8192 bytes).
  -/
  maxChunkLineLength : Nat := 8192

  /--
  Maximum allowed chunk payload size in bytes (default: 8 MiB).
  -/
  maxChunkSize : Nat := 8 * 1024 * 1024

  /--
  Maximum allowed total body size per request in bytes (default: 64 MiB).
  -/
  maxBodySize : Nat := 64 * 1024 * 1024

  /--
  Maximum length of reason phrase (default: 512 bytes)
  -/
  maxReasonPhraseLength : Nat := 512

  /--
  Maximum number of trailer headers (default: 20)
  -/
  maxTrailerHeaders : Nat := 20

  /--
  Maximum number of extensions on a single chunk-size line (default: 16).
  -/
  maxChunkExtensions : Nat := 16

namespace Config

/--
Converts to HTTP/1.1 config.
-/
def toH1Config (config : Config) : Protocol.H1.Config where
  maxMessages := config.maxRequests
  maxHeaders := config.maxHeaders
  maxHeaderBytes := config.maxHeaderBytes
  enableKeepAlive := config.enableKeepAlive
  agentName := config.serverName
  maxUriLength := config.maxUriLength
  maxStartLineLength := config.maxStartLineLength
  maxHeaderNameLength := config.maxHeaderNameLength
  maxHeaderValueLength := config.maxHeaderValueLength
  maxSpaceSequence := config.maxSpaceSequence
  maxLeadingEmptyLines := config.maxLeadingEmptyLines
  maxChunkExtensions := config.maxChunkExtensions
  maxChunkExtNameLength := config.maxChunkExtNameLength
  maxChunkExtValueLength := config.maxChunkExtValueLength
  maxChunkLineLength := config.maxChunkLineLength
  maxChunkSize := config.maxChunkSize
  maxBodySize := config.maxBodySize
  maxReasonPhraseLength := config.maxReasonPhraseLength
  maxTrailerHeaders := config.maxTrailerHeaders

end Std.Http.Config
