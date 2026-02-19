/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Internal.Http.Data
public import Std.Internal.Http.Internal

public section

/-!
# HTTP/1.1 Configuration

This module defines the configuration options for HTTP/1.1 protocol processing,
including connection limits, header constraints, and various size limits.
-/

namespace Std.Http.Protocol.H1

set_option linter.all true

open Std Internal Parsec ByteArray
open Internal

/--
Connection limits and parser bounds configuration.
-/
structure Config where
  /--
  Maximum number of messages per connection.
  -/
  maxMessages : Nat := 100

  /--
  Maximum number of headers allowed per message.
  -/
  maxHeaders : Nat := 100

  /--
  Whether to enable keep-alive connections by default.
  -/
  enableKeepAlive : Bool := true

  /--
  The server name (for sending responses) or user agent (for sending requests)
  -/
  identityHeader : Option Header.Value := none

  /--
  Maximum length of request URI (default: 8192 bytes)
  -/
  maxUriLength : Nat := 8192

  /--
  Maximum number of bytes consumed while parsing request/status start-lines (default: 8192 bytes).
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
  Maximum number of spaces in delimiter sequences (default: 256)
  -/
  maxSpaceSequence : Nat := 256

  /--
  Maximum number of extensions on a single chunk-size line (default: 16).
  -/
  maxChunkExtensions : Nat := 16

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
  Maximum allowed total body size per message in bytes (default: 64 MiB).
  This limit applies across all body framing modes.
  -/
  maxBodySize : Nat := 64 * 1024 * 1024

  /--
  Maximum length of reason phrase (default: 512 bytes)
  -/
  maxReasonPhraseLength : Nat := 512

  /--
  Maximum number of trailer headers (default: 100)
  -/
  maxTrailerHeaders : Nat := 100

end Std.Http.Protocol.H1
