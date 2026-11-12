/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Http.Data
public import Std.Http.Internal

public section

/-!
# HTTP/1.1 configuration

Connection limits and parser bounds of the HTTP/1.1 machine.
-/

namespace Std.Http.Protocol.H1

set_option linter.all true

/--
Connection limits and parser bounds.
-/
structure Config where
  /--
  The number of requests (server) or responses (client) per connection.
  -/
  maxMessages : Nat := 100

  /--
  The number of header fields per message.
  -/
  maxHeaders : Nat := 100

  /--
  The bytes of a message's header fields, counting `: ` and the line break of each (64 KiB).
  -/
  maxHeaderBytes : Nat := 65536

  /--
  Whether connections are kept alive between messages.
  -/
  enableKeepAlive : Bool := true

  /--
  The `Server` field a server adds to its responses, or the `User-Agent` field a client adds to its
  requests, unless the message has one. `none` adds neither.
  -/
  agentName : Option Header.Value := none

  /--
  The bytes of a request-target (8 KiB).
  -/
  maxUriLength : Nat := 8192

  /--
  The bytes of a request or status line (8 KiB).
  -/
  maxStartLineLength : Nat := 8192

  /--
  The bytes of a header field name.
  -/
  maxHeaderNameLength : Nat := 256

  /--
  The bytes of a header field value (8 KiB).
  -/
  maxHeaderValueLength : Nat := 8192

  /--
  The spaces and tabs in one run of whitespace.
  -/
  maxSpaceSequence : Nat := 16

  /--
  The empty lines a server skips before a request line (RFC 9112 §2.2).
  -/
  maxLeadingEmptyLines : Nat := 8

  /--
  The extensions on one chunk-size line.
  -/
  maxChunkExtensions : Nat := 16

  /--
  The bytes of a chunk extension name.
  -/
  maxChunkExtNameLength : Nat := 256

  /--
  The bytes of a chunk extension value.
  -/
  maxChunkExtValueLength : Nat := 256

  /--
  The bytes of a chunk-size line, extensions included (8 KiB).
  -/
  maxChunkLineLength : Nat := 8192

  /--
  The data bytes of one chunk (8 MiB).
  -/
  maxChunkSize : Nat := 8 * 1024 * 1024

  /--
  The bytes of a message body (64 MiB). For a chunked body the chunk-size lines, the line breaks
  after chunk data and the trailer section count too, so the bytes a body takes on the wire stay
  bounded however small its chunks are.
  -/
  maxBodySize : Nat := 64 * 1024 * 1024

  /--
  The bytes of a reason phrase.
  -/
  maxReasonPhraseLength : Nat := 512

  /--
  The fields of a trailer section.
  -/
  maxTrailerHeaders : Nat := 20

  /--
  Transfer codings other than `chunked` that a server accepts on a request because the application
  decodes them, such as `"gzip"`, compared case-insensitively. The machine removes only the chunked
  framing, so the body reaches the application still coded, and the request's `Transfer-Encoding`
  field says which codings to decode. A request with any other coding gets 501 Not Implemented
  (RFC 9112 §6.1).
  -/
  acceptedTransferCodings : Array String := #[]

end Std.Http.Protocol.H1
