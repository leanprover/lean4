/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Internal.Parsec
public import Std.Http.Data
public import Std.Internal.Parsec.ByteArray
public import Std.Http.Protocol.H1.Config

/-!
This module defines parsers for HTTP/1.1 request and response lines, headers, and body framing. The
reference used is https://httpwg.org/specs/rfc9112.html.
-/

namespace Std.Http.Protocol.H1

open Std Internal Parsec ByteArray Internal Internal.Char

set_option linter.all true

/--
Checks if a byte may appear inside a field value.

This parser enforces strict ASCII-only field values and allows only `field-content`
(`HTAB / SP / VCHAR`).
-/
@[inline]
def isFieldVChar (c : UInt8) : Bool :=
  fieldContent (Char.ofUInt8 c)

/--
Checks if a byte may appear unescaped inside a quoted-string value.

Allows `HTAB / SP / %x21 / %x23-5B / %x5D-7E` (strict ASCII-only; no obs-text).
-/
@[inline]
def isQdText (c : UInt8) : Bool :=
  qdtext (Char.ofUInt8 c)

/--
Checks if a byte is optional whitespace (`OWS = SP / HTAB`, RFC 9110 §5.6.3).
-/
@[inline]
def isOwsByte (c : UInt8) : Bool :=
  ows (Char.ofUInt8 c)

-- Parser blocks

/--
Repeatedly applies `parser` until it returns `none` or the `maxCount` limit is
exceeded. Returns the collected results as an array.
-/
partial def manyItems {α : Type} (parser : Parser (Option α)) (maxCount : Nat) : Parser (Array α) := do
  let rec go (acc : Array α) : Parser (Array α) := do
    let step ← optional <| attempt do
      match ← parser with
      | none => fail "end of items"
      | some x => return x

    match step with
    | none =>
      return acc
    | some x =>
      let acc := acc.push x

      if acc.size > maxCount then
        fail s!"too many items: {acc.size} > {maxCount}"

      go acc
  go #[]


/--
Lifts an `Option` into the parser monad, failing with a generic message if the value is `none`.
-/
def liftOption (x : Option α) : Parser α :=
  if let some res := x then
    return res
  else
    fail "expected value but got none"

/--
Parses an HTTP token (RFC 9110 §5.6.2): one or more token characters, up to `limit` bytes.
Fails if the input starts with a non-token character or is empty.
-/
@[inline]
def parseToken (limit : Nat) : Parser ByteSlice :=
  takeWhileUpTo1 (fun c => tchar (Char.ofUInt8 c)) limit

/--
Parses a line terminator.
-/
@[inline]
def crlf : Parser Unit := do
  skipBytes "\r\n".toUTF8

/--
Consumes and ignores empty lines (`CRLF`) that appear before a request-line.

https://httpwg.org/specs/rfc9112.html#rfc.section.2.2:

"In the interest of robustness, a server that is expecting to receive and parse a request-line SHOULD
ignore at least one empty line (CRLF) received prior to the request-line."
-/
def skipLeadingRequestEmptyLines (limits : H1.Config) : Parser Unit := do
  let mut count := 0
  while (← peekWhen? (· == '\r'.toUInt8)).isSome do
    if count >= limits.maxLeadingEmptyLines then
      fail "too many leading empty lines"
    crlf
    count := count + 1

/--
Parses a single space (SP, 0x20).
-/
@[inline]
def sp : Parser Unit :=
  skipByte ' '.toUInt8

/--
Parses optional whitespace (OWS = *(SP / HTAB), RFC 9110 §5.6.3), bounded by
`limits.maxSpaceSequence`. Fails if more whitespace follows the limit, so oversized
padding is rejected rather than silently truncated.
-/
@[inline]
def ows (limits : H1.Config) : Parser Unit := do
  discard <| takeWhileUpTo isOwsByte limits.maxSpaceSequence

  if (← peekWhen? isOwsByte) |>.isSome then
    fail "invalid space sequence"
  else
    pure ()

/--
Parses a single ASCII hex digit and returns its numeric value (`0`–`15`).
-/
def hexDigit : Parser UInt8 := do
  let b ← any
  if isHexDigitByte b then
    if b ≥ '0'.toUInt8 && b ≤ '9'.toUInt8 then return b - '0'.toUInt8
    else if b ≥ 'A'.toUInt8 && b ≤ 'F'.toUInt8 then return b - 'A'.toUInt8 + 10
    else return b - 'a'.toUInt8 + 10
  else fail s!"invalid hex digit {Char.ofUInt8 b |>.quote}"

/--
Parses a hexadecimal integer (one or more hex digits, up to 16 digits).
Used for chunk-size lines in chunked transfer encoding.
-/
partial def hex : Parser Nat := do
  let rec go (acc : Nat) (count : Nat) : Parser Nat := do
    match ← optional (attempt hexDigit) with
    | some d =>
        if count + 1 > 16 then
          fail "chunk size too large"
        else
          go (acc * 16 + d.toNat) (count + 1)
    | none =>
        if count = 0 then
          -- Preserve EOF as incremental chunk-size parsing can request more data.
          -- For non-EOF invalid bytes, keep the specific parse failure.
          let _ ← peek!
          fail "expected hex digit"
        else
          return acc
  go 0 0

-- Actual parsers

/--
Parses `HTTP-version = HTTP-name "/" DIGIT "." DIGIT` and returns the major and
minor version numbers as a pair.
-/
def parseHttpVersionNumber : Parser (Nat × Nat) := do
  skipBytes "HTTP/".toUTF8
  let major ← digit
  skipByte '.'.toUInt8
  let minor ← digit
  pure ((major.toNat - 48), (minor.toNat - 48))

/--
Parses an HTTP version string and returns the corresponding `Version` value.
Fails if the version is not recognized by `Version.ofNumber?`.
-/
def parseHttpVersion : Parser Version := do
  let (major, minor) ← parseHttpVersionNumber
  liftOption <| Version.ofNumber? major minor

/-
method         = token

Every branch is wrapped in `attempt` so that `<|>` always backtracks on
failure, even after consuming bytes. This is strictly necessary only for the
P-group (POST / PUT / PATCH) which share a common first byte, but wrapping
all alternatives keeps the parser defensively correct if new methods are
added in the future.
-/
def parseMethod : Parser Method :=
  (attempt <| skipBytes "GET".toUTF8 <&> fun _ => Method.get)
  <|> (attempt <| skipBytes "HEAD".toUTF8 <&> fun _ => Method.head)
  <|> (attempt <| skipBytes "DELETE".toUTF8 <&> fun _ => Method.delete)
  <|> (attempt <| skipBytes "TRACE".toUTF8 <&> fun _ => Method.trace)
  <|> (attempt <| skipBytes "ACL".toUTF8 <&> fun _ => Method.acl)
  <|> (attempt <| skipBytes "QUERY".toUTF8 <&> fun _ => Method.query)
  <|> (attempt <| skipBytes "SEARCH".toUTF8 <&> fun _ => Method.search)
  <|> (attempt <| skipBytes "BASELINE-CONTROL".toUTF8 <&> fun _ => Method.baselineControl)
  <|> (attempt <| skipBytes "BIND".toUTF8 <&> fun _ => Method.bind)
  <|> (attempt <| skipBytes "CONNECT".toUTF8 <&> fun _ => Method.connect)
  <|> (attempt <| skipBytes "CHECKIN".toUTF8 <&> fun _ => Method.checkin)
  <|> (attempt <| skipBytes "CHECKOUT".toUTF8 <&> fun _ => Method.checkout)
  <|> (attempt <| skipBytes "COPY".toUTF8 <&> fun _ => Method.copy)
  <|> (attempt <| skipBytes "LABEL".toUTF8 <&> fun _ => Method.label)
  <|> (attempt <| skipBytes "LINK".toUTF8 <&> fun _ => Method.link)
  <|> (attempt <| skipBytes "LOCK".toUTF8 <&> fun _ => Method.lock)
  <|> (attempt <| skipBytes "MERGE".toUTF8 <&> fun _ => Method.merge)
  <|> (attempt <| skipBytes "MKACTIVITY".toUTF8 <&> fun _ => Method.mkactivity)
  <|> (attempt <| skipBytes "MKCALENDAR".toUTF8 <&> fun _ => Method.mkcalendar)
  <|> (attempt <| skipBytes "MKCOL".toUTF8 <&> fun _ => Method.mkcol)
  <|> (attempt <| skipBytes "MKREDIRECTREF".toUTF8 <&> fun _ => Method.mkredirectref)
  <|> (attempt <| skipBytes "MKWORKSPACE".toUTF8 <&> fun _ => Method.mkworkspace)
  <|> (attempt <| skipBytes "MOVE".toUTF8 <&> fun _ => Method.move)
  <|> (attempt <| skipBytes "OPTIONS".toUTF8 <&> fun _ => Method.options)
  <|> (attempt <| skipBytes "ORDERPATCH".toUTF8 <&> fun _ => Method.orderpatch)
  <|> (attempt <| skipBytes "POST".toUTF8 <&> fun _ => Method.post)
  <|> (attempt <| skipBytes "PUT".toUTF8 <&> fun _ => Method.put)
  <|> (attempt <| skipBytes "PATCH".toUTF8 <&> fun _ => Method.patch)
  <|> (attempt <| skipBytes "PRI".toUTF8 <&> fun _ => Method.pri)
  <|> (attempt <| skipBytes "PROPFIND".toUTF8 <&> fun _ => Method.propfind)
  <|> (attempt <| skipBytes "PROPPATCH".toUTF8 <&> fun _ => Method.proppatch)
  <|> (attempt <| skipBytes "REBIND".toUTF8 <&> fun _ => Method.rebind)
  <|> (attempt <| skipBytes "REPORT".toUTF8 <&> fun _ => Method.report)
  <|> (attempt <| skipBytes "UNBIND".toUTF8 <&> fun _ => Method.unbind)
  <|> (attempt <| skipBytes "UNCHECKOUT".toUTF8 <&> fun _ => Method.uncheckout)
  <|> (attempt <| skipBytes "UNLINK".toUTF8 <&> fun _ => Method.unlink)
  <|> (attempt <| skipBytes "UNLOCK".toUTF8 <&> fun _ => Method.unlock)
  <|> (attempt <| skipBytes "UPDATEREDIRECTREF".toUTF8 <&> fun _ => Method.updateredirectref)
  <|> (attempt <| skipBytes "UPDATE".toUTF8 <&> fun _ => Method.update)
  <|> (attempt <| skipBytes "VERSION-CONTROL".toUTF8 <&> fun _ => Method.versionControl)
  <|> (parseToken 64 *> fail "unrecognized method")

/--
Parses a request-target URI, up to `limits.maxUriLength` bytes.
Fails with `"uri too long"` if the target exceeds the configured limit.
-/
def parseURI (limits : H1.Config) : Parser ByteArray := do
  let uri ← takeUntilUpTo (· == ' '.toUInt8) limits.maxUriLength
  if uri.size == limits.maxUriLength then
    if (← peekWhen? (· != ' '.toUInt8)) |>.isSome then
      fail "uri too long"

  return uri.toByteArray

/--
Shared core for request-line parsing: parses `request-target SP HTTP-version CRLF`
and returns the `RequestTarget` together with the raw major/minor version numbers.

Both `parseRequestLine` and `parseRequestLineRawVersion` call this after consuming
the method token, keeping URI validation and version parsing in one place.
-/
def parseRequestLineBody (limits : H1.Config) : Parser (RequestTarget × Nat × Nat) := do
  let rawUri ← parseURI limits <* sp
  let uri ← match (Std.Http.URI.Parser.parseRequestTarget <* eof).run rawUri with
  | .ok res => pure res
  | .error res => fail res
  let versionPair ← parseHttpVersionNumber <* crlf
  return (uri, versionPair)

/--
Parses a request line and returns a fully-typed `Request.Head`.
`request-line = method SP request-target SP HTTP-version`
-/
public def parseRequestLine (limits : H1.Config) : Parser Request.Head := do
  skipLeadingRequestEmptyLines limits
  let method ← parseMethod <* sp
  let (uri, (major, minor)) ← parseRequestLineBody limits
  if major == 1 ∧ minor == 1 then
    return ⟨method, .v11, uri, .empty⟩
  else if major == 1 ∧ minor == 0 then
    return ⟨method, .v10, uri, .empty⟩
  else
    fail "unsupported HTTP version"

/--
Parses a request line and returns the recognized HTTP method and version when available.

request-line = method SP request-target SP HTTP-version
-/
public def parseRequestLineRawVersion (limits : H1.Config) : Parser (Method × RequestTarget × Option Version) := do
  skipLeadingRequestEmptyLines limits
  let method ← parseMethod <* sp
  let (uri, (major, minor)) ← parseRequestLineBody limits
  return (method, uri, Version.ofNumber? major minor)

/--
Parses a single header field line.

`field-line = field-name ":" OWS field-value OWS`
-/
def parseFieldLine (limits : H1.Config) : Parser (String × String) := do
  let name ← parseToken limits.maxHeaderNameLength
  let value ← skipByte ':'.toUInt8 *> ows limits *> optional (takeWhileUpTo isFieldVChar limits.maxHeaderValueLength) <* ows limits

  let name ← liftOption <| String.fromUTF8? name.toByteArray
  let value ← liftOption <| String.fromUTF8? <| value.map (·.toByteArray) |>.getD .empty
  let value := value.trimAsciiEnd.toString

  return (name, value)

/--
Parses a single header field line, or returns `none` when it sees the blank line that
terminates the header section.

```
field-line = field-name ":" OWS field-value OWS CRLF
```
-/
public def parseSingleHeader (limits : H1.Config) : Parser (Option (String × String)) := do
  let next ← peek?
  if next == some '\r'.toUInt8 ∨ next == some '\n'.toUInt8 then
    crlf
    pure none
  else
    some <$> (parseFieldLine limits <* crlf)

/--
Parses a backslash-escaped character inside a quoted-string.

`quoted-pair = "\" ( HTAB / SP / VCHAR )` — strict ASCII-only (no obs-text).
-/
def parseQuotedPair : Parser UInt8 := do
  skipByte '\\'.toUInt8
  let b ← any

  if quotedPairChar (Char.ofUInt8 b) then
    return b
  else
    fail s!"invalid quoted-pair byte: {Char.ofUInt8 b |>.quote}"

/--
Parses a quoted-string value, unescaping quoted-pairs.

`quoted-string = DQUOTE *( qdtext / quoted-pair ) DQUOTE`
-/
partial def parseQuotedString (maxLength : Nat) : Parser String := do
  skipByte '"'.toUInt8

  let rec loop (buf : ByteArray) (length : Nat) : Parser ByteArray := do
    let b ← any

    if b == '"'.toUInt8 then
      return buf
    else if b == '\\'.toUInt8 then
      let next ← any
      if quotedPairChar (Char.ofUInt8 next)
        then
          let length := length + 1
          if length > maxLength then
            fail "quoted-string too long"
          else
            loop (buf.push next) length
        else fail s!"invalid quoted-pair byte: {Char.ofUInt8 next |>.quote}"
    else if isQdText b then
      let length := length + 1
      if length > maxLength then
        fail "quoted-string too long"
      else
        loop (buf.push b) length
    else
      fail s!"invalid qdtext byte: {Char.ofUInt8 b |>.quote}"

  liftOption <| String.fromUTF8? (← loop .empty 0)

-- chunk-ext = *( BWS ";" BWS chunk-ext-name [ BWS "=" BWS chunk-ext-val] )
def parseChunkExt (limits : H1.Config) : Parser (Chunk.ExtensionName × Option Chunk.ExtensionValue) := do
  ows limits *> skipByte ';'.toUInt8 *> ows limits
  let name ← (liftOption =<< String.fromUTF8? <$> ByteSlice.toByteArray <$> parseToken limits.maxChunkExtNameLength) <* ows limits

  let some name := Chunk.ExtensionName.ofString? name
    | fail "invalid extension name"

  if (← peekWhen? (· == '='.toUInt8)) |>.isSome then
    -- RFC 9112 §7.1.1: BWS is allowed around "=".
    -- The `<* ows limits` after the name already consumed any trailing whitespace,
    -- so these ows calls are no-ops in practice, but kept for explicit grammar correspondence.
    ows limits *> skipByte '='.toUInt8 *> ows limits
    let value ← ows limits *> (parseQuotedString limits.maxChunkExtValueLength <|> liftOption =<< (String.fromUTF8? <$> ByteSlice.toByteArray <$> parseToken limits.maxChunkExtValueLength))

    let some value := Chunk.ExtensionValue.ofString? value
      | fail "invalid extension value"

    return (name, some value)

  return (name, none)

/--
Parses the size and extensions of a chunk.
-/
public def parseChunkSize (limits : H1.Config) : Parser (Nat × Array (Chunk.ExtensionName × Option Chunk.ExtensionValue)) := do
  let size ← hex
  let ext ← manyItems (optional (attempt (parseChunkExt limits))) limits.maxChunkExtensions
  crlf
  return (size, ext)

/--
Result of parsing partial or complete information.
-/
public inductive TakeResult
  | complete (data : ByteSlice)
  | incomplete (data : ByteSlice) (remaining : Nat)

/--
Parses a single chunk in chunked transfer encoding.
-/
public def parseChunkPartial (limits : H1.Config) : Parser (Option (Nat × Array (Chunk.ExtensionName × Option Chunk.ExtensionValue) × ByteSlice)) := do
  let (size, ext) ← parseChunkSize limits
  if size == 0 then
    return none
  else
    let data ← take size
    return some ⟨size, ext, data⟩

/--
Parses fixed-size data that can be incomplete.
-/
public def parseFixedSizeData (size : Nat) : Parser TakeResult := fun it =>
  if it.remainingBytes = 0 then
    .error it .eof
  else if it.remainingBytes < size then
    .success (it.forward it.remainingBytes) (.incomplete it.array[it.idx...(it.idx+it.remainingBytes)] (size - it.remainingBytes))
  else
    .success (it.forward size) (.complete (it.array[it.idx...(it.idx+size)]))

/--
Parses fixed-size chunk data that can be incomplete.
-/
public def parseChunkSizedData (size : Nat) : Parser TakeResult := do
  match ← parseFixedSizeData size with
  | .complete data => crlf *> return .complete data
  | .incomplete data res => return .incomplete data res

/--
Returns `true` if `name` (compared case-insensitively) is a field that MUST NOT appear in HTTP/1.1
trailer sections per RFC 9112 §6.5. Forbidden fields are those required for message framing
(`content-length`, `transfer-encoding`), routing (`host`), or connection management (`connection`).
-/
def isForbiddenTrailerField (name : String) : Bool :=
  let n := name.toLower
  n == "content-length" || n == "transfer-encoding" || n == "host" ||
  n == "connection" || n == "expect" || n == "te" ||
  n == "authorization" || n == "max-forwards" || n == "cache-control" ||
  n == "content-encoding" || n == "upgrade" || n == "trailer"

/--
Parses a trailer header (used after a chunked body), rejecting forbidden field names per RFC 9112
§6.5. Fields used for message framing (`content-length`, `transfer-encoding`), routing (`host`),
or connection management (`connection`, `te`, `upgrade`) are rejected to prevent trailer injection
attacks where a downstream proxy might re-interpret them.
-/
def parseTrailerHeader (limits : H1.Config) : Parser (Option (String × String)) := do
  let result ← parseSingleHeader limits
  if let some (name, _) := result then
    if isForbiddenTrailerField name then
      fail s!"forbidden trailer field: {name}"
  return result

/--
Parses trailer headers after a chunked body and returns them as an array of name-value pairs.

This is exposed for callers that need the trailer values directly (e.g. clients). The
internal protocol machine uses `parseLastChunkBody` instead, which discards trailer values.
-/
public def parseTrailers (limits : H1.Config) : Parser (Array (String × String)) := do
  let trailers ← manyItems (parseTrailerHeader limits) limits.maxTrailerHeaders
  crlf
  return trailers

/--
Returns `true` if `c` is a valid reason-phrase byte (`HTAB / SP / VCHAR`, strict ASCII-only).
-/
@[inline]
def isReasonPhraseByte (c : UInt8) : Bool :=
  fieldContent (Char.ofUInt8 c)

/--
Parses a reason phrase (text after status code).

Allows only `HTAB / SP / VCHAR` bytes (strict ASCII-only).
-/
def parseReasonPhrase (limits : H1.Config) : Parser String := do
  let bytes ← takeWhileUpTo isReasonPhraseByte limits.maxReasonPhraseLength
  liftOption <| String.fromUTF8? bytes.toByteArray

/--
Parses a status-code (3 decimal digits), the following reason phrase, and the
terminating CRLF; returns a typed `Status`.
-/
def parseStatusCode (limits : H1.Config) : Parser Status := do
  let d1 ← digit
  let d2 ← digit
  let d3 ← digit
  let code := (d1.toNat - 48) * 100 + (d2.toNat - 48) * 10 + (d3.toNat - 48)
  sp
  let phrase ← parseReasonPhrase limits <* crlf

  if h : IsValidReasonPhrase phrase then
    if let some status := Status.ofCode (some ⟨phrase, h⟩) code.toUInt16 then
      return status

  fail "invalid status code"

/--
Parses a status line and returns a fully-typed `Response.Head`.
`status-line = HTTP-version SP status-code SP [ reason-phrase ]`
Accepts only HTTP/1.1. For parsing where the version may be unrecognized and must be
mapped to an error event, use `parseStatusLineRawVersion`.
-/
public def parseStatusLine (limits : H1.Config) : Parser Response.Head := do
  let (major, minor) ← parseHttpVersionNumber <* sp
  let status ← parseStatusCode limits
  if major == 1 ∧ minor == 1 then
    return { status, version := .v11, headers := .empty }
  else if major == 1 ∧ minor == 0 then
    return { status, version := .v10, headers := .empty }
  else
    fail "unsupported HTTP version"

/--
Parses a status line and returns the status code plus recognized HTTP version when available.
Consumes and discards the reason phrase.

status-line = HTTP-version SP status-code SP [ reason-phrase ] CRLF
-/
public def parseStatusLineRawVersion (limits : H1.Config) : Parser (Status × Option Version) := do
  let (major, minor) ← parseHttpVersionNumber <* sp
  let status ← parseStatusCode limits
  return (status, Version.ofNumber? major minor)

/--
Parses the trailer section that follows the last chunk size line (`0\r\n`).
-/
public def parseLastChunkBody (limits : H1.Config) : Parser Unit := do
  discard <| manyItems (parseTrailerHeader limits) limits.maxTrailerHeaders
  crlf

end Std.Http.Protocol.H1
