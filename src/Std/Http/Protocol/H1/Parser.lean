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
public import Std.Http.Protocol.H1.LineScan
import Init.Data.String.Lossy

/-!
This module defines parsers for HTTP/1.1 request and response lines, headers, and body framing. The
reference used is https://httpwg.org/specs/rfc9112.html.
-/

namespace Std.Http.Protocol.H1

open Std Std.Internal Parsec ByteArray Internal.Char
open LineScan (Class)

set_option linter.all true

-- Parser blocks

/--
Like `optional (attempt p)`, but an `.eof` failure of `p` is propagated instead of becoming `none`.

The protocol machine treats `.eof` as "need more data". If an item is cut off by the end of the
currently buffered input, swallowing the `.eof` would backtrack and let the next parser fail on the
unfinished item's bytes, turning a valid message into a hard parse error.
-/
@[inline]
def optionalUnlessEof (p : Parser α) : Parser (Option α) := fun it =>
  match p it with
  | .success rem res => .success rem (some res)
  | .error rem .eof => .error rem .eof
  | .error _ _ => .success it none

/--
Parses an HTTP token (RFC 9110 §5.6.2): one or more token characters, up to `limit` bytes.
Fails if the input starts with a non-token character or is empty.
-/
@[inline]
def parseToken (limit : Nat) : Parser ByteSlice :=
  takeWhileUpTo1 (Class.token.accepts ·) limit

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
  discard <| takeWhileUpTo (Class.ows.accepts ·) limits.maxSpaceSequence

  if (← peekWhen? (Class.ows.accepts ·)) |>.isSome then
    fail "invalid space sequence"
  else
    pure ()

/--
The value of an ASCII hex digit (`isHexDigitByte`).
-/
@[inline]
def hexValue (b : UInt8) : Nat :=
  if b ≤ '9'.toUInt8 then (b - '0'.toUInt8).toNat
  else if b ≤ 'F'.toUInt8 then (b - 'A'.toUInt8 + 10).toNat
  else (b - 'a'.toUInt8 + 10).toNat

/--
Parses a hexadecimal integer (one or more hex digits, up to 16 after any leading zeros, which do not
change the value).
Used for chunk-size lines in chunked transfer encoding.
-/
def hex : Parser Nat := do
  let zeros ← takeWhile (· == '0'.toUInt8)
  let digits ← takeWhileUpTo (Class.hexDigit.accepts ·) (maxChunkSizeDigits + 1)
  if digits.size > maxChunkSizeDigits then
    fail "chunk size too large"
  if zeros.size == 0 && digits.size == 0 then
    fail "expected hex digit"
  return digits.byteArray.foldl (fun n b => n * 16 + hexValue b) 0 digits.start digits.stop

-- Actual parsers

/--
Parses `HTTP-version = HTTP-name "/" DIGIT "." DIGIT`. A higher minor version of HTTP/1 is read as
HTTP/1.1 (RFC 9110 §2.5, §6.2). Returns `none` for a version this library does not know.
-/
def parseHttpVersion : Parser (Option Version) := do
  skipBytes "HTTP/".toUTF8
  let major := (← digit).toNat - 48
  skipByte '.'.toUInt8
  let minor := (← digit).toNat - 48
  return Version.ofNumber? major (if major == 1 then min minor 1 else minor)

/--
Accepts HTTP/1.0 and HTTP/1.1, the versions an HTTP/1 message can have.
-/
def http1Version : Option Version → Parser Version
  | some .v10 => pure .v10
  | some .v11 => pure .v11
  | _ => fail "unsupported HTTP version"

/--
The methods `parseMethod` recognizes, by name, the most common first: every `Method`
(`Method.all_complete`).
-/
def knownMethods : Array (ByteSlice × Method) :=
  Method.all.map fun method => ((toString method).toUTF8.toByteSlice, method)

/-
method         = token

The whole token is read before it is looked up, so a read that ends inside a method name waits for
more input instead of matching a shorter method (`UPDATE` inside `UPDATEREDIRECTREF`), and a
method that only starts with a known one (`GETX`) is not read as it.

A token the server does not recognize gives `none` when the space that ends a method follows it, so
the line still has to parse before it gets 501 (RFC 9110 §9.1). A token longer than any method is
skipped to its end, up to `maxStartLineLength`, for the same reason; only one longer still fails with
`"unrecognized method"` at once (RFC 9112 §3). A token followed by any other byte fails with
`"invalid method"`.
-/
def parseMethod (limits : H1.Config) : Parser (Option Method) := do
  let token ← parseToken maxMethodLength
  match knownMethods.find? fun (name, _) => name.size == token.size && name == token with
  | some (_, method) => return some method
  | none =>
    if token.size == maxMethodLength then
      let rest ← takeWhileUpTo (Class.token.accepts ·) limits.maxStartLineLength
      if rest.size == limits.maxStartLineLength then
        if (← peekWhen? (Class.token.accepts ·)).isSome then fail "unrecognized method"
    let next ← peek!
    if next == ' '.toUInt8 then return none
    else fail "invalid method"

/--
Parses a request-target URI, up to `limits.maxUriLength` bytes.
Fails with `"uri too long"` if the target exceeds the configured limit.

The target ends at the first byte no request-target contains, such as the CR of a line with no
version, so the SP that must follow fails on that byte as soon as it arrives instead of waiting for
an SP (RFC 9112 §3). Only a target byte past the limit makes the target too long.
-/
def parseURI (limits : H1.Config) : Parser ByteArray := do
  let uri ← takeWhileUpTo (Class.target.accepts ·) limits.maxUriLength
  if uri.size == limits.maxUriLength then
    if (← peekWhen? (Class.target.accepts ·)) |>.isSome then
      fail "uri too long"

  return uri.toByteArray

/--
The URI limits for a request-target. `maxUriLength` bounds the whole target, so no component limit
lower than it rejects a target the server accepts as a whole, which RFC 9112 §3 would answer with
`414`, not `400`. The host keeps its own limit, the length of a DNS name.
-/
def requestTargetConfig (limits : H1.Config) : URI.Config :=
  let n := limits.maxUriLength
  { maxSchemeLength := n, maxUserInfoLength := n, maxSegmentLength := n, maxQueryLength := n,
    maxFragmentLength := n, maxPathSegments := n, maxTotalPathLength := n, maxQueryParams := n }

/--
Parses a request line and returns the method, the target and the version, `none` for a version this
library does not know. An unrecognized method fails with `"unrecognized method"` only once the rest of
the line parses, so an invalid request line gets 400 (RFC 9112 §3) whatever its method, and only a
valid one with an unrecognized method gets 501.

request-line = method SP request-target SP HTTP-version
-/
public def parseRequestLineRawVersion (limits : H1.Config) :
    Parser (Method × RequestTarget × Option Version) := do
  skipLeadingRequestEmptyLines limits
  let method? ← parseMethod limits <* sp
  let rawUri ← parseURI limits <* sp
  let uri ← match (Std.Http.URI.Parser.parseRequestTarget (requestTargetConfig limits) <* eof).run rawUri with
  | .ok res => pure res
  | .error res => fail res
  let version ← parseHttpVersion <* crlf
  let some method := method? | fail "unrecognized method"
  return (method, uri, version)

/--
Parses a request line of HTTP/1.0 or HTTP/1.1 and returns a fully-typed `Request.Head`.
-/
public def parseRequestLine (limits : H1.Config) : Parser Request.Head := do
  let (method, uri, version) ← parseRequestLineRawVersion limits
  return ⟨method, ← http1Version version, uri, .empty⟩

/--
Parses a field value with the whitespace around it, `OWS field-value OWS`, and returns the value.
Fails with `"header value too long"` if the value taken up to `limits.maxHeaderValueLength` goes on:
a field-vchar follows once the whitespace after it is consumed. Trailing whitespace does not count
toward the limit, and a value that ends at the limit with an invalid byte is malformed instead.
obs-text need not be UTF-8; it is kept as opaque data, with any invalid sequence replaced.
-/
def parseFieldValue (limits : H1.Config) : Parser String := do
  let limit := limits.maxHeaderValueLength
  let value ← ows limits *> optional (takeWhileUpTo (Class.fieldContent.accepts ·) limit) <* ows limits
  if let some value := value then
    if value.size == limit then
      if (← peekWhen? (Class.fieldContent.accepts ·)) |>.isSome then
        fail "header value too long"
  let value := String.fromUTF8Lossy <| value.map (·.toByteArray) |>.getD .empty
  return value.trimAsciiEnd.toString

/--
Parses a single header field line, or returns `none` when it sees the blank line that terminates the
header section. Fails with `"header name too long"` or `"header value too long"` when the name or
the value goes past its limit.

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
    let name ← parseToken limits.maxHeaderNameLength
    if name.size == limits.maxHeaderNameLength then
      if (← peekWhen? (Class.token.accepts ·)) |>.isSome then
        fail "header name too long"
    skipByte ':'.toUInt8
    let value ← parseFieldValue limits <* crlf
    -- Token bytes are ASCII.
    let some name := String.fromUTF8? name.toByteArray | fail "invalid field name"
    return some (name, value)

/--
Parses the line that continues a field value after an obsolete line folding (`obs-fold = OWS CRLF
RWS`, RFC 9112 §5.2): the leading whitespace, the field content and the terminating CRLF. Returns the
content without the whitespace around it.
-/
public def parseObsFoldContinuation (limits : H1.Config) : Parser String :=
  parseFieldValue limits <* crlf

/--
Parses a quoted-string value, unescaping quoted-pairs, and returns its bytes.

`quoted-string = DQUOTE *( qdtext / quoted-pair ) DQUOTE`, where both `qdtext` and `quoted-pair`
also allow obs-text (`%x80-FF`, RFC 9110 §5.6.4).
-/
def parseQuotedString (maxLength : Nat) : Parser ByteArray := do
  skipByte '"'.toUInt8
  loop .empty 0
where
  loop (buf : ByteArray) (length : Nat) : Parser ByteArray := do
    let b ← any

    if b == '"'.toUInt8 then
      return buf
    else if b == '\\'.toUInt8 then
      let next ← any
      if quotedPairChar (Char.ofUInt8 next) || next ≥ 0x80
        then
          if length + 1 > maxLength then
            fail "quoted-string too long"
          else
            loop (buf.push next) (length + 1)
        else fail s!"invalid quoted-pair byte: {Char.ofUInt8 next |>.quote}"
    else if Class.quoted.accepts b then
      if length + 1 > maxLength then
        fail "quoted-string too long"
      else
        loop (buf.push b) (length + 1)
    else
      fail s!"invalid qdtext byte: {Char.ofUInt8 b |>.quote}"
  termination_by maxLength - length

/--
Parses one chunk extension:
`chunk-ext = *( BWS ";" BWS chunk-ext-name [ BWS "=" BWS chunk-ext-val] )`.

Returns `none` for an extension whose quoted value holds obs-text, which `Chunk.ExtensionValue` cannot
represent: such an extension is ignored, as a recipient ignores any extension it does not
recognize (RFC 9112 §7.1.1).
-/
def parseChunkExt (limits : H1.Config) :
    Parser (Option (Chunk.ExtensionName × Option Chunk.ExtensionValue)) := do
  ows limits *> skipByte ';'.toUInt8 *> ows limits
  -- A token is ASCII, and a valid name and value, so only obs-text in a quoted value gives `none`.
  let name := String.fromUTF8? (← parseToken limits.maxChunkExtNameLength).toByteArray >>=
    Chunk.ExtensionName.ofString?
  -- BWS may follow a name only before "=" (RFC 9112 §7.1.1). After a name without a value,
  -- whitespace must lead to the next ";", so `5;a \r\n` is malformed, as `5 \r\n` is.
  let some () ← optionalUnlessEof (ows limits *> skipByte '='.toUInt8) | return name.map (·, none)
  ows limits
  let value ←
    if (← peekWhen? (· == '"'.toUInt8)).isSome then parseQuotedString limits.maxChunkExtValueLength
    else ByteSlice.toByteArray <$> parseToken limits.maxChunkExtValueLength
  let value := String.fromUTF8? value >>= Chunk.ExtensionValue.ofString?
  return name.bind fun name => value.map (name, some ·)

/--
Parses the size and extensions of a chunk.
-/
public def parseChunkSize (limits : H1.Config) : Parser (Nat × Array (Chunk.ExtensionName × Option Chunk.ExtensionValue)) := do
  let size ← hex
  let ext ← extensions #[] 0
  crlf
  return (size, ext)
where
  /--
  Parses the extensions after the `count` ones already read. One cut off by the end of the input
  fails with `.eof`, so it is parsed again once the rest arrives.
  -/
  extensions (acc : Array (Chunk.ExtensionName × Option Chunk.ExtensionValue)) (count : Nat) :
      Parser (Array (Chunk.ExtensionName × Option Chunk.ExtensionValue)) := do
    let some ext ← optionalUnlessEof (parseChunkExt limits) | return acc
    if h : count + 1 > limits.maxChunkExtensions then
      fail s!"too many chunk extensions: {count + 1} > {limits.maxChunkExtensions}"
    else
      extensions (ext.elim acc acc.push) (count + 1)
  termination_by limits.maxChunkExtensions - count

/--
Whether `name` (compared case-insensitively) is a field a trailer section must not carry (RFC 9112
§6.5). The fields that frame or route a message (`content-length`, `transfer-encoding`, `host`,
`connection`, `te`, `upgrade`, `trailer`) always are: in a trailer section such a field is an
attempt to reframe the message after the fact, which a downstream proxy might act on. With
`strict`, so are the fields that control how the message is processed (`expect`, `authorization`,
`max-forwards`, `cache-control`, `content-encoding`).
-/
def isRejectedTrailerField (strict : Bool) (name : String) : Bool :=
  let n := name.toLower
  n == "content-length" || n == "transfer-encoding" || n == "host" || n == "connection" ||
    n == "te" || n == "upgrade" || n == "trailer" ||
    strict && (n == "expect" || n == "authorization" || n == "max-forwards" ||
      n == "cache-control" || n == "content-encoding")

/--
Parses a trailer header (used after a chunked body), rejecting a field a trailer section must not
carry (`isRejectedTrailerField`). Without `strict`, only framing and routing fields are rejected; the
others are parsed and left for the caller to drop, since RFC 9110 §6.5.1 asks recipients not to
merge them rather than to reject a message that is otherwise complete.
-/
public def parseTrailerHeader (limits : H1.Config) (strict : Bool := true) :
    Parser (Option (String × String)) := do
  let result ← parseSingleHeader limits
  if let some (name, _) := result then
    if isRejectedTrailerField strict name then
      fail s!"forbidden trailer field: {name}"
  return result

/--
Parses a status line and returns the status and the version, `none` for a version this library does
not know. The reason phrase, `HTAB / SP / VCHAR / obs-text` bytes, is checked and discarded: a
client ignores it (RFC 9112 §4), so bytes that are not UTF-8 are replaced rather than rejected.

A code of 000–099 is a well-formed `3DIGIT` that `Status` cannot hold. RFC 9110 §15 asks a client to
process such a response as a 5xx, so it is read as `500 Internal Server Error`.

status-line = HTTP-version SP status-code SP [ reason-phrase ] CRLF
-/
public def parseStatusLineRawVersion (limits : H1.Config) : Parser (Status × Option Version) := do
  let version ← parseHttpVersion <* sp
  let d1 ← digit
  let d2 ← digit
  let d3 ← digit
  let code := (d1.toNat - 48) * 100 + (d2.toNat - 48) * 10 + (d3.toNat - 48)
  -- Servers that send no reason phrase often leave out the space before it too.
  let phrase ← optional <| sp *>
    (String.fromUTF8Lossy ·.toByteArray) <$>
      takeWhileUpTo (Class.fieldContent.accepts ·) limits.maxReasonPhraseLength
  let phrase := phrase.getD ""
  crlf

  if code < 100 then
    return (.internalServerError, version)

  if h : IsValidReasonPhrase phrase then
    if let some status := Status.ofCode (some ⟨phrase, h⟩) code.toUInt16 then
      return (status, version)

  fail "invalid status code"

/--
Parses a status line of HTTP/1.0 or HTTP/1.1 and returns a fully-typed `Response.Head`.
-/
public def parseStatusLine (limits : H1.Config) : Parser Response.Head := do
  let (status, version) ← parseStatusLineRawVersion limits
  return { status, version := ← http1Version version, headers := .empty }

end Std.Http.Protocol.H1
