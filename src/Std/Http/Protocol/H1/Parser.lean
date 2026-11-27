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
import Init.Data.String.Lossy

/-!
This module defines parsers for HTTP/1.1 request and response lines, headers, and body framing. The
reference used is https://httpwg.org/specs/rfc9112.html.
-/

namespace Std.Http.Protocol.H1

open Std Std.Internal Parsec ByteArray Internal.Char

set_option linter.all true

/--
Checks if a byte may appear inside a field value.

Allows `field-content`: `HTAB / SP / VCHAR / obs-text`.
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
Repeatedly applies `parser` until it returns `none` or the `maxCount` limit is
exceeded. Returns the collected results as an array.

An item cut off by the end of the input fails with `.eof` instead of ending the list, so it is
re-parsed once the rest arrives.
-/
def manyItems {α : Type} (parser : Parser (Option α)) (maxCount : Nat) : Parser (Array α) :=
  go #[]
where
  go (acc : Array α) : Parser (Array α) := do
    let step ← optionalUnlessEof do
      match ← parser with
      | none => fail "end of items"
      | some x => return x

    match step with
    | none =>
      return acc
    | some x =>
      if acc.size + 1 > maxCount then
        fail s!"too many items: {acc.size + 1} > {maxCount}"
      else
        go (acc.push x)
  termination_by maxCount - acc.size
  decreasing_by simp only [Array.size_push]; omega


/--
Lifts an `Option` into the parser monad, failing with a generic message if the value is `none`.
-/
def liftOption (x : Option α) : Parser α :=
  if let some res := x then
    return res
  else
    fail "expected value but got none"

/--
End of the run of bytes of `a` from `i` that satisfy `p`, stopping at `stop`.
-/
@[specialize]
def scanUSize (p : UInt8 → Bool) (a : ByteArray) (i stop : USize) (hs : stop.toNat ≤ a.size) :
    USize :=
  if h : i < stop then
    have : i.toNat < stop.toNat := h
    if p (a.uget i (by omega)) then scanUSize p a (i + 1) stop hs else i
  else
    i
termination_by stop.toNat - i.toNat
decreasing_by
  have : i.toNat < stop.toNat := h
  have : (i + 1).toNat = i.toNat + 1 := by
    have hs := stop.toNat_lt_size
    rw [USize.size_eq_two_pow] at hs
    rw [USize.toNat_add, USize.toNat_one]; exact Nat.mod_eq_of_lt (by omega)
  omega

/--
End of the run of bytes of `a` from `i` that satisfy `p`, stopping at `stop` or the end of `a`.
-/
@[inline]
def scanUpTo (p : UInt8 → Bool) (a : ByteArray) (i stop : Nat) : Nat :=
  let stop := min stop a.size
  -- A byte array has fewer than `USize.size` bytes, so only `i > stop` takes the other branch.
  if h : i ≤ stop ∧ stop < USize.size then
    (scanUSize p a (USize.ofNatLT i (Nat.lt_of_le_of_lt h.1 h.2)) (USize.ofNatLT stop h.2) (by
      rw [USize.toNat_ofNatLT]; exact Nat.min_le_right _ _)).toNat
  else
    i

/--
`takeWhileUpTo p limit` with `scanUpTo`: the same result, with `p` specialized instead of called
through a closure for every byte.
-/
@[inline]
def takeRunUpTo (p : UInt8 → Bool) (limit : Nat) : Parser ByteSlice := fun it =>
  let a := it.array
  let stop := it.idx + limit
  let j := scanUpTo p a it.idx stop
  if j ≥ a.size && j < stop then .error ⟨a, j⟩ .eof
  else .success ⟨a, j⟩ a[it.idx...j]

/--
`takeWhileUpTo1 p limit` with `scanUpTo`, as `takeRunUpTo` is for `takeWhileUpTo`.
-/
@[inline]
def takeRunUpTo1 (p : UInt8 → Bool) (limit : Nat) : Parser ByteSlice := fun it =>
  let a := it.array
  let stop := it.idx + limit
  let j := scanUpTo p a it.idx stop
  if j ≥ a.size && j < stop then .error ⟨a, j⟩ .eof
  else if j == it.idx then .error it (.other "expected at least one char")
  else .success ⟨a, j⟩ a[it.idx...j]

/--
Parses an HTTP token (RFC 9110 §5.6.2): one or more token characters, up to `limit` bytes.
Fails if the input starts with a non-token character or is empty.
-/
@[inline]
def parseToken (limit : Nat) : Parser ByteSlice :=
  takeRunUpTo1 Internal.Bytes.isTchar limit

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
  discard <| takeRunUpTo isOwsByte limits.maxSpaceSequence

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
The number of significant hex digits a chunk size may have.
-/
public def maxChunkSizeDigits : Nat := 16

/--
Parses a hexadecimal integer (one or more hex digits, up to 16 after any leading zeros, which do not
change the value).
Used for chunk-size lines in chunked transfer encoding.
-/
def hex : Parser Nat := do
  let zeros ← takeWhile (· == '0'.toUInt8)
  if zeros.size > 0 then
    -- A size of only zeros is complete; `go` still needs one digit when nothing came before it.
    if (← peekWhen? isHexDigitByte) |>.isSome then go 0 0 else return 0
  else
    go 0 0
where
  go (acc : Nat) (count : Nat) : Parser Nat := do
    match ← optional (attempt hexDigit) with
    | some d =>
        if count + 1 > maxChunkSizeDigits then
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
  termination_by maxChunkSizeDigits - count

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

/--
The length of method token `parseMethod` reads before it looks it up; longer than every `Method`.
-/
public def maxMethodLength : Nat := 64

/--
The methods `parseMethod` recognizes, every `Method` (`Method.all_complete`), by the length of their
name: entry `n` holds the names of `n` bytes, the most common first.
-/
def methodsByLength : Array (Array (ByteArray × Method)) :=
  Method.all.foldl (init := Array.replicate maxMethodLength #[]) fun table method =>
    let name := (toString method).toUTF8
    table.modify name.size (·.push (name, method))

/--
Whether the bytes of `a` from `start` are `name`.
-/
def bytesAt (a : ByteArray) (start : Nat) (name : ByteArray) (i : Nat := 0) : Bool :=
  if h : i < name.size then
    a[start + i]? == some name[i] && bytesAt a start name (i + 1)
  else
    true
termination_by name.size - i

/--
The method whose name is the `n` bytes of `a` from `start`.
-/
@[inline]
def knownMethod? (a : ByteArray) (start n : Nat) : Option Method :=
  methodsByLength[n]?.bind fun names =>
    (names.find? fun (name, _) => bytesAt a start name).map (·.2)

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
def parseMethod (limits : H1.Config) : Parser (Option Method) := fun it =>
  -- `parseToken maxMethodLength`, looked up where it lies in the input.
  let a := it.array
  let stop := it.idx + maxMethodLength
  let j := scanUpTo Internal.Bytes.isTchar a it.idx stop
  if j ≥ a.size && j < stop then .error ⟨a, j⟩ .eof
  else if j == it.idx then .error it (.other "expected at least one char")
  else
    match knownMethod? a it.idx (j - it.idx) with
    | some method => .success ⟨a, j⟩ (some method)
    | none => unrecognized (j - it.idx == maxMethodLength) ⟨a, j⟩
where
  unrecognized (long : Bool) : Parser (Option Method) := do
    if long then
      let rest ← takeRunUpTo Internal.Bytes.isTchar limits.maxStartLineLength
      if rest.size == limits.maxStartLineLength then
        if (← peekWhen? Internal.Bytes.isTchar).isSome then fail "unrecognized method"
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
def parseURI (limits : H1.Config) : Parser ByteSlice := do
  let uri ← takeRunUpTo isRequestTargetChar limits.maxUriLength
  if uri.size == limits.maxUriLength then
    if (← peekWhen? isRequestTargetChar) |>.isSome then
      fail "uri too long"

  return uri

/--
A byte of an origin-form path: a `pchar`, the `%` of a triplet, or `/`.
-/
@[inline] def isOriginPathByte (c : UInt8) : Bool :=
  isPChar c || c == '%'.toUInt8 || c == '/'.toUInt8

/--
A byte of a query: a query character or the `%` of a triplet.
-/
@[inline] def isQueryByte (c : UInt8) : Bool :=
  isQueryChar c || c == '%'.toUInt8

/--
The origin-form request-target that `URI.Parser.parseRequestTarget` reads from the bytes of `a` from
`start` to `stop`, read without a `String` or a closure per byte: the path split at each `/`, the
query at each `&` and each parameter at its first `=`, every part checked by the constructor the
general parser uses. `none` when the bytes do not start with `/`, or hold a byte outside the path and
query grammars or an invalid `%` triplet; the general parser reads those, and fails on most.
-/
def originForm? (a : ByteArray) (start stop : Nat) : Option RequestTarget := do
  guard (a[start]? == some '/'.toUInt8)
  let pathEnd := scanUpTo isOriginPathByte a (start + 1) stop
  let segments ← if pathEnd == start + 1 then some #[] else segmentsFrom (start + 1) pathEnd #[]
  let path : URI.Path := { segments, absolute := true }
  if pathEnd == stop then
    return .originForm path none
  guard (a[pathEnd]? == some '?'.toUInt8 && scanUpTo isQueryByte a (pathEnd + 1) stop == stop)
  if pathEnd + 1 == stop then
    return .originForm path (some .empty)
  return .originForm path (some (← paramsFrom (pathEnd + 1) stop .empty))
where
  segmentsFrom (i e : Nat) (acc : Array URI.EncodedSegment) : Option (Array URI.EncodedSegment) := do
    let j := scanUpTo (· != '/'.toUInt8) a i e
    let acc := acc.push (← URI.EncodedSegment.ofByteArray? (a.extract i j))
    if h : i ≤ j ∧ j < e then segmentsFrom (j + 1) e acc else return acc
  termination_by e - i
  paramsFrom (i e : Nat) (acc : URI.Query) : Option URI.Query := do
    let j := scanUpTo (· != '&'.toUInt8) a i e
    let eq := scanUpTo (· != '='.toUInt8) a i j
    let key ← URI.EncodedQueryParam.ofByteArray? (a.extract i eq)
    let value ←
      if eq < j then some <$> URI.EncodedQueryParam.ofByteArray? (a.extract (eq + 1) j)
      else pure none
    let acc := acc.insertEncoded key value
    if h : i ≤ j ∧ j < e then paramsFrom (j + 1) e acc else return acc
  termination_by e - i

/--
The URI limits for a request-target. `maxUriLength` bounds the whole target, so no component limit
lower than it rejects a target the server accepts as a whole, which RFC 9112 §3 would answer with
`414`, not `400`. The host keeps its own limit, the length of a DNS name. `maxPathSegments` and
`maxQueryParams` are checked on the parsed target instead (`exceedsElementLimits`).
-/
def requestTargetConfig (limits : H1.Config) : URI.Config :=
  let n := limits.maxUriLength
  { maxSchemeLength := n, maxUserInfoLength := n, maxSegmentLength := n, maxQueryLength := n,
    maxFragmentLength := n, maxPathSegments := n, maxTotalPathLength := n, maxQueryParams := n }

/--
Whether `target` has more path segments or query parameters than `limits.maxPathSegments` and
`limits.maxQueryParams` allow. Empty segments and parameters count, as `URI.Config` counts them.
-/
def exceedsElementLimits (limits : H1.Config) (target : RequestTarget) : Bool :=
  let over (path : URI.Path) (query : Option URI.Query) :=
    limits.maxPathSegments.any (path.segments.size > ·) ||
      limits.maxQueryParams.any (((query.map (·.size)).getD 0) > ·)
  match target with
  | .originForm path query => over path query
  | .absoluteForm uri => over uri.path uri.query
  | .authorityForm _ | .asteriskForm => false

/--
Shared core for request-line parsing: parses `request-target SP HTTP-version CRLF`
and returns the `RequestTarget` together with the raw major/minor version numbers.

Both `parseRequestLine` and `parseRequestLineRawVersion` call this after consuming
the method token, keeping URI validation and version parsing in one place.
-/
def parseRequestLineBody (limits : H1.Config) : Parser (RequestTarget × Nat × Nat) := do
  let rawUri ← parseURI limits <* sp
  let uri ← match originForm? rawUri.byteArray rawUri.start rawUri.stop with
  | some target => pure target
  | none =>
    match (URI.Parser.parseRequestTarget (requestTargetConfig limits) <* eof).run rawUri.toByteArray with
    | .ok res => pure res
    | .error res => fail res
  -- A configured element count is a limit on how much of the target the server parses, as
  -- `maxUriLength` is, so it gets the same 414 (RFC 9110 §15.5.15).
  if exceedsElementLimits limits uri then
    fail "uri too long"
  let versionPair ← parseHttpVersionNumber <* crlf
  return (uri, versionPair)

/--
Parses `method SP request-target SP HTTP-version CRLF`. An unrecognized method fails with
`"unrecognized method"` only once the rest of the line parses, so an invalid request line gets 400
(RFC 9112 §3) whatever its method, and only a valid one with an unrecognized method gets 501.
-/
def parseRequestLineParts (limits : H1.Config) : Parser (Method × RequestTarget × Nat × Nat) := do
  skipLeadingRequestEmptyLines limits
  let method? ← parseMethod limits <* sp
  let (uri, version) ← parseRequestLineBody limits
  let some method := method? | fail "unrecognized method"
  return (method, uri, version)

/--
Parses a request line and returns a fully-typed `Request.Head`. A higher minor version of HTTP/1 is
read as HTTP/1.1 (RFC 9110 §6.2).
`request-line = method SP request-target SP HTTP-version`
-/
public def parseRequestLine (limits : H1.Config) : Parser Request.Head := do
  let (method, uri, major, minor) ← parseRequestLineParts limits
  if major == 1 ∧ minor ≥ 1 then
    return ⟨method, .v11, uri, .empty⟩
  else if major == 1 ∧ minor == 0 then
    return ⟨method, .v10, uri, .empty⟩
  else
    fail "unsupported HTTP version"

/--
Parses a request line and returns the recognized HTTP method and version when available. A higher
minor version of HTTP/1 is read as HTTP/1.1 (RFC 9110 §6.2).

request-line = method SP request-target SP HTTP-version
-/
public def parseRequestLineRawVersion (limits : H1.Config) : Parser (Method × RequestTarget × Option Version) := do
  let (method, uri, major, minor) ← parseRequestLineParts limits
  return (method, uri, Version.ofNumber? major (if major == 1 then min minor 1 else minor))

/--
Fails with `"header value too long"` if a field value taken up to `limits.maxHeaderValueLength` goes
on: a field-vchar follows once the whitespace after it is consumed. Trailing whitespace does not
count toward the limit, and a value that ends at the limit with an invalid byte is malformed instead.
-/
def checkFieldValueLength (limits : H1.Config) (value : Option ByteSlice) : Parser Unit := do
  if let some value := value then
    if value.size == limits.maxHeaderValueLength then
      if (← peekWhen? isFieldVChar) |>.isSome then
        fail "header value too long"

/--
Start of the run of ASCII whitespace (`Char.isWhitespace`) of `a` that ends at `j`, stopping at
`start`.
-/
def trimWhitespaceEnd (a : ByteArray) (start j : Nat) : Nat :=
  if h : start < j ∧ j ≤ a.size then
    if Std.Http.Internal.Bytes.isNotWhitespace a[j - 1] then j
    else trimWhitespaceEnd a start (j - 1)
  else
    j
termination_by j

/--
Reads a field line, or the empty line that ends a header section (`none`):

```
field-line = field-name ":" OWS field-value OWS CRLF
```

The name is read up to `maxHeaderNameLength` bytes and each `OWS` up to `maxSpaceSequence`; a
token byte or whitespace past the limit fails. The value is read up to `maxHeaderValueLength`
bytes; a field-vchar past it fails with `"header value too long"`. Any byte that ends a run early
is left to the next step, so a malformed line fails at its first byte that does not fit, and input
that ends inside the line fails with `.eof`.

`mk` gets the input bytes and the bounds of the name and the value (with any trailing whitespace)
and builds the result; `none` fails the line.
-/
@[inline]
def fieldLineWith (limits : H1.Config) (mk : ByteArray → Nat → Nat → Nat → Nat → Option β) :
    Parser (Option β) := do
  if (← peekWhen? fun c => c == '\r'.toUInt8 || c == '\n'.toUInt8).isSome then
    crlf
    return none
  let name ← takeRunUpTo1 Internal.Bytes.isTchar limits.maxHeaderNameLength
  if name.size == limits.maxHeaderNameLength then
    if (← peekWhen? Internal.Bytes.isTchar).isSome then fail "header name too long"
  skipByte ':'.toUInt8
  ows limits
  let value ← takeRunUpTo isFieldVChar limits.maxHeaderValueLength
  ows limits
  checkFieldValueLength limits (some value)
  crlf
  match mk name.byteArray name.start name.stop value.start value.stop with
  | some res => return some res
  | none => fail "invalid field line"

/--
Parses a single header field line, or returns `none` when it sees the blank line that
terminates the header section.

```
field-line = field-name ":" OWS field-value OWS CRLF
```

Fails with `"header name too long"` or `"header value too long"` when the name or the value goes
past its limit. The name is returned as sent and the value without the whitespace around it;
obs-text need not be UTF-8, so it is kept as opaque data, with any invalid sequence replaced.
-/
public def parseSingleHeader (limits : H1.Config) : Parser (Option (String × String)) :=
  fieldLineWith limits fun a ns ne vs ve => do
    let name ← String.fromUTF8? (a.extract ns ne)
    let value := String.fromUTF8Lossy (a.extract vs ve)
    return (name, value.trimAsciiEnd.toString)

/--
Whether the bytes of `a` from `start` are `lower` with any ASCII letters in either case.
-/
def eqLowerAt (a : ByteArray) (start : Nat) (lower : String) (i : Nat := 0) : Bool :=
  if h : i < lower.utf8ByteSize then
    if h' : start + i < a.size then
      let b := a[start + i]
      let b := if 'A'.toUInt8 ≤ b && b ≤ 'Z'.toUInt8 then b + 32 else b
      b == lower.getUTF8Byte ⟨i⟩ h && eqLowerAt a start lower (i + 1)
    else
      false
  else
    true
termination_by lower.utf8ByteSize - i

def nameAcceptLanguage : Header.Name := .mk "accept-language"
def nameAcceptEncoding : Header.Name := .mk "accept-encoding"
def nameUpgradeInsecureRequests : Header.Name := .mk "upgrade-insecure-requests"
def nameSecFetchDest : Header.Name := .mk "sec-fetch-dest"
def nameSecFetchMode : Header.Name := .mk "sec-fetch-mode"
def nameSecFetchSite : Header.Name := .mk "sec-fetch-site"
def nameSecFetchUser : Header.Name := .mk "sec-fetch-user"
def nameCacheControl : Header.Name := .mk "cache-control"
def namePragma : Header.Name := .mk "pragma"
def nameTe : Header.Name := .mk "te"
def nameUpgrade : Header.Name := .mk "upgrade"
def nameTrailer : Header.Name := .mk "trailer"
def nameEtag : Header.Name := .mk "etag"
def nameVary : Header.Name := .mk "vary"
def nameExpires : Header.Name := .mk "expires"
def nameAcceptRanges : Header.Name := .mk "accept-ranges"
def nameXForwardedFor : Header.Name := .mk "x-forwarded-for"
def namePriority : Header.Name := .mk "priority"
def nameDnt : Header.Name := .mk "dnt"
def nameContentDisposition : Header.Name := .mk "content-disposition"
def nameRange : Header.Name := .mk "range"

/--
The `Header.Name` constant for the token bytes of `a` from `start` to `start + n` when they name a
field a message head most often carries, so reading it allocates nothing.
-/
def knownName? (a : ByteArray) (start n : Nat) : Option Header.Name :=
  let is (name : Header.Name) := eqLowerAt a start name.value
  match n with
  | 2 => if is nameTe then some nameTe else none
  | 3 => if is nameDnt then some nameDnt else none
  | 4 =>
    if is .host then some .host
    else if is .date then some .date
    else if is nameEtag then some nameEtag
    else if is nameVary then some nameVary
    else none
  | 5 => if is nameRange then some nameRange else none
  | 6 =>
    if is .accept then some .accept
    else if is .cookie then some .cookie
    else if is .origin then some .origin
    else if is .server then some .server
    else if is .expect then some .expect
    else if is namePragma then some namePragma
    else none
  | 7 =>
    if is .referer then some .referer
    else if is nameUpgrade then some nameUpgrade
    else if is nameTrailer then some nameTrailer
    else if is nameExpires then some nameExpires
    else none
  | 8 =>
    if is .location then some .location
    else if is namePriority then some namePriority
    else none
  | 10 =>
    if is .userAgent then some .userAgent
    else if is .connection then some .connection
    else if is .setCookie then some .setCookie
    else if is .keepAlive then some .keepAlive
    else none
  | 12 => if is .contentType then some .contentType else none
  | 13 =>
    if is .authorization then some .authorization
    else if is .lastModified then some .lastModified
    else if is .ifNoneMatch then some .ifNoneMatch
    else if is nameCacheControl then some nameCacheControl
    else if is nameAcceptRanges then some nameAcceptRanges
    else none
  | 14 =>
    if is .contentLength then some .contentLength
    else if is nameSecFetchDest then some nameSecFetchDest
    else if is nameSecFetchMode then some nameSecFetchMode
    else if is nameSecFetchSite then some nameSecFetchSite
    else if is nameSecFetchUser then some nameSecFetchUser
    else none
  | 15 =>
    if is nameAcceptLanguage then some nameAcceptLanguage
    else if is nameAcceptEncoding then some nameAcceptEncoding
    else if is nameXForwardedFor then some nameXForwardedFor
    else none
  | 16 =>
    if is .contentEncoding then some .contentEncoding
    else if is .contentLanguage then some .contentLanguage
    else if is .contentLocation then some .contentLocation
    else none
  | 17 =>
    if is .transferEncoding then some .transferEncoding
    else if is .ifModifiedSince then some .ifModifiedSince
    else none
  | 19 =>
    if is .proxyAuthorization then some .proxyAuthorization
    else if is nameContentDisposition then some nameContentDisposition
    else none
  | 25 => if is nameUpgradeInsecureRequests then some nameUpgradeInsecureRequests else none
  | _ => none

/--
The `Header.Name` of the token bytes of `a` from `start` to `stop`: the constant of `knownName?`, or
else a new lowercased name. `Header.Name.ofString?` gives the same name.
-/
def nameOfBytes? (a : ByteArray) (start stop : Nat) : Option Header.Name :=
  let n := stop - start
  match knownName? a start n with
  | some name => some name
  | none => Header.Name.ofAsciiBytes? (a.extract start stop)

/--
The `Header.Value` of the field-value bytes of `a` from `start` to `stop`, without trailing
whitespace: the value `parseSingleHeader` gives, read with `Header.Value.ofString?`.
-/
def valueOfBytes? (a : ByteArray) (start stop : Nat) : Option Header.Value :=
  let stop' := trimWhitespaceEnd a start stop
  if stop' == start then
    some ⟨"", by decide⟩
  else
    match Header.Value.ofAsciiBytes? (a.extract start stop') with
    | some value => some value
    | none =>
      -- Removing ASCII whitespace from the end of valid UTF-8 keeps it valid, and the reverse.
      match String.fromUTF8? (a.extract start stop') with
      | some value => Header.Value.ofString? value
      | none =>
        Header.Value.ofString? (String.fromUTF8Lossy (a.extract start stop)).trimAsciiEnd.toString

/--
Parses a single header field line into a header name and value, or returns `none` when it sees the
blank line that terminates the header section: `parseSingleHeader` followed by
`Header.Name.ofString?` and `Header.Value.ofString?`, which accept every line it reads.
-/
public def parseHeaderField (limits : H1.Config) : Parser (Option (Header.Name × Header.Value)) :=
  fieldLineWith limits fun a ns ne vs ve => do
    return (← nameOfBytes? a ns ne, ← valueOfBytes? a vs ve)

/--
Parses the line that continues a field value after an obsolete line folding (`obs-fold = OWS CRLF
RWS`, RFC 9112 §5.2): the leading whitespace, the field content and the terminating CRLF. Returns the
content without the whitespace around it.
-/
public def parseObsFoldContinuation (limits : H1.Config) : Parser String := do
  let value ← ows limits *> optional (takeRunUpTo isFieldVChar limits.maxHeaderValueLength) <* ows limits
  checkFieldValueLength limits value
  crlf
  let value := String.fromUTF8Lossy <| value.map (·.toByteArray) |>.getD .empty
  return value.trimAscii.toString

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
    else if isQdText b || b ≥ 0x80 then
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
  let name ← liftOption =<< String.fromUTF8? <$> ByteSlice.toByteArray <$> parseToken limits.maxChunkExtNameLength

  let some name := Chunk.ExtensionName.ofString? name
    | fail "invalid extension name"

  -- BWS may follow a name only before "=" (RFC 9112 §7.1.1). After a name without a value,
  -- whitespace must lead to the next ";", so `5;a \r\n` is malformed, as `5 \r\n` is.
  let some () ← optionalUnlessEof (ows limits *> skipByte '='.toUInt8) | return some (name, none)
  ows limits
  if (← peekWhen? (· == '"'.toUInt8)).isSome then
    let bytes ← parseQuotedString limits.maxChunkExtValueLength
    return (String.fromUTF8? bytes >>= Chunk.ExtensionValue.ofString?).map (name, some ·)

  let value ← liftOption =<< (String.fromUTF8? <$> ByteSlice.toByteArray <$> parseToken limits.maxChunkExtValueLength)
  let some value := Chunk.ExtensionValue.ofString? value
    | fail "invalid extension value"

  return some (name, some value)

/--
Parses the size and extensions of a chunk.
-/
public def parseChunkSize (limits : H1.Config) : Parser (Nat × Array (Chunk.ExtensionName × Option Chunk.ExtensionValue)) := do
  let size ← hex
  let ext ← manyItems (some <$> parseChunkExt limits) limits.maxChunkExtensions
  crlf
  return (size, ext.filterMap id)

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
Returns `true` if `name` (compared case-insensitively) frames or routes a message
(`content-length`, `transfer-encoding`, `host`, `connection`, `te`, `upgrade`, `trailer`). In a
trailer section such a field is an attempt to reframe the message after the fact, which a downstream
proxy might act on, so the message is rejected.
-/
def isFramingTrailerField (name : String) : Bool :=
  let n := name.toLower
  n == "content-length" || n == "transfer-encoding" || n == "host" ||
  n == "connection" || n == "te" || n == "upgrade" || n == "trailer"

/--
Returns `true` if `name` (compared case-insensitively) is a field that MUST NOT appear in HTTP/1.1
trailer sections per RFC 9112 §6.5: the framing and routing fields of `isFramingTrailerField`, and
fields that control how the message is processed (`expect`, `authorization`, `max-forwards`,
`cache-control`, `content-encoding`).
-/
def isForbiddenTrailerField (name : String) : Bool :=
  let n := name.toLower
  isFramingTrailerField name || n == "expect" ||
  n == "authorization" || n == "max-forwards" || n == "cache-control" || n == "content-encoding"

/--
Parses a trailer header (used after a chunked body). Framing and routing fields
(`isFramingTrailerField`) are always rejected, to prevent trailer injection attacks where a
downstream proxy might re-interpret them. With `strict`, every field forbidden in trailers is
rejected; without it, the others are parsed and left for the caller to drop, since RFC 9110 §6.5.1
asks recipients not to merge them rather than to reject a message that is otherwise complete.
-/
public def parseTrailerHeader (limits : H1.Config) (strict : Bool := true) :
    Parser (Option (String × String)) := do
  let result ← parseSingleHeader limits
  if let some (name, _) := result then
    if isFramingTrailerField name || (strict && isForbiddenTrailerField name) then
      fail s!"forbidden trailer field: {name}"
  return result

/--
Parses trailer headers after a chunked body and returns them as an array of name-value pairs.

This is exposed for callers that need the trailer values directly (e.g. clients). The
internal protocol machine parses the section one field at a time with `parseTrailerHeader`, and
discards trailer values.
-/
public def parseTrailers (limits : H1.Config) : Parser (Array (String × String)) := do
  let trailers ← manyItems (parseTrailerHeader limits) limits.maxTrailerHeaders
  crlf
  return trailers

/--
Returns `true` if `c` is a valid reason-phrase byte (`HTAB / SP / VCHAR / obs-text`).
-/
@[inline]
def isReasonPhraseByte (c : UInt8) : Bool :=
  fieldContent (Char.ofUInt8 c)

/--
Parses a reason phrase (text after status code).

Allows `HTAB / SP / VCHAR / obs-text` bytes. A client ignores the phrase (RFC 9112 §4), so bytes
that are not UTF-8 are replaced rather than rejected.
-/
def parseReasonPhrase (limits : H1.Config) : Parser String := do
  let bytes ← takeRunUpTo isReasonPhraseByte limits.maxReasonPhraseLength
  return String.fromUTF8Lossy bytes.toByteArray

/--
Parses a status-code (3 decimal digits), the following reason phrase, and the
terminating CRLF; returns a typed `Status`.

A code outside 100–599 is a well-formed `3DIGIT` but not a valid status code. RFC 9110 §15 asks a
client to process such a response as a 5xx, so it is read as `500 Internal Server Error`.
-/
def parseStatusCode (limits : H1.Config) : Parser Status := do
  let d1 ← digit
  let d2 ← digit
  let d3 ← digit
  let code := (d1.toNat - 48) * 100 + (d2.toNat - 48) * 10 + (d3.toNat - 48)
  -- Servers that send no reason phrase often leave out the space before it too.
  let phrase := (← optional (sp *> parseReasonPhrase limits)).getD ""
  crlf

  if code < 100 || code ≥ 600 then
    return .internalServerError

  if h : IsValidReasonPhrase phrase then
    if let some status := Status.ofCode (some ⟨phrase, h⟩) code.toUInt16 then
      return status

  fail "invalid status code"

/--
Parses a status line and returns a fully-typed `Response.Head`.
`status-line = HTTP-version SP status-code SP [ reason-phrase ]`
Accepts only HTTP/1.x, read as HTTP/1.1 for any minor version above 1. For parsing where the version
may be unrecognized and must be mapped to an error event, use `parseStatusLineRawVersion`.
-/
public def parseStatusLine (limits : H1.Config) : Parser Response.Head := do
  let (major, minor) ← parseHttpVersionNumber <* sp
  let status ← parseStatusCode limits
  if major == 1 ∧ minor ≥ 1 then
    return { status, version := .v11, headers := .empty }
  else if major == 1 ∧ minor == 0 then
    return { status, version := .v10, headers := .empty }
  else
    fail "unsupported HTTP version"

/--
Parses a status line and returns the status code plus recognized HTTP version when available.
Consumes and discards the reason phrase.

RFC 9110 §2.5: a response with a higher minor version than HTTP/1.1 (`HTTP/1.2`) is processed as
HTTP/1.1, the highest minor version this client implements.

status-line = HTTP-version SP status-code SP [ reason-phrase ] CRLF
-/
public def parseStatusLineRawVersion (limits : H1.Config) : Parser (Status × Option Version) := do
  let (major, minor) ← parseHttpVersionNumber <* sp
  let status ← parseStatusCode limits
  return (status, Version.ofNumber? major (if major == 1 then min minor 1 else minor))

/-! ## Scanning input before it is parsed -/

/--
Whether the unread input holds nothing but `CR` and `LF` bytes. Scans in place and stops at the
first other byte; `ByteArray.data` would box a copy of the whole buffer.
-/
public def onlyLineEndsLeft (input : ByteArray.Iterator) : Bool :=
  (input.array.findIdx? (fun b => b != '\r'.toUInt8 && b != '\n'.toUInt8) input.idx).isNone

/--
Whether the unread input holds only empty lines a server ignores before a request line, possibly
followed by the `CR` of one more: line ends that the request-line parser reads to their end without
failing. A bare `LF`, or more empty lines than `maxLeadingEmptyLines`, fail the parser, so they get
the answer they get when more input follows.
-/
public def onlyEmptyLinesLeft (config : Config) (input : ByteArray.Iterator) : Bool :=
  onlyLineEndsLeft input && (parseRequestLineRawVersion config input matches .error _ .eof)

/--
The bytes of the empty lines (`CRLF`) at the start of `input`, up to `maxLeadingEmptyLines` of them.
A server ignores them before a request line (RFC 9112 §2.2), so they do not count toward
`maxStartLineLength`.
-/
public def leadingEmptyLineBytes (config : Config) (input : ByteArray.Iterator) : Nat := Id.run do
  let mut n := 0
  for _ in [0:config.maxLeadingEmptyLines] do
    if input.array[input.idx + n]? == some '\r'.toUInt8 &&
        input.array[input.idx + n + 1]? == some '\n'.toUInt8 then
      n := n + 2
    else
      break
  return n

/--
Whether the request line in `input` starts with the method `HEAD`. A client that sent it reads the
response as having no content (RFC 9110 §9.3.2), even when the rest of the line fails to parse.
-/
public def startsWithHead (config : Config) (input : ByteArray.Iterator) : Bool :=
  let s := input.idx + leadingEmptyLineBytes config input
  let b := input.array
  b[s]? == some 'H'.toUInt8 && b[s + 1]? == some 'E'.toUInt8 && b[s + 2]? == some 'A'.toUInt8 &&
    b[s + 3]? == some 'D'.toUInt8 && b[s + 4]? == some ' '.toUInt8

end Std.Http.Protocol.H1
