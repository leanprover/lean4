/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
import Init.While
public import Init.Data.String
public import Std.Internal.Parsec
public import Std.Internal.Parsec.ByteArray
public import Std.Internal.Http.Data.URI.Basic
public import Std.Internal.Http.Data.URI.Config

public section

/-!
# URI Parser

This module provides parsers for URIs and request targets according to RFC 3986.
It handles parsing of schemes, authorities, paths, queries, and fragments.
-/

namespace Std.Http.URI.Parser

open Internal Char

set_option linter.all true

open Std Internal Parsec ByteArray

@[inline]
private def tryOpt (p : Parser α) : Parser (Option α) :=
  optional (attempt p)

@[inline]
private def ofExcept (p : Except String α) : Parser α :=
  match p with
  | .ok res => pure res
  | .error err => fail err

@[inline]
private def peekIs (p : UInt8 → Bool) : Parser Bool := do
  return (← peekWhen? p).isSome

private def hexToByte (digit : UInt8) : UInt8 :=
  if digit <= '9'.toUInt8 then digit - '0'.toUInt8
  else if digit <= 'F'.toUInt8 then digit - 'A'.toUInt8 + 10
  else digit - 'a'.toUInt8 + 10

private def parsePctEncoded : Parser UInt8 := do
  skipByte '%'.toUInt8
  let hi ← hexToByte <$> satisfy isHexDigit
  let lo ← hexToByte <$> satisfy isHexDigit
  return (hi <<< 4) ||| lo

-- scheme = ALPHA *( ALPHA / DIGIT / "+" / "-" / "." )
private def parseScheme (config : URI.Config) : Parser URI.Scheme := do
  let first ← takeWhileUpTo1 isAlpha 1
  let rest ← takeWhileUpTo
    (fun c =>
      isAlphaNum c ∨
      c = '+'.toUInt8 ∨ c = '-'.toUInt8 ∨ c = '.'.toUInt8)
    (config.maxSchemeLength - 1)
  let schemeBytes := first.toByteArray ++ rest.toByteArray
  let str := String.fromUTF8! schemeBytes |>.toLower

  if h: str.toList.all isValidSchemeChar ∧ ¬str.isEmpty then
    return ⟨str, ⟨.isLowerCase_toLower, h⟩⟩
  else
    fail "invalid scheme"

-- port = *DIGIT
private def parsePortNumber : Parser UInt16 := do
  let portBytes ← takeWhileUpTo isDigit 5
  if portBytes.size = 0 then fail "empty port number"
  let portStr := String.fromUTF8! portBytes.toByteArray

  let some portNum := String.toNat? portStr
    | fail s!"invalid port number: {portStr}"

  if portNum > 65535 then
    fail s!"port number too large: {portNum}"

  return portNum.toUInt16

-- userinfo = *( unreserved / pct-encoded / sub-delims / ":" )
private def parseUserInfo (config : URI.Config) : Parser URI.UserInfo := do
  let userBytesName ← takeWhileUpTo
    (fun x =>
      x ≠ ':'.toUInt8 ∧
      (isUserInfoChar x ∨ x = '%'.toUInt8))
    config.maxUserInfoLength

  let some userName := URI.EncodedUserInfo.ofByteArray? userBytesName.toByteArray
    | fail "invalid percent encoding in user info"

  let userPass ← if ← peekIs (· == ':'.toUInt8) then
      skip

      let userBytesPass ← takeWhileUpTo
        (fun x => isUserInfoChar x ∨ x = '%'.toUInt8)
        config.maxUserInfoLength

      let some userStrPass := URI.EncodedUserInfo.ofByteArray? userBytesPass.toByteArray >>= URI.EncodedUserInfo.decode
        | fail "invalid percent encoding in user info"

      pure <| some userStrPass
    else
      pure none

  let some userName := userName.decode
    | fail "invalid username"

  return ⟨userName, userPass⟩

-- IP-literal = "[" ( IPv6address / IPvFuture  ) "]"
private def parseIPv6 : Parser Net.IPv6Addr := do
  skipByte '['.toUInt8

  let result ← takeWhileUpTo1
    (fun x => x = ':'.toUInt8 ∨ isHexDigit x)
    256

  skipByte ']'.toUInt8

  let ipv6Str := String.fromUTF8! result.toByteArray
  let some ipv6Addr := Std.Net.IPv6Addr.ofString ipv6Str
    | fail s!"invalid IPv6 address: {ipv6Str}"

  return  ipv6Addr

-- IPv4address = dec-octet "." dec-octet "." dec-octet "." dec-octet
private def parseIPv4 : Parser Net.IPv4Addr := do
  let result ← takeWhileUpTo1
    (fun x => x = '.'.toUInt8 ∨ isDigit x)
    256

  let ipv4Str := String.fromUTF8! result.toByteArray
  let some ipv4Str := Std.Net.IPv4Addr.ofString ipv4Str
    | fail s!"invalid IPv4 address: {ipv4Str}"

  return ipv4Str

-- host = IP-literal / IPv4address / reg-name
-- Note: RFC 1123 allows domain labels to start with digits, so we must try IPv4
-- first and fall back to reg-name parsing if it fails.
private def parseHost (config : URI.Config) : Parser URI.Host := do
  if (← peekWhen? (· == '['.toUInt8)).isSome then
    return .ipv6 (← parseIPv6)
  else
    if (← peekWhen? Internal.Char.isDigit).isSome then
      if let some ipv4 ← tryOpt parseIPv4 then
        return .ipv4 ipv4

    -- It needs to be a legal DNS label, so it differs from reg-name.
    let some str := String.fromUTF8? (← takeWhileUpTo1
      (fun x => isAlphaNum x ∨ x = '-'.toUInt8 ∨ x = '.'.toUInt8)
      config.maxHostLength).toByteArray
      | fail s!"invalid host"

    let lower := str.toLower
    if h : URI.IsValidDomainName lower ∧ ¬lower.isEmpty then
      return .name ⟨lower, .isLowerCase_toLower, h⟩
    else
      fail s!"invalid domain name: {str}"

-- authority = [ userinfo "@" ] host [ ":" port ]
private def parseAuthority (config : URI.Config) : Parser URI.Authority := do
  let userinfo ← tryOpt do
    let ui ← parseUserInfo config
    skipByte '@'.toUInt8
    return ui

  let host ← parseHost config

  let port ← optional do
    skipByte ':'.toUInt8
    parsePortNumber

  return { userInfo := userinfo, host := host, port := port }

-- segment = *pchar
private def parseSegment (config : URI.Config) : Parser ByteSlice := do
  takeWhileUpTo (fun c => isPChar c ∨ c = '%'.toUInt8) config.maxSegmentLength

/-
path = path-abempty ; begins with "/" or is empty
  / path-absolute   ; begins with "/" but not "//"
  / path-noscheme   ; begins with a non-colon segment
  / path-rootless   ; begins with a segment
  / path-empty      ; zero characters

path-abempty  = *( "/" segment )
path-absolute = "/" [ segment-nz *( "/" segment ) ]
path-noscheme = segment-nz-nc *( "/" segment )
path-rootless = segment-nz *( "/" segment )
path-empty    = 0<pchar>
-/

/--
Parses a URI path with combined parsing and validation.
-/
def parsePath (config : URI.Config) (forceAbsolute : Bool) (allowEmpty : Bool) : Parser URI.Path := do
  let mut isAbsolute := false
  let mut segments : Array _ := #[]
  let mut totalLength := 0

  let isSegmentOrSlash ←
    peekIs (fun c => isPChar c ∨ c = '%'.toUInt8 ∨ c = '/'.toUInt8)

  if ¬allowEmpty ∧ ((← isEof) ∨ ¬isSegmentOrSlash) then
    fail "need a path"

  -- Check if path is absolute
  if ← peekIs (· == '/'.toUInt8) then
    isAbsolute := true
    totalLength := totalLength + 1
    skip
  else if forceAbsolute then
    if allowEmpty ∧ ((← isEof) ∨ ¬isSegmentOrSlash) then
      return { segments := segments, absolute := isAbsolute }
    else
      fail "require '/' in path"
  else
    pure ()

  -- Parse segments
  while (← peek?).isSome do
    if segments.size >= config.maxPathSegments then
      fail s!"too many path segments (limit: {config.maxPathSegments})"

    let segmentBytes ← parseSegment config
    let some segmentStr := URI.EncodedSegment.ofByteArray? segmentBytes.toByteArray
      | fail "invalid percent encoding in path segment"

    totalLength := totalLength + segmentBytes.size
    if totalLength > config.maxTotalPathLength then
      fail s!"path too long (limit: {config.maxTotalPathLength} bytes)"

    segments := segments.push segmentStr

    if (← peek?).any (· == '/'.toUInt8) then
      totalLength := totalLength + 1
      if totalLength > config.maxTotalPathLength then
        fail s!"path too long (limit: {config.maxTotalPathLength} bytes)"
      skip
      -- If path ends with '/', add empty segment
      if (← peek?).isNone then
        segments := segments.push (URI.EncodedString.empty)
    else
      break

  return { segments := segments, absolute := isAbsolute }

-- query = *( pchar / "/" / "?" )
private def parseQuery (config : URI.Config) : Parser URI.Query := do
  let queryBytes ←
    takeWhileUpTo (fun c => isQueryChar c ∨ c = '%'.toUInt8) config.maxQueryLength

  let some queryStr := String.fromUTF8? queryBytes.toByteArray
    | fail "invalid query string"

  let rawPairs := queryStr.splitOn "&"

  if rawPairs.length > config.maxQueryParams then
    fail s!"too many query parameters (limit: {config.maxQueryParams})"

  let pairs : Option URI.Query := rawPairs.foldlM (init := URI.Query.empty) fun acc pair => do
    match pair.splitOn "=" with
    | [key] =>
      let key ← URI.EncodedQueryParam.fromString? key
      pure (acc.insertEncoded key none)
    | key :: value =>
      let key ← URI.EncodedQueryParam.fromString? key
      let value ← URI.EncodedQueryParam.fromString? (String.intercalate "=" value)
      pure (acc.insertEncoded key (some value))
    | [] => pure acc

  if let some pairs := pairs then
    return pairs
  else
    fail "invalid query string"

--  fragment = *( pchar / "/" / "?" )
private def parseFragment (config : URI.Config) : Parser URI.EncodedFragment := do
  let fragmentBytes ←
    takeWhileUpTo (fun c => isFragmentChar c ∨ c = '%'.toUInt8) config.maxFragmentLength

  let some fragmentStr := URI.EncodedFragment.ofByteArray? fragmentBytes.toByteArray
    | fail "invalid percent encoding in fragment"

  return fragmentStr

private def parseHierPart (config : URI.Config) : Parser (Option URI.Authority × URI.Path) := do
  -- Check for "//" authority path-abempty
  if (← tryOpt (skipString "//")).isSome then
    let authority ← parseAuthority config
    let path ← parsePath config true true  -- path-abempty (must start with "/" or be empty)
    return (some authority, path)
  else
    -- path-absolute / path-rootless / path-empty
    let path ← parsePath config false true
    return (none, path)

/--
Parses a URI (Uniform Resource Identifier).

URI = scheme ":" hier-part [ "?" query ] [ "#" fragment ]
hier-part = "//" authority path-abempty / path-absolute / path-rootless / path-empty
-/
public def parseURI (config : URI.Config := {}) : Parser URI := do
  let scheme ← parseScheme config
  skipByte ':'.toUInt8

  let (authority, path) ← parseHierPart config

  let query ← optional (skipByteChar '?' *> parseQuery config)
  let query := query.getD .empty

  let fragment ← optional do
    let some result := (← (skipByteChar '#' *> parseFragment config)) |>.decode
      | fail "invalid fragment parse encoding"
    return result

  return { scheme, authority, path, query, fragment }

/--
Parses a request target with combined parsing and validation.
-/
public def parseRequestTarget (config : URI.Config := {}) : Parser RequestTarget :=
  asterisk <|> origin <|> authority <|> absolute
where
  -- The asterisk form
  asterisk : Parser RequestTarget := do
    skipByte '*'.toUInt8
    return .asteriskForm

  -- origin-form = absolute-path [ "?" query ]
  -- absolute-path = 1*( "/" segment )
  origin : Parser RequestTarget := attempt do
    if ← peekIs (· == '/'.toUInt8) then
      let path ← parsePath config true true
      let query ← optional (skipByte '?'.toUInt8 *> parseQuery config)

      return .originForm path query
    else
      fail "not origin"

  -- absolute-URI  = scheme ":" hier-part [ "?" query ]
  absolute : Parser RequestTarget := attempt do
    let scheme ← parseScheme config
    skipByte ':'.toUInt8
    let (auth, path) ← parseHierPart config
    let query ← optional (skipByteChar '?' *> parseQuery config)
    let query := query.getD URI.Query.empty

    return .absoluteForm { path, scheme, authority := auth, query, fragment := none } (by simp)

  -- authority-form = host ":" port
  authority : Parser RequestTarget := attempt do
    let host ← parseHost config
    skipByteChar ':'
    let port ← parsePortNumber
    return .authorityForm { host, port := some port }

/--
Parses an HTTP `Host` header value.
-/
public def parseHostHeader (config : URI.Config := {}) : Parser (URI.Host × Option UInt16) := do
  let host ← parseHost config

  let port ← optional do
    skipByte ':'.toUInt8
    parsePortNumber

  if ¬(← isEof) then
    fail "invalid host header"

  return (host, port)

end Std.Http.URI.Parser
