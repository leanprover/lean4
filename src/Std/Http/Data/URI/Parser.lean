/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
import Init.While
public import Init.Data.String.Basic
public import Std.Internal.Parsec
public import Std.Internal.Parsec.ByteArray
public import Std.Http.Data.URI.Basic
public import Std.Http.Data.URI.Config
import Init.Data.String.Search

public section

/-!
# URI Parser

This module provides parsers for HTTP request targets and HTTP-oriented URIs aligned with RFC 3986.
It handles parsing of schemes, authorities, paths, queries, and fragments.

Notable intentional constraints:
* hosts are limited to IPv4, bracketed IPv6, and DNS-style domain names
* IPvFuture (`v...`) inside `IP-literal` is currently rejected

References:
* https://www.rfc-editor.org/rfc/rfc3986.html
* https://www.rfc-editor.org/rfc/rfc9110.html#name-uri-references
* https://www.rfc-editor.org/rfc/rfc9112.html#section-3.3
-/

namespace Std.Http.URI.Parser

set_option linter.all true

open Internal Char
open Std Internal Parsec ByteArray

@[inline]
private def tryOpt (p : Parser α) : Parser (Option α) :=
  optional (attempt p)

@[inline]
private def peekIs (p : UInt8 → Bool) : Parser Bool := do
  return (← peekWhen? p).isSome

-- scheme = ALPHA *( ALPHA / DIGIT / "+" / "-" / "." )
private def parseScheme (config : URI.Config) : Parser URI.Scheme := do
  if config.maxSchemeLength = 0 then
    fail "scheme length limit is 0 (no scheme allowed)"

  let first : UInt8 ← satisfy isAlphaByte
  let rest ← takeWhileAtMost
    (fun c =>
      isAlphaNum c ∨
      c = '+'.toUInt8 ∨ c = '-'.toUInt8 ∨ c = '.'.toUInt8)
    (config.maxSchemeLength - 1)
  let schemeBytes := ByteArray.empty.push first ++ rest.toByteArray
  let str := String.fromUTF8! schemeBytes |>.toLower

  if h : URI.IsValidScheme str then
    return ⟨str, h⟩
  else
    fail "invalid scheme"

-- port = 1*DIGIT
private def parsePortNumber : Parser UInt16 := do
  let portBytes ← takeWhileAtMost isDigitByte 5

  let portStr := String.fromUTF8! portBytes.toByteArray

  let some portNum := String.toNat? portStr
    | fail s!"invalid port number: {portStr}"

  if portNum > 65535 then
    fail s!"port number too large: {portNum}"

  return portNum.toUInt16

-- userinfo = *( unreserved / pct-encoded / sub-delims / ":" )
private def parseUserInfo (config : URI.Config) : Parser URI.UserInfo := do
  let userBytesName ← takeWhileAtMost
    (fun x =>
      x ≠ ':'.toUInt8 ∧
      (isUserInfoChar x ∨ x = '%'.toUInt8))
    config.maxUserInfoLength

  let some userNameEncoded := URI.EncodedUserInfo.ofByteArray? userBytesName.toByteArray
    | fail "invalid percent encoding in user info"

  let userPassEncoded ← if ← peekIs (· == ':'.toUInt8) then
      skip

      let userBytesPass ← takeWhileAtMost
        (fun x => isUserInfoChar x ∨ x = '%'.toUInt8)
        config.maxUserInfoLength

      let some userPassEncoded := URI.EncodedUserInfo.ofByteArray? userBytesPass.toByteArray
        | fail "invalid percent encoding in user info"

      pure <| some userPassEncoded
    else
      pure none

  return ⟨userNameEncoded, userPassEncoded⟩

-- Parses bracketed IPv6 literals.
-- Note: RFC 3986 also allows IPvFuture inside `IP-literal`; this parser
-- currently rejects IPvFuture.
private def parseIPv6 : Parser Net.IPv6Addr := do
  skipByte '['.toUInt8

  let result ← takeWhile1AtMost
    (fun x => x = ':'.toUInt8 ∨ x = '.'.toUInt8 ∨ isHexDigitByte x)
    256

  skipByte ']'.toUInt8

  let ipv6Str := String.fromUTF8! result.toByteArray
  let some ipv6Addr := Std.Net.IPv6Addr.ofString ipv6Str
    | fail s!"invalid IPv6 address: {ipv6Str}"

  return ipv6Addr

-- IPv4address = dec-octet "." dec-octet "." dec-octet "." dec-octet
private def parseIPv4 : Parser Net.IPv4Addr := do
  let result ← takeWhile1AtMost
    (fun x => x = '.'.toUInt8 ∨ isDigitByte x)
    256

  let ipv4Str := String.fromUTF8! result.toByteArray
  let some ipv4Addr := Std.Net.IPv4Addr.ofString ipv4Str
    | fail s!"invalid IPv4 address: {ipv4Str}"

  return ipv4Addr

-- host = IP-literal / IPv4address / reg-name
-- Note: RFC 1123 allows domain labels to start with digits, so we must try IPv4
-- first and fall back to reg-name parsing if it fails.
private def parseHost (config : URI.Config) : Parser URI.Host := do
  if (← peekWhen? (· == '['.toUInt8)).isSome then
    return .ipv6 (← parseIPv6)
  else
    if (← peekWhen? isDigitByte).isSome then
      if let some ipv4 ← tryOpt parseIPv4 then
        return .ipv4 ipv4

    -- It needs to be a legal DNS label, so it differs from reg-name.
    let some str := String.fromUTF8? (← takeWhile1AtMost
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
  let userInfo ← tryOpt do
    let ui ← parseUserInfo config
    skipByte '@'.toUInt8
    return ui

  let host ← parseHost config

  let port : URI.Port ←
    if ← peekIs (· == ':'.toUInt8) then
      skipByte ':'.toUInt8
      if (← peekWhen? isDigitByte).isSome then
        pure (.value (← parsePortNumber))
      else
        let next ← peek?
        if next.isNone || next.any (fun c => c = '/'.toUInt8 ∨ c = '?'.toUInt8 ∨ c = '#'.toUInt8) then
          pure .empty
        else
          fail "invalid port number"
    else
      pure .omitted

  return { userInfo, host, port }

-- segment = *pchar
private def parseSegment (config : URI.Config) : Parser ByteSlice := do
  takeWhileAtMost (fun c => isPChar c ∨ c = '%'.toUInt8) config.maxSegmentLength

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
  let isPathDelimiter : UInt8 → Bool := fun c => c = '?'.toUInt8 ∨ c = '#'.toUInt8
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
    let some next := (← peek?) | break
    if isPathDelimiter next then
      break

    if ¬(next = '/'.toUInt8 ∨ isPChar next ∨ next = '%'.toUInt8) then
      break

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
      let next ← peek?
      if next.isNone || next.any isPathDelimiter then
        if segments.size >= config.maxPathSegments then
          fail s!"too many path segments (limit: {config.maxPathSegments})"
        segments := segments.push (URI.EncodedString.empty)
    else
      break

  return { segments := segments, absolute := isAbsolute }

-- query = *( pchar / "/" / "?" )
private def parseQuery (config : URI.Config) : Parser URI.Query := do
  let queryBytes ←
    takeWhileAtMost (fun c => isQueryChar c ∨ c = '%'.toUInt8) config.maxQueryLength

  let some queryStr := String.fromUTF8? queryBytes.toByteArray
    | fail "invalid query string"

  if queryStr.isEmpty then
    return URI.Query.empty

  let rawPairs := queryStr.split '&'

  if rawPairs.length > config.maxQueryParams then
    fail s!"too many query parameters (limit: {config.maxQueryParams})"

  let pairs : Option URI.Query := rawPairs.foldM (init := URI.Query.empty) fun acc pair => do
    match pair.split '=' |>.toStringList with
    | [key] =>
      let key ← URI.EncodedQueryParam.fromString? key
      pure (acc.insertEncoded key none)
    | key :: value =>
      let key ← URI.EncodedQueryParam.fromString? key
      let value ← URI.EncodedQueryParam.fromString? (String.intercalate "=" value)
      pure (acc.insertEncoded key (some value))
    | [] => pure acc  -- unreachable: splitOn always returns at least one element

  if let some pairs := pairs then
    return pairs
  else
    fail "invalid query string"

--  fragment = *( pchar / "/" / "?" )
private def parseFragment (config : URI.Config) : Parser URI.EncodedFragment := do
  let fragmentBytes ←
    takeWhileAtMost (fun c => isFragmentChar c ∨ c = '%'.toUInt8) config.maxFragmentLength

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
def parseURI (config : URI.Config := {}) : Parser URI := do
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
def parseRequestTarget (config : URI.Config := {}) : Parser RequestTarget :=
  asterisk <|> origin <|> absoluteHttp <|> authority <|> absolute
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

  absoluteFromScheme (scheme : URI.Scheme) : Parser RequestTarget := do
    skipByte ':'.toUInt8
    let (auth, path) ← parseHierPart config
    let query ← optional (skipByteChar '?' *> parseQuery config)
    let query := query.getD URI.Query.empty

    return .absoluteForm { path, scheme, authority := auth, query, fragment := none }

  -- Prefer absolute-form for explicit HTTP(S) scheme targets with a path or authority.
  -- This avoids misclassifying `http://host/path` as authority-form while still
  -- letting `http:80` fall through to authority-form parsing.
  absoluteHttp : Parser RequestTarget := attempt do
    let scheme ← parseScheme config
    if scheme.val = "http" || scheme.val = "https" then
      skipByte ':'.toUInt8
      if ← peekIs (· == '/'.toUInt8) then
        let (authority, path) ← parseHierPart config
        let query ← optional (skipByteChar '?' *> parseQuery config)
        let query := query.getD .empty
        return .absoluteForm { scheme, path, authority, query, fragment := none }
      else
        fail "not http absolute uri with path"
    else
      fail "not http absolute uri"

  -- absolute-URI  = scheme ":" hier-part [ "?" query ]
  absolute : Parser RequestTarget := attempt do
    let scheme ← parseScheme config
    absoluteFromScheme scheme

  -- authority-form = host ":" port
  authority : Parser RequestTarget := attempt do
    let host ← parseHost config
    skipByteChar ':'
    let port ← parsePortNumber
    return .authorityForm { host, port := .value port }

/--
Parses an HTTP `Host` header value.
-/
def parseHostHeader (config : URI.Config := {}) : Parser (URI.Host × URI.Port) := do
  let host ← parseHost config

  let port : URI.Port ←
    if ← peekIs (· == ':'.toUInt8) then
      skipByte ':'.toUInt8
      if (← peekWhen? isDigitByte).isSome then
        pure (.value (← parsePortNumber))
      else
        let next ← peek?
        if next.isNone then
          pure .empty
        else
          fail "invalid host header port"
    else
      pure .omitted

  if ¬(← isEof) then
    fail "invalid host header"

  return (host, port)

end Std.Http.URI.Parser
