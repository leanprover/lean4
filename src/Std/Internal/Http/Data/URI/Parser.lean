/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Init.Data.String
public import Std.Internal.Parsec
public import Std.Internal.Parsec.ByteArray
public import Std.Internal.Http.Data.URI.Basic

public section

namespace Std.Http.Parser

set_option linter.all true

open Std Internal Parsec ByteArray

@[inline]
private def isDigit (c : UInt8) : Bool :=
  c >= '0'.toUInt8 ∧ c <= '9'.toUInt8

@[inline]
private def isHexDigit (c : UInt8) : Bool :=
  isDigit c ∨ (c >= 'A'.toUInt8 ∧ c <= 'F'.toUInt8) ∨ (c >= 'a'.toUInt8 ∧ c <= 'f'.toUInt8)

@[inline]
private def isAlpha (c : UInt8) : Bool :=
  (c >= 'A'.toUInt8 ∧ c <= 'Z'.toUInt8) ∨ (c >= 'a'.toUInt8 ∧ c <= 'z'.toUInt8)

@[inline]
private def isAlphaNum (c : UInt8) : Bool :=
  isAlpha c ∨ isDigit c

@[inline]
private def isUnreserved (c : UInt8) : Bool :=
  isAlphaNum c ∨ c = '-'.toUInt8 ∨ c = '.'.toUInt8 ∨ c = '_'.toUInt8 ∨ c = '~'.toUInt8

@[inline]
private def isSubDelims (c : UInt8) : Bool :=
  c = '!'.toUInt8 ∨ c = '$'.toUInt8 ∨ c = '&'.toUInt8 ∨ c = '\''.toUInt8 ∨
  c = '('.toUInt8 ∨ c = ')'.toUInt8 ∨ c = '*'.toUInt8 ∨ c = '+'.toUInt8 ∨
  c = ','.toUInt8 ∨ c = ';'.toUInt8 ∨ c = '='.toUInt8

@[inline]
private def isGenDelims (c : UInt8) : Bool :=
  c = ':'.toUInt8 ∨ c = '/'.toUInt8 ∨ c = '?'.toUInt8 ∨ c = '#'.toUInt8 ∨
  c = '['.toUInt8 ∨ c = ']'.toUInt8 ∨ c = '@'.toUInt8

@[inline]
private def isReserved (c : UInt8) : Bool :=
  isGenDelims c ∨ isSubDelims c

@[inline]
private def isPChar (c : UInt8) : Bool :=
  isUnreserved c ∨ isSubDelims c ∨ c = ':'.toUInt8 ∨ c = '@'.toUInt8 ∨ c = '%'.toUInt8

@[inline]
private def isRegNameChar (c : UInt8) : Bool :=
  isUnreserved c ∨ isSubDelims c ∨ c = '%'.toUInt8

@[inline]
private def isSchemeChar (c : UInt8) : Bool :=
  isAlphaNum c ∨ c = '+'.toUInt8 ∨ c = '-'.toUInt8 ∨ c = '.'.toUInt8

@[inline]
private def isQueryChar (c : UInt8) : Bool :=
  isPChar c ∨ c = '/'.toUInt8 ∨ c = '?'.toUInt8

@[inline]
private def isFragmentChar (c : UInt8) : Bool :=
  isPChar c ∨ c = '/'.toUInt8 ∨ c = '?'.toUInt8

@[inline]
private def isUserInfoChar (c : UInt8) : Bool :=
  isUnreserved c ∨ isSubDelims c ∨ c = '%'.toUInt8 ∨ c = ':'.toUInt8

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

private def hexToByte? (digit : UInt8) : Option UInt8 :=
  if digit ≥ '0'.toUInt8 ∧ digit ≤ '9'.toUInt8 then some (digit - '0'.toUInt8)
  else if digit ≥ 'A'.toUInt8 ∧ digit ≤ 'F'.toUInt8 then some (digit - 'A'.toUInt8 + 10)
  else if digit ≥ 'a'.toUInt8 ∧ digit ≤ 'f'.toUInt8 then some (digit - 'a'.toUInt8 + 10)
  else none

private def parsePctEncoded : Parser UInt8 := do
  skipByte '%'.toUInt8
  let hi ← hexToByte <$> satisfy isHexDigit
  let lo ← hexToByte <$> satisfy isHexDigit
  return (hi <<< 4) ||| lo

/--
Decode a percent encoded byte array to an extended ascii string.
-/
public partial def percentDecode (ba : ByteArray) : Except String String := do
  let rec loop (i : Nat) (acc : ByteArray) : Except String ByteArray :=
    if i ≥ ba.size then
      .ok acc
    else
      let c := ba.get! i
      if c = '%'.toUInt8 then
        if i + 2 ≥ ba.size then
          Except.error "invalid percent encoding"
        else
          match hexToByte? (ba.get! (i+1)), hexToByte? (ba.get! (i+2)) with
          | some hi, some lo => loop (i + 3) (acc.push ((hi <<< 4) ||| lo))
          | _, _ => .error "cannot get values"
      else
        loop (i + 1) (acc.push c)

  let result ← loop 0 .empty
  match String.fromUTF8? result with
  | some res => .ok res
  | none => Except.error "invalid percent encoding"

-- scheme = ALPHA *( ALPHA / DIGIT / "+" / "-" / "." )
private def parseScheme : Parser URI.Scheme := do
  let schemeBytes ← takeWhileUpTo1 isSchemeChar 63
  return String.fromUTF8! schemeBytes.toByteArray

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
private def parseUserInfo : Parser URI.UserInfo := do
  let userBytes ← takeWhileUpTo isUserInfoChar 1024

  let .ok userStr := percentDecode userBytes.toByteArray
    | fail "invalid percent encoding in user info"

  return userStr

-- IP-literal = "[" ( IPv6address / IPvFuture  ) "]"
private def parseIPv6 : Parser Net.IPv6Addr := do
  skipByte '['.toUInt8

  let result ← takeWhileUpTo1 (fun x => x = ':'.toUInt8 ∨ isHexDigit x) 256

  skipByte ']'.toUInt8

  let ipv6Str := String.fromUTF8! result.toByteArray
  let some ipv6Addr := Std.Net.IPv6Addr.ofString ipv6Str
    | fail s!"invalid IPv6 address: {ipv6Str}"

  return  ipv6Addr

-- IPv4address = dec-octet "." dec-octet "." dec-octet "." dec-octet
private def parseIPv4 : Parser Net.IPv4Addr := do
  let result ← takeWhileUpTo1 (fun x => x = '.'.toUInt8 ∨ isDigit x) 256

  let ipv4Str := String.fromUTF8! result.toByteArray
  let some ipv4Str := Std.Net.IPv4Addr.ofString ipv4Str
    | fail s!"invalid IPv4 address: {ipv4Str}"

  return ipv4Str

-- host = IP-literal / IPv4address / reg-name
private def parseHost : Parser URI.Host := do
  if (← peekWhen? (· == '['.toUInt8)).isSome then
    return .ipv6 (← parseIPv6)
  else if (← peekWhen? isDigit).isSome then
    return .ipv4 (← parseIPv4)
  else
    let isHostName x := isUnreserved x ∨ x = '%'.toUInt8 ∨ isSubDelims x
    let str ← ofExcept <| percentDecode (← takeWhileUpTo1 isHostName 1024).toByteArray
    return .name str

-- authority = [ userinfo "@" ] host [ ":" port ]
private def parseAuthority : Parser URI.Authority := do
  let userinfo ← tryOpt do
    let ui ← parseUserInfo
    skipByte '@'.toUInt8
    return ui

  let host ← parseHost

  let port ← optional do
    skipByte ':'.toUInt8
    parsePortNumber

  return { userInfo := userinfo, host := host, port := port }

-- segment = *pchar
private def parseSegment : Parser ByteSlice := do
  takeWhileUpTo isPChar 256

/--
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

private def parsePath (forceAbsolute : Bool) : Parser URI.Path := do
  let mut isAbsolute := false
  let mut segments : Array String := #[]

  -- Check if path is absolute
  if ← peekIs (· == '/'.toUInt8) then
    isAbsolute := true
    skip
    if ← peekIs (· == '/'.toUInt8) then
      fail "it's a scheme starter"
  else if forceAbsolute then
    fail "require '/' in path"
  else
    pure ()
  -- Parse segments
  while true do
    let segmentBytes ← parseSegment

    let .ok segmentStr := percentDecode segmentBytes.toByteArray
      | fail "invalid percent encoding in path segment"

    segments := segments.push segmentStr

    if (← peek?).any (· == '/'.toUInt8) then
      skip
    else
      break

  return { segments := segments, absolute := isAbsolute }


-- query = *( pchar / "/" / "?" )
private def parseQuery : Parser URI.Query := do
  let queryBytes ← takeWhileUpTo isQueryChar 1024
  let queryStr := String.fromUTF8! queryBytes.toByteArray

  let pairs ← queryStr.splitOn "&" |>.mapM fun pair => do
    match pair.splitOn "=" with
    | [key] =>
      let .ok decodedKey := percentDecode key.toUTF8
        | fail "invalid percent encoding in query key"
      pure (decodedKey, none)
    | key :: value =>
      let .ok decodedKey := percentDecode key.toUTF8
        | fail "invalid percent encoding in query key"
      let .ok decodedValue := percentDecode (String.intercalate "=" value).toUTF8
        | fail "invalid percent encoding in query value"
      pure (decodedKey, some decodedValue)
    | [] => pure ("", none)

  return pairs.toArray

--  fragment = *( pchar / "/" / "?" )
private def parseFragment : Parser String := do
  let fragmentBytes ← takeWhileUpTo isFragmentChar 1024

  let .ok fragmentStr := percentDecode fragmentBytes.toByteArray
    | fail "invalid percent encoding in fragment"

  return fragmentStr

/--
Parses a request target with combined parsing and validation.
-/
public def parseRequestTarget : Parser RequestTarget := do

  -- The asterisk form
  if (← tryOpt (skipByte '*'.toUInt8)).isSome then
    return .asteriskForm

  -- origin-form = absolute-path [ "?" query ]
  -- absolute-path = 1*( "/" segment )
  if ← peekIs (· == '/'.toUInt8) then
    let path ← parsePath false
    let query ← optional (skipByte '?'.toUInt8 *> parseQuery)
    let frag ← optional (skipByte '#'.toUInt8 *> parseFragment)
    return .originForm path query frag

  let authorityForm ← tryOpt do
    let host ← parseHost
    skipByteChar ':'
    let port ← parsePortNumber
    return RequestTarget.authorityForm { host, port := some port }

  -- absolute-URI  = scheme ":" hier-part [ "?" query ]
  let scheme ← tryOpt do
    let scheme ← parseScheme
    skipByte ':'.toUInt8
    return scheme

  if let some authorityForm := authorityForm then
    return authorityForm

  -- absolute-URI  = scheme ":" hier-part [ "?" query ]
  if let some scheme := scheme then
    -- hier-part = "//" authority path-abempty
    let authority ← optional (skipString "//" *> parseAuthority)
    let path ← parsePath true
    let query ← optional (skipByteChar '?' *> parseQuery)
    let fragment ← optional (skipByteChar '#' *> parseFragment)
    return .absoluteForm { path, scheme, authority, query, fragment }

  fail "invalid request target"

end Std.Http.Parser
