/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Internal.Parsec
public import Std.Internal.Parsec.ByteArray
public import Std.Internal.Http.Data.URI.Basic

public section

namespace Std
namespace Http
namespace Parser

set_option linter.all true

open Std Internal Parsec ByteArray

private structure UriComponents where
  schema : Option ByteSlice
  userinfo : Option (ByteSlice × Option ByteSlice)
  host : Option ByteSlice
  port : Option ByteSlice
  path : Option ByteArray
  query : Option ByteSlice
  fragment : Option ByteSlice

@[inline]
private def isDigit (c : UInt8) : Bool :=
  c >= '0'.toUInt8 && c <= '9'.toUInt8

@[inline]
private def isHexDigit (c : UInt8) : Bool :=
  isDigit c || (c >= 'A'.toUInt8 && c <= 'F'.toUInt8) || (c >= 'a'.toUInt8 && c <= 'f'.toUInt8)

@[inline]
private def isAlpha (c : UInt8) : Bool :=
  (c >= 'A'.toUInt8 && c <= 'Z'.toUInt8) || (c >= 'a'.toUInt8 && c <= 'z'.toUInt8)

@[inline]
private def isAlphaNum (c : UInt8) : Bool :=
  isAlpha c || isDigit c

@[inline]
private def isUnreserved (c : UInt8) : Bool :=
  isAlphaNum c || c == '-'.toUInt8 || c == '.'.toUInt8 || c == '_'.toUInt8 || c == '~'.toUInt8

@[inline]
private def isSubDelims (c : UInt8) : Bool :=
  c == '!'.toUInt8 || c == '$'.toUInt8 || c == '&'.toUInt8 || c == '\''.toUInt8 ||
  c == '('.toUInt8 || c == ')'.toUInt8 || c == '*'.toUInt8 || c == '+'.toUInt8 ||
  c == ','.toUInt8 || c == ';'.toUInt8 || c == '='.toUInt8

@[inline]
private def isGenDelims (c : UInt8) : Bool :=
  c == ':'.toUInt8 || c == '/'.toUInt8 || c == '?'.toUInt8 || c == '#'.toUInt8 ||
  c == '['.toUInt8 || c == ']'.toUInt8 || c == '@'.toUInt8

@[inline]
private def isReserved (c : UInt8) : Bool :=
  isGenDelims c || isSubDelims c

@[inline]
private def isPChar (c : UInt8) : Bool :=
  isUnreserved c || isSubDelims c || c == ':'.toUInt8 || c == '@'.toUInt8 || c == '%'.toUInt8

@[inline]
private def isRegNameChar (c : UInt8) : Bool :=
  isUnreserved c || isSubDelims c || c == '%'.toUInt8

@[inline]
private def isSchemeChar (c : UInt8) : Bool :=
  isAlphaNum c || c == '+'.toUInt8 || c == '-'.toUInt8 || c == '.'.toUInt8

@[inline]
private def isQueryChar (c : UInt8) : Bool :=
  isPChar c || c == '/'.toUInt8 || c == '?'.toUInt8

@[inline]
private def isFragmentChar (c : UInt8) : Bool :=
  isPChar c || c == '/'.toUInt8 || c == '?'.toUInt8

@[inline]
private def isUserInfoChar (c : UInt8) : Bool :=
  isUnreserved c || isSubDelims c || c == '%'.toUInt8

private def failNone (x : Option α) : Parser α :=
  if let some res := x then
    pure res
  else
    fail "expected value but got none"

private def tryOpt (p : Parser α) : Parser (Option α) := optional (attempt p)

private def hexDigit : Parser UInt8 := do
  let b ← any
  if b ≥ '0'.toUInt8 && b ≤ '9'.toUInt8 then return b - '0'.toUInt8
  else if b ≥ 'A'.toUInt8 && b ≤ 'F'.toUInt8 then return b - 'A'.toUInt8 + 10
  else if b ≥ 'a'.toUInt8 && b ≤ 'f'.toUInt8 then return b - 'a'.toUInt8 + 10
  else fail s!"Invalid hex digit {Char.ofUInt8 b |>.quote}"

-- Abstracted percent-encoding parser that automatically decodes to UInt8
private def parsePctEncoded : Parser UInt8 := do
  skipByte '%'.toUInt8
  let digit1 ← satisfy isHexDigit
  let digit2 ← satisfy isHexDigit
  let hi := if digit1 <= '9'.toUInt8 then digit1 - '0'.toUInt8
            else if digit1 <= 'F'.toUInt8 then digit1 - 'A'.toUInt8 + 10
            else digit1 - 'a'.toUInt8 + 10
  let lo := if digit2 <= '9'.toUInt8 then digit2 - '0'.toUInt8
            else if digit2 <= 'F'.toUInt8 then digit2 - 'A'.toUInt8 + 10
            else digit2 - 'a'.toUInt8 + 10
  return (hi <<< 4) ||| lo

-- Generic function to parse characters with percent-encoding support
private def parseCharWithPctEncoding (isValidChar : UInt8 → Bool) (stopChar : UInt8 → Bool := fun _ => false) : Parser UInt8 := do
  let c? ← peek?
  match c? with
  | none => fail "unexpected end of input"
  | some c =>
    if c == '%'.toUInt8 then
      parsePctEncoded
    else if isValidChar c && !stopChar c then
      skip
      return c
    else
      fail s!"invalid character: {Char.ofUInt8 c |>.quote}"

-- Generic function to parse a sequence of characters with percent-encoding support
private def parseSequenceWithPctEncoding (isValidChar : UInt8 → Bool) (stopChar : UInt8 → Bool := fun _ => false) : Parser ByteArray := do
  let mut result : ByteArray := .empty
  while true do
    let c? ← peek?
    match c? with
    | none => break
    | some c =>
      if stopChar c then break
      else if c == '%'.toUInt8 then
        let decoded ← parsePctEncoded
        result := result.push decoded
      else if isValidChar c then
        skip
        result := result.push c
      else break
  return result

private def parseScheme : Parser ByteSlice := do
  takeWhileUpTo1 isSchemeChar 63

private def parsePort : Parser ByteSlice := do
  takeWhileUpTo isDigit 5

private def parseUserInfo : Parser (ByteSlice × Option ByteSlice) := do
  -- Parse user part
  let userBytes ← parseSequenceWithPctEncoding isUserInfoChar (fun c => c == ':'.toUInt8 || c == '@'.toUInt8)

  let hasPassword ← optional (skipByte ':'.toUInt8)
  if hasPassword.isSome then
    -- Parse password part
    let passBytes ← parseSequenceWithPctEncoding isUserInfoChar (fun c => c == '@'.toUInt8)
    return (userBytes.toByteSlice, some passBytes.toByteSlice)
  else
    return (userBytes.toByteSlice, none)

private def parseHost : Parser ByteSlice := do
  if (← peek?).any (· == '['.toUInt8) then
    let mut result : ByteArray := .empty
    while true do
      let c? ← peek?
      match c? with
      | none => fail "unterminated IP literal"
      | some c =>
        skip
        result := result.push c
        if c == ']'.toUInt8 then break
    return result.toByteSlice
  else
    let hostBytes ← parseSequenceWithPctEncoding isRegNameChar
    return hostBytes.toByteSlice

private def parseAuthority : Parser (Option (ByteSlice × Option ByteSlice) × Option ByteSlice × Option ByteSlice) := do
  let userinfo ← tryOpt do
    let ui ← parseUserInfo
    skipByte '@'.toUInt8
    return ui

  let host ← parseHost
  if host.size == 0 then
    fail "expected host"

  let port ← optional do
    skipByte ':'.toUInt8
    parsePort

  return (userinfo, some host, port)

private def parseSegmentRaw : Parser ByteSlice := do
  takeWhileUpTo (fun c => isPChar c && c != '/'.toUInt8) 4096

private def parsePathSegments : Parser ByteArray := do
  let mut result : ByteArray := .empty
  let mut first := true

  while (← peek?).any (· == '/'.toUInt8) || first do
    if !first then
      skip
      result := result.push '/'.toUInt8
    first := false

    let segment ← parseSegmentRaw
    result := result ++ segment.toByteArray

    if (← peek?).any (fun c => c != '/'.toUInt8) then break

  return result

private def parseQuery : Parser ByteSlice := do
  takeWhileUpTo isQueryChar 4096

private def parseFragment : Parser ByteSlice := do
  let fragmentBytes ← parseSequenceWithPctEncoding isFragmentChar
  return fragmentBytes.toByteSlice

private def parseUri : Parser UriComponents := do
  let mut components : UriComponents := ⟨none, none, none, none, none, none, none⟩

  let schemeResult ← tryOpt do
    let scheme ← parseScheme
    skipByte ':'.toUInt8
    return scheme

  components := { components with schema := schemeResult }

  if (← tryOpt (skipBytes "//".toUTF8)).isSome then
    let (userinfo, host, port) ← parseAuthority
    components := { components with userinfo := userinfo, host := host, port := port }

  let pathResult ← tryOpt parsePathSegments
  components := { components with path := pathResult }

  if (← optional (skipByte '?'.toUInt8)).isSome then
    let queryBytes ← parseQuery
    components := { components with query := some queryBytes }

  if (← optional (skipByte '#'.toUInt8)).isSome then
    let fragmentBytes ← parseFragment
    components := { components with fragment := some fragmentBytes }

  return components

private def hexValue (c : UInt8) : Option UInt8 :=
  if c ≥ '0'.toUInt8 && c ≤ '9'.toUInt8 then some (c - '0'.toUInt8)
  else if c ≥ 'A'.toUInt8 && c ≤ 'F'.toUInt8 then some (c - 'A'.toUInt8 + 10)
  else if c ≥ 'a'.toUInt8 && c ≤ 'f'.toUInt8 then some (c - 'a'.toUInt8 + 10)
  else none

/--
Decode a percent encoded byte array to an extended ascii string.
-/
public partial def percentDecode (ba : ByteArray) : Except String String := do
  let rec loop (i : Nat) (acc : ByteArray) : Except String ByteArray :=
    if i ≥ ba.size then .ok acc
    else
      let c := ba.get! i
      if c = '%'.toUInt8 then
        if i + 2 ≥ ba.size then Except.error "invalid percent encoding"
        else
          match hexValue (ba.get! (i+1)), hexValue (ba.get! (i+2)) with
          | some hi, some lo =>
              loop (i + 3) (acc.push ((hi <<< 4) ||| lo))
          | _, _ => .error "cannot get values"
      else
        loop (i + 1) (acc.push c)

  let result ← loop 0 .empty
  match String.fromUTF8? result with
  | some res => .ok res
  | none => Except.error "invalid percent encoding"



private def parsePortNumber (portBytes : ByteSlice) : Option UInt16 := do
  let portStr := String.fromUTF8! portBytes.toByteArray
  String.toNat? portStr >>= (fun n => if n ≤ 65535 then some n.toUInt16 else none)

private def componentToUserInfo (userBytes : ByteSlice) (passBytes : Option ByteSlice) : Option URI.UserInfo := do
  return { user := some <| String.fromUTF8! userBytes.toByteArray, pass := String.fromUTF8! <$> passBytes.map (·.toByteArray) }

private def componentToHost (hostBytes : ByteSlice) : Except String URI.Host := do
  let hostStr := String.fromUTF8! hostBytes.toByteArray

  if hostStr.startsWith "[" && hostStr.endsWith "]" then
    let hostStr := hostStr.extract ⟨1⟩ ⟨hostStr.length-1⟩

    let some res := Std.Net.IPv6Addr.ofString hostStr
      | Except.error "cannot parse ipv6"

    return .ipv6 res
  else if hostStr.all (fun c => c.isDigit || c == '.') then

    let some res := Std.Net.IPv4Addr.ofString hostStr
      | Except.error "cannot parse ipv4"

    return .ipv4 res
  else
    return .name hostStr

private def componentToPath (pathBytes : Option ByteArray) : Except String URI.Path :=
  match pathBytes with
  | none => .ok { segments := #[], absolute := false }
  | some bytes =>
    let pathStr := String.fromUTF8! bytes
    let isAbsolute := pathStr.startsWith "/"
    let cleanPath := if isAbsolute then pathStr.drop 1 else pathStr

    if cleanPath.isEmpty then
      .ok { segments := #[], absolute := isAbsolute }
    else do
      -- Split on unescaped forward slashes only
      let rawSegments := cleanPath.splitOn "/"
      let decodedSegments ← rawSegments.mapM (percentDecode ∘ String.toUTF8)
      .ok { segments := decodedSegments.toArray, absolute := isAbsolute }


private def componentToQuery (queryBytes : Option ByteSlice) : Except String (Option URI.Query) :=
  match queryBytes with
  | some bytes => do
    let queryStr := String.fromUTF8! bytes.toByteArray

    let pairs ← queryStr.splitOn "&" |>.mapM fun pair => do
      match pair.splitOn "=" with
      | [key] =>
        let decodedKey ← percentDecode key.toUTF8
        .ok (decodedKey, none)
      | key :: value :: _ =>
        let decodedKey  ← percentDecode key.toUTF8
        let decodedValue ← percentDecode value.toUTF8
        .ok (decodedKey, some decodedValue)
      | [] => .ok ("", none)

    .ok (some pairs.toArray)
  | none => .ok none

private def componentToAuthority (userinfo : Option (ByteSlice × Option ByteSlice)) (host : Option ByteSlice) (port : Option ByteSlice) : Parser (Option URI.Authority) := do
  let some hostBytes := host
    | return none

  let .ok hostValue := componentToHost hostBytes
    | fail "invalid host"

  let userinfoValue := userinfo.bind fun (user, pass) => componentToUserInfo user pass

  let portValue := port.bind parsePortNumber

  return (some { userInfo := userinfoValue, host := hostValue, port := portValue })

private def componentToUri (comp : UriComponents) : Parser URI := do
  let scheme := comp.schema.map (String.fromUTF8! ∘ ByteSlice.toByteArray)
  let authority ← componentToAuthority comp.userinfo comp.host comp.port

  let path ←
    match componentToPath comp.path with
    | .ok res => pure res
    | .error err => fail err

  let query ←
    match componentToQuery comp.query with
    | .ok res => pure res
    | .error res => fail res

  let fragment ←
    match comp.fragment.map (percentDecode ∘ ByteSlice.toByteArray) with
    | some (.ok res) => pure (some res)
    | some (.error err) => fail err
    | none => pure none


  return { scheme, authority, path, query, fragment }

/--
Parses a request target.
-/
public def parseRequestTarget : Parser RequestTarget := do

  -- The asterisk form
  if (← tryOpt (do skipByte '*'.toUInt8)).isSome then
    return .asteriskForm

  -- Try to parse as authority form (host:port) first
  let authorityResult ← do
    let some (userinfo, host, port) ← optional <| attempt parseAuthority
      | pure none

    let some result ← componentToAuthority userinfo host port
      | pure none

    if result.port.isNone then
      pure none
    else
      pure <| some result

  if let some auth := authorityResult then
    return .authorityForm auth

  -- Try to parse as absolute URI (has scheme)
  let absoluteResult ← tryOpt do
    let comp ← parseUri
    if comp.schema.isSome then
      componentToUri comp
    else
      fail "not absolute URI"

  if let some uri := absoluteResult then
    return .absoluteForm uri

  -- Check if input starts with a path (/ or alphanumeric)
  let startsWithPath ← peekWhen? (fun c => c == '/'.toUInt8 || isAlphaNum c)

  if startsWithPath.isSome then
    -- Parse as origin form (path and optional query)
    let comp ← parseUri
    let uri ← componentToUri comp
    return .originForm uri.path uri.query

  -- Fallback: try parsing as origin form anyway
  let comp ← parseUri
  let uri ← componentToUri comp
  return .originForm uri.path uri.query

end Parser
end Http
end Std
