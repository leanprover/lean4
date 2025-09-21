/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Net
public import Std.Internal.Http.Encode

public section

namespace Std
namespace Http
namespace URI

set_option linter.all true

/--
URI scheme (e.g., "http", "https", "ftp").
-/
abbrev Scheme := String

/--
User information component containing username and password.
-/
structure UserInfo where
  /--
  Optional username to include in the authority portion of a URI.
  -/
  user : Option String

  /--
  Optional password associated with the username, rarely used in modern practice.
  -/
  pass : Option String
deriving Inhabited, Repr

/--
Host component of a URI, supporting domain names and IP addresses.
-/
inductive Host
  /--
  A registered name (typically a domain name).
  -/
  | name (name : String)

  /--
  An IPv4 address.
  -/
  | ipv4 (ipv4 : Net.IPv4Addr)

  /--
  An IPv6 address.
  -/
  | ipv6 (ipv6 : Net.IPv6Addr)
deriving Inhabited

instance : Repr Host where
  reprPrec x prec :=
    let nestPrec := (if prec ≥ 1024 then 1 else 2)
    let name := "Std.Http.URI.Host"
    let repr (ctr : String) a := Repr.addAppParen (Format.nest nestPrec (.text s!"{name}.{ctr}" ++ .line ++ a)).group prec
    match x with
    | Host.name a => repr "name" (reprArg a)
    | Host.ipv4 a => repr "ipv4" (toString a)
    | Host.ipv6 a => repr "ipv6" (toString a)

/--
TCP number port.
-/
abbrev Port := UInt16

/--
The authority component in a URI provides the necessary information for locating the resource
on the network.

* Reference: https://www.rfc-editor.org/rfc/rfc3986.html#section-3.2
-/
structure Authority where

  /--
  Optional user information (username and optional password).
  -/
  userInfo: Option UserInfo := none

  /--
  The host identifying the network location of the resource.
  -/
  host: Host

  /--
  Optional port number for connecting to the host.
  -/
  port: Option Port := none
deriving Inhabited, Repr

/--
Abstraction of paths.
-/
structure Path where
  /--
  Path segments making up the hierarchical structure.
  -/
  segments : Array String

  /--
  Whether the path is absolute (begins with a `/`) or relative.
  -/
  absolute : Bool := false
deriving Inhabited, Repr

/--
Query string represented as an array of key–value pairs.
-/
abbrev Query := Array (String × Option String)

end URI

/--
Complete URI structure following RFC 3986.
-/
structure URI where
  scheme : Option URI.Scheme
  authority : Option URI.Authority
  path : URI.Path
  query : Option URI.Query
  fragment : Option String
deriving Inhabited, Repr

/--
HTTP request target forms as defined in RFC 7230 Section 5.3.
-/
inductive RequestTarget where
  | originForm (path : URI.Path) (query : Option URI.Query)
  | absoluteForm (uri : URI)
  | authorityForm (authority : URI.Authority)
  | asteriskForm
deriving Inhabited, Repr

namespace RequestTarget

def path? : RequestTarget → Option URI.Path
  | .originForm p _ => some p
  | .absoluteForm u => some u.path
  | _ => none

def query? : RequestTarget → Option URI.Query
  | .originForm _ q => q
  | .absoluteForm u => u.query
  | _ => none

def authority? : RequestTarget → Option URI.Authority
  | .authorityForm a => some a
  | .absoluteForm u => u.authority
  | _ => none

def uri? : RequestTarget → Option URI
  | .absoluteForm u => some u
  | _ => none

end RequestTarget

-- ToString implementations

def isUnreserved (c : UInt8) : Bool :=
  (c ≥ '0'.toUInt8 && c ≤ '9'.toUInt8) || (c ≥ 'a'.toUInt8 && c ≤ 'z'.toUInt8) || (c ≥ 'A'.toUInt8 && c ≤ 'Z'.toUInt8)
  || c = '-'.toUInt8 || c = '.'.toUInt8 || c = '_'.toUInt8 || c = '~'.toUInt8

def hexDigit (n : UInt8) : UInt8 :=
  if n < 10 then (n + '0'.toUInt8)
  else (n - 10 + 'A'.toUInt8)

def byteToHex (b : UInt8) : ByteArray :=
  let hi := hexDigit (b >>> 4)
  let lo := hexDigit (b &&& 0xF)
  ByteArray.mk #['%'.toUInt8, hi, lo]

def percentEncode (s : String) : ByteArray :=
  s.toUTF8.foldl (init := ByteArray.emptyWithCapacity s.utf8ByteSize) fun acc c =>
    if isUnreserved c then  acc.push c else acc.append (byteToHex c)

instance : ToString URI.UserInfo where
  toString
    | ⟨some u, some p⟩ =>
        let encodedU := String.fromUTF8! (percentEncode u)
        let encodedP := String.fromUTF8! (percentEncode p)
        s!"{encodedU}:{encodedP}"
    | ⟨some u, none⟩   => String.fromUTF8! (percentEncode u)
    | ⟨none, some p⟩   => s!":{String.fromUTF8! (percentEncode p)}"
    | ⟨none, none⟩     => ""

instance : ToString URI.Host where
  toString
    | .name n => String.fromUTF8! (percentEncode n)
    | .ipv4 addr => toString addr
    | .ipv6 addr => s!"[{toString addr}]"

instance : ToString URI.Authority where
  toString auth :=
    let userPart := match auth.userInfo with
      | none => ""
      | some ui => s!"{ui}@"
    let hostPart := toString auth.host
    let portPart := match auth.port with
      | none => ""
      | some p => s!":{p}"
    s!"{userPart}{hostPart}{portPart}"

instance : ToString URI.Path where
  toString
    | ⟨segs, abs⟩ =>
      let encodedSegs := segs.toList.map (fun seg => String.fromUTF8! (percentEncode seg))
      let core := String.intercalate "/" encodedSegs
      if abs then s!"/{core}" else core

def encodeQueryParam (key : String) (value : Option String) : String :=
  let encodedKey := String.fromUTF8! (percentEncode key)
  match value with
  | none => encodedKey
  | some v =>
      let encodedValue := String.fromUTF8! (percentEncode v)
      s!"{encodedKey}={encodedValue}"

instance : ToString URI.Query where
  toString q :=
    if q.isEmpty then "" else
      let encodedParams := q.toList.map fun (key, value) =>
        match key with
        | "" => match value with
          | none => ""
          | some v => s!"={String.fromUTF8! (percentEncode v)}"
        | k => encodeQueryParam k value
      "?" ++ String.intercalate "&" encodedParams

instance : ToString URI where
  toString uri :=
    let schemePart := match uri.scheme with
      | none => ""
      | some s => s!"{String.fromUTF8! (percentEncode s)}:"
    let authorityPart := match uri.authority with
      | none => ""
      | some auth => s!"//{toString auth}"
    let pathPart := toString uri.path
    let queryPart := uri.query.map toString |>.getD ""
    let fragmentPart := match uri.fragment with
      | none => ""
      | some f => s!"#{String.fromUTF8! (percentEncode f)}"
    s!"{schemePart}{authorityPart}{pathPart}{queryPart}{fragmentPart}"

instance : ToString RequestTarget where
  toString
    | .originForm path query =>
        let pathStr := toString path
        let queryStr := query.map toString |>.getD ""
        s!"{pathStr}{queryStr}"
    | .absoluteForm uri => toString uri
    | .authorityForm auth => toString auth
    | .asteriskForm => "*"

end Http
end Std
