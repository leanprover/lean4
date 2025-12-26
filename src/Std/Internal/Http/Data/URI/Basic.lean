/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Net

public section

/-!
# URI

This modules defines all the URI related components like `RequestTarget`, `Path`, `Query` and others.
-/

namespace Std.Http.URI

set_option linter.all true

private def hexDigit (n : UInt8) : UInt8 :=
  if n < 10 then (n + '0'.toUInt8)
  else (n - 10 + 'A'.toUInt8)

private def byteToHex (b : UInt8) : ByteArray :=
  let hi := hexDigit (b >>> 4)
  let lo := hexDigit (b &&& 0xF)
  ByteArray.mk #['%'.toUInt8, hi, lo]

private def isUnreserved (c : UInt8) : Bool :=
  (c ≥ '0'.toUInt8 && c ≤ '9'.toUInt8) || (c ≥ 'a'.toUInt8 && c ≤ 'z'.toUInt8) || (c ≥ 'A'.toUInt8 && c ≤ 'Z'.toUInt8)
  || c = '-'.toUInt8 || c = '.'.toUInt8 || c = '_'.toUInt8 || c = '~'.toUInt8

private def isPathAllowed (c : UInt8) : Bool :=
  isUnreserved c
  || c = ':'.toUInt8 || c = '@'.toUInt8 || c = '!'.toUInt8 || c = '$'.toUInt8
  || c = '&'.toUInt8 || c = '\''.toUInt8 || c = '('.toUInt8 || c = ')'.toUInt8
  || c = '*'.toUInt8 || c = '+'.toUInt8 || c = ','.toUInt8 || c = ';'.toUInt8
  || c = '='.toUInt8

/--
Encodes a string as a URI component by percent-encoding all characters.
-/
def encodeURIComponent (s : String) : String :=
  let result := s.toUTF8.foldl (init := ByteArray.emptyWithCapacity s.utf8ByteSize) fun acc c =>
    if isUnreserved c then  acc.push c else acc.append (byteToHex c)

  String.fromUTF8! result

/--
Encodes a string as a URI path component by percent-encoding characters not allowed in paths.
Allows unreserved characters plus sub-delims (: @ ! $ & ' ( ) * + , ; =) commonly used in paths.
-/
def encodeURIPathComponent (s : String) : String :=
  let result := s.toUTF8.foldl (init := ByteArray.emptyWithCapacity s.utf8ByteSize) fun acc c =>
    if isPathAllowed c then acc.push c else acc.append (byteToHex c)

  String.fromUTF8! result

/--
URI scheme (e.g., "http", "https", "ftp").
-/
abbrev Scheme := String

/--
User information component containing the username and password.
-/
structure UserInfo where

  /--
  User info user name.
  -/
  username : String

  /--
  User info password.
  -/
  password : Option String
deriving Inhabited, Repr

/--
Host component of a URI, supporting domain names and IP addresses.
-/
inductive Host
  /--
  A registered name (e.g., a domain name).
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

    let repr (ctr : String) a :=
      Repr.addAppParen (Format.nest nestPrec (.text s!"{name}.{ctr}" ++ .line ++ a)).group prec

    match x with
    | Host.name a => repr "name" (reprArg a)
    | Host.ipv4 a => repr "ipv4" (toString a)
    | Host.ipv6 a => repr "ipv6" (toString a)

/--
TCP port number.
-/
abbrev Port := UInt16

/--
The authority component in a URI provides the necessary information for locating the resource
on the network.

* Reference: https://www.rfc-editor.org/rfc/rfc3986.html#section-3.2
-/
structure Authority where
  /--
  Optional user information such as username and password.
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

instance : ToString Path where
  toString path :=
    let result := String.intercalate "/" path.segments.toList
    if path.absolute then "/" ++ result else result

/--
Query string represented as an array of key–value pairs.
-/
@[expose]
def Query := Array (String × Option String)

namespace Query

/--
Gets all the names of the query parameters
-/
@[expose]
def names (query : Query) : List String :=
  query.map Prod.fst |>.toList

/--
Gets all the values of the query parameters
-/
@[expose]
def values (query : Query) : Array String :=
  query.map Prod.snd |>.map (Option.getD · "")

/--
Gets all the values of the query parameters
-/
@[expose]
def pairs (query : Query) : Array (String × String) :=
  query.map (fun (x,y) => (x, y.getD ""))

/--
Encodes query params with percent encoding.
-/
def encodeQueryParam (key : String) (value : Option String) : String :=
  let encodedKey := encodeURIComponent key
  match value with
  | none => encodedKey
  | some v =>
      let encodedValue := encodeURIComponent v
      s!"{encodedKey}={encodedValue}"

end Query

instance : Repr Query :=
  inferInstanceAs (Repr (Array (String × Option String)))

end URI

/--
Complete URI structure following RFC 3986.
-/
structure URI where
  /--
  The scheme of the URI (e.g., "http", "https", "ftp").
  -/
  scheme : URI.Scheme

  /--
  Optional authority component containing user info, host, and port.
  -/
  authority : Option URI.Authority

  /--
  Path component of the URI, representing the hierarchical location.
  -/
  path : { p : URI.Path // p.absolute }

  /--
  Optional query string of the URI represented as key–value pairs.
  -/
  query : Option URI.Query

  /--
  Optional fragment identifier of the URI (the part after `#`).
  -/
  fragment : Option String
deriving Repr

instance : Inhabited URI where
  default := ⟨default, default, ⟨{ absolute := true, segments := #[] }, by simp⟩, default, default⟩

namespace URI

/--
Builder for constructing URIs with a fluent API.
-/
structure Builder where
  scheme : Option String := none
  userInfo : Option UserInfo := none
  host : Option Host := none
  port : Option URI.Port := none
  pathSegments : Array String := #[]
  query : Array (String × Option String) := #[]
  fragment : Option String := none
deriving Inhabited

namespace Builder

/--
Creates an empty builder.
-/
def empty : Builder := {}

/--
Sets the scheme of the URI.
-/
def setScheme (b : Builder) (scheme : String) : Builder :=
  { b with scheme := some scheme }

/--
Sets the user information.
-/
def setUserInfo (b : Builder) (userInfo : UserInfo) : Builder :=
  { b with userInfo := some userInfo }

/--
Sets the host as a domain name.
-/
def setHost (b : Builder) (name : String) : Builder :=
  { b with host := some (Host.name name) }

/--
Sets the host as an IPv4 address.
-/
def setHostIPv4 (b : Builder) (addr : Net.IPv4Addr) : Builder :=
  { b with host := some (Host.ipv4 addr) }

/--
Sets the host as an IPv6 address.
-/
def setHostIPv6 (b : Builder) (addr : Net.IPv6Addr) : Builder :=
  { b with host := some (Host.ipv6 addr) }

/--
Sets the port number.
-/
def setPort (b : Builder) (port : Port) : Builder :=
  { b with port := some port }

/--
Sets the path segments and whether the path is absolute.
-/
def setPath (b : Builder) (segments : Array String) : Builder :=
  { b with pathSegments := segments }

/--
Appends a segment to the path.
-/
def appendPathSegment (b : Builder) (segment : String) : Builder :=
  { b with pathSegments := b.pathSegments.push segment }

/--
Adds a query parameter with a value.
-/
def addQueryParam (b : Builder) (key : String) (value : String) : Builder :=
  { b with query := b.query.push (key, some value) }

/--
Adds a query parameter without a value (flag parameter).
-/
def addQueryFlag (b : Builder) (key : String) : Builder :=
  { b with query := b.query.push (key, none) }

/--
Sets the entire query array.
-/
def setQuery (b : Builder) (query : Array (String × Option String)) : Builder :=
  { b with query := query }

/--
Sets the fragment identifier.
-/
def setFragment (b : Builder) (fragment : String) : Builder :=
  { b with fragment := some fragment }

/--
Builds a URI from the builder state.
Returns `none` if required components (scheme) are missing.
-/
def build (b : Builder) (hasScheme : b.scheme.isSome := by decide) : URI :=
  let scheme := b.scheme.get hasScheme

  let authority :=
    if b.host.isSome then
      some {
        userInfo := b.userInfo
        host := b.host.get!
        port := b.port
      }
    else none

  let path : Path := {
    segments := b.pathSegments
    absolute := true
  }

  let query := if b.query.isEmpty then none else some b.query

  {
    scheme := scheme
    authority := authority
    path := ⟨path, by unfold path; simp⟩
    query := query
    fragment := b.fragment
  }

/--
Builds a URI from the builder, using default values for missing components.
-/
def buildWithDefaults (b : Builder) : URI :=
  let scheme := b.scheme.getD "http"

  let authority :=
    if b.host.isSome then
      some {
        userInfo := b.userInfo
        host := b.host.get!
        port := b.port
      }
    else none

  let path : Path := {
    segments := b.pathSegments
    absolute := true
  }

  let query := if b.query.isEmpty then none else some b.query

  {
    scheme := scheme
    authority := authority
    path := ⟨path, by unfold path; simp⟩
    query := query
    fragment := b.fragment
  }

end URI.Builder

/--
HTTP request target forms as defined in RFC 7230 Section 5.3.
-/
inductive RequestTarget where
  /--
  Request target using an origin-form (most common form for HTTP requests),
  consisting of a path, an optional query string, and an optional fragment.
  -/
  | originForm (path : URI.Path) (query : Option URI.Query) (fragment : Option String)

  /--
  Request target using an absolute-form URI.
  -/
  | absoluteForm (uri : URI)

  /--
  Request target using the authority-form (used for CONNECT requests).
  -/
  | authorityForm (authority : URI.Authority)

  /--
  Asterisk-form request target (used with OPTIONS requests).
  -/
  | asteriskForm
deriving Inhabited, Repr

namespace RequestTarget

/--
Returns the path component of a `RequestTarget`, if available.
-/
def path? : RequestTarget → Option URI.Path
  | .originForm p _ _ => some p
  | .absoluteForm u => some u.path
  | _ => none

/--
Returns the query component of a `RequestTarget`, if available.
-/
def query? : RequestTarget → Option URI.Query
  | .originForm _ q _ => q
  | .absoluteForm u => u.query
  | _ => none

/--
Returns the authority component of a `RequestTarget`, if available.
-/
def authority? : RequestTarget → Option URI.Authority
  | .authorityForm a => some a
  | .absoluteForm u => u.authority
  | _ => none

/--
Returns the full URI if the `RequestTarget` is in absolute form, otherwise `none`.
-/
def uri? : RequestTarget → Option URI
  | .absoluteForm u => some u
  | _ => none

end RequestTarget

-- ToString implementations

instance : ToString URI.Host where
  toString
    | .name n => URI.encodeURIComponent n
    | .ipv4 addr => toString addr
    | .ipv6 addr => s!"[{toString addr}]"

instance : ToString URI.Authority where
  toString auth :=
    let userPart := match auth.userInfo with
      | none => ""
      | some ⟨name, some pass⟩ => s!"{URI.encodeURIComponent name}:{URI.encodeURIComponent pass}@"
      | some ⟨name, none⟩ => s!"{URI.encodeURIComponent name}@"
    let hostPart := toString auth.host
    let portPart := match auth.port with
      | none => ""
      | some p => s!":{p}"
    s!"{userPart}{hostPart}{portPart}"

instance : ToString URI.Path where
  toString
    | ⟨segs, abs⟩ =>
      let encodedSegs := segs.toList.map (fun seg => URI.encodeURIPathComponent seg)
      let core := String.intercalate "/" encodedSegs
      if abs then s!"/{core}" else core

instance : ToString URI.Query where
  toString q :=
    if q.isEmpty then "" else
      let encodedParams := q.toList.map fun (key, value) =>
        match key with
        | "" => match value with
          | none => ""
          | some v => s!"={URI.encodeURIComponent v}"
        | k => URI.Query.encodeQueryParam k value
      "?" ++ String.intercalate "&" encodedParams

instance : ToString URI where
  toString uri :=
    let schemePart :=  URI.encodeURIComponent uri.scheme
    let authorityPart := match uri.authority with
      | none => ""
      | some auth => s!"://{toString auth}"
    let pathPart := toString uri.path
    let queryPart := uri.query.map toString |>.getD ""
    let fragmentPart := match uri.fragment with
      | none => ""
      | some f => s!"#{URI.encodeURIComponent f}"
    s!"{schemePart}{authorityPart}{pathPart}{queryPart}{fragmentPart}"

instance : ToString RequestTarget where
  toString
    | .originForm path query frag =>
        let pathStr := toString path
        let queryStr := query.map toString |>.getD ""
        let frag := frag.map ("#" ++ ·) |>.getD ""
        s!"{pathStr}{queryStr}{frag}"
    | .absoluteForm uri => toString uri
    | .authorityForm auth => toString auth
    | .asteriskForm => "*"

end Std.Http
