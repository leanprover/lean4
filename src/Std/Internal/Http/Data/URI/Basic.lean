/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Net
public import Std.Internal.Http.Data.URI.Encoding
public import Std.Internal.Http.Internal

public section

/-!
# URI Structure

This module defines the complete URI structure following RFC 3986, including
schemes, authorities, paths, queries, fragments, and request targets.

All text components use the encoding types from `Std.Http.URI.Encoding` to ensure
proper percent-encoding is maintained throughout.
-/

namespace Std.Http

set_option linter.all true

namespace URI

/--
URI scheme identifier (e.g., "http", "https", "ftp").
-/
abbrev Scheme := String

/--
User information component containing the username and optional password.
Both fields are stored as EncodedString to ensure proper percent-encoding.
-/
structure UserInfo where
  /--
  The username (percent-encoded).
  -/
  username : EncodedString

  /--
  The optional password (percent-encoded).
  -/
  password : Option EncodedString
deriving Inhabited, Repr

/--
Host component of a URI, supporting domain names and IP addresses.
-/
inductive Host
  /--
  A registered domain name (percent-encoded).
  -/
  | name (name : EncodedString)

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
The authority component of a URI, identifying the network location of the resource.

Reference: https://www.rfc-editor.org/rfc/rfc3986.html#section-3.2
-/
structure Authority where
  /--
  Optional user information (username and password).
  -/
  userInfo : Option UserInfo := none

  /--
  The host identifying the network location.
  -/
  host : Host

  /--
  Optional port number for connecting to the host.
  -/
  port : Option Port := none
deriving Inhabited, Repr

/--
Hierarchical path component of a URI.
Each segment is stored as an EncodedString to ensure proper percent-encoding.
-/
structure Path where
  /--
  The path segments making up the hierarchical structure (each segment is percent-encoded).
  -/
  segments : Array EncodedString

  /--
  Whether the path is absolute (begins with '/') or relative.
  -/
  absolute : Bool
deriving Inhabited, Repr

instance : ToString Path where
  toString path :=
    let result := String.intercalate "/" (path.segments.map toString).toList
    if path.absolute then "/" ++ result else result

/--
Query string represented as an array of key-value pairs.
Keys are stored as EncodedQueryString to ensure proper encoding
for application/x-www-form-urlencoded format.
Values are optional to support parameters without values (e.g., "?flag").
Order is preserved based on insertion order.
-/
@[expose]
def Query := Array (EncodedQueryString × EncodedQueryString)
  deriving Repr

namespace Query

/--
Extracts all unique query parameter names.
-/
@[expose]
def names (query : Query) : Array EncodedQueryString :=
  query.map (fun p => p.fst)
  |> Array.toList
  |> List.eraseDups
  |> List.toArray

/--
Extracts all query parameter values.
-/
@[expose]
def values (query : Query) : Array EncodedQueryString :=
  query.map (fun p => p.snd)

/--
Returns the query as an array of (key, value) pairs.
This is an identity function since Query is already an array of pairs.
-/
@[expose]
def toArray (query : Query) : Array (EncodedQueryString × EncodedQueryString) :=
  query

/--
Encodes a query parameter as a string in the format "key" or "key=value".
The key and value are already percent-encoded in EncodedQueryString format.
-/
def encodeQueryParam (key : EncodedQueryString) (value : EncodedQueryString) : String :=
  match toString value with
  | "" => toString key
  | v => s!"{toString key}={toString v}"

/--
Finds the first decoded value of a query parameter by key name.
Returns `none` if the key is not found.
-/
def find? (query : Query) (key : String) : Option EncodedQueryString :=
  let encodedKey := EncodedQueryString.encode key
  let matchingKey := Array.find? (fun x => x.fst.toByteArray = encodedKey.toByteArray) query
  matchingKey.map (fun x => x.snd)

/--
Finds all decoded values of a query parameter by key name.
Returns an empty array if the key is not found.
-/
def findAll (query : Query) (key : String) : Array EncodedQueryString :=
  let encodedKey := EncodedQueryString.encode key
  query.filterMap (fun x =>
    if x.fst.toByteArray = encodedKey.toByteArray then
      some (x.snd)
    else none)

/--
Adds a query parameter to the query string.
-/
def insert (query : Query) (key : String) (value : String) : Query :=
  let encodedKey := EncodedQueryString.encode key
  let encodedValue := EncodedQueryString.encode value
  query.push (encodedKey, encodedValue)

/--
Adds a query parameter to the query string.
-/
def insertEncoded (query : Query) (key : EncodedQueryString) (value : EncodedQueryString) : Query :=
  query.push (key, value)

/--
Creates an empty query string.
-/
def empty : Query := #[]

/--
Creates a query string from a list of key-value pairs.
-/
def ofList (pairs : List (EncodedQueryString × EncodedQueryString)) : Query :=
  pairs.toArray

/--
Checks if a query parameter exists.
-/
def contains (query : Query) (key : String) : Bool :=
  let encodedKey := EncodedQueryString.encode key
  query.any (fun x => x.fst.toByteArray = encodedKey.toByteArray)

/--
Removes all occurrences of a query parameter by key name.
-/
def erase (query : Query) (key : String) : Query :=
  let encodedKey := EncodedQueryString.encode key
  -- Filter out matching keys
  query.filter (fun x => x.fst.toByteArray ≠ encodedKey.toByteArray)

/--
Converts the query to a properly encoded query string format.
Example: "key1=value1&key2=value2&flag"
-/
def toString (query : Query) : String :=
  let params := query.map (fun (k, v) => encodeQueryParam k v)
  String.intercalate "&" params.toList

instance : ToString Query where
  toString := Query.toString

instance : EmptyCollection Query :=
  ⟨Query.empty⟩

instance : Singleton (String × String) Query :=
  ⟨fun ⟨k, v⟩ => Query.empty.insert k v⟩

instance : Insert (String × String) Query :=
  ⟨fun ⟨k, v⟩ q => q.insert k v⟩

end Query

end URI

/--
Complete URI structure following RFC 3986.
All text components use encoded string types to ensure proper percent-encoding.

Reference: https://www.rfc-editor.org/rfc/rfc3986.html
-/
structure URI where
  /--
  The URI scheme (e.g., "http", "https", "ftp").
  -/
  scheme : URI.Scheme

  /--
  Optional authority component (user info, host, and port).
  -/
  authority : Option URI.Authority

  /--
  The hierarchical path component.
  -/
  path : URI.Path

  /--
  Optional query string as key-value pairs.
  -/
  query : URI.Query

  /--
  Optional fragment identifier (the part after '#'), percent-encoded.
  -/
  fragment : Option URI.EncodedString
deriving Repr

instance : Inhabited URI where
  default := ⟨default, default, { absolute := true, segments := #[] }, URI.Query.empty, default⟩

namespace URI

/--
Fluent builder for constructing URIs.
Takes raw (unencoded) strings and handles encoding automatically when building the final URI.
-/
structure Builder where
  /--
  The URI scheme (e.g., "http", "https").
  -/
  scheme : Option String := none

  /--
  User information (username and optional password).
  -/
  userInfo : Option UserInfo := none

  /--
  The host component.
  -/
  host : Option Host := none

  /--
  The port number.
  -/
  port : Option URI.Port := none

  /--
  Path segments (will be encoded when building).
  -/
  pathSegments : Array String := #[]

  /--
  Query parameters as (key, optional value) pairs (will be encoded when building).
  -/
  query : Array (String × Option String) := #[]

  /--
  Fragment identifier (will be encoded when building).
  -/
  fragment : Option String := none
deriving Inhabited

namespace Builder

/--
Creates an empty URI builder.
-/
def empty : Builder := {}

/--
Sets the URI scheme (e.g., "http", "https").
-/
def setScheme (b : Builder) (scheme : String) : Builder :=
  { b with scheme := some scheme }

/--
Sets the user information with username and optional password.
The strings will be automatically percent-encoded.
-/
def setUserInfo (b : Builder) (username : String) (password : Option String := none) : Builder :=
  { b with userInfo := some {
      username := EncodedString.encode username
      password := password.map EncodedString.encode
    }
  }

/--
Sets the host as a domain name.
The domain name will be automatically percent-encoded.
-/
def setHost (b : Builder) (name : String) : Builder :=
  { b with host := some (Host.name (EncodedString.encode name)) }

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
Replaces all path segments.
Segments will be automatically percent-encoded when building.
-/
def setPath (b : Builder) (segments : Array String) : Builder :=
  { b with pathSegments := segments }

/--
Appends a single segment to the path.
The segment will be automatically percent-encoded when building.
-/
def appendPathSegment (b : Builder) (segment : String) : Builder :=
  { b with pathSegments := b.pathSegments.push segment }

/--
Adds a query parameter with a value.
Both key and value will be automatically percent-encoded when building.
-/
def addQueryParam (b : Builder) (key : String) (value : String) : Builder :=
  { b with query := b.query.push (key, some value) }

/--
Adds a query parameter without a value (flag parameter).
The key will be automatically percent-encoded when building.
-/
def addQueryFlag (b : Builder) (key : String) : Builder :=
  { b with query := b.query.push (key, none) }

/--
Replaces all query parameters.
Keys and values will be automatically percent-encoded when building.
-/
def setQuery (b : Builder) (query : Array (String × Option String)) : Builder :=
  { b with query := query }

/--
Sets the fragment identifier.
The fragment will be automatically percent-encoded when building.
-/
def setFragment (b : Builder) (fragment : String) : Builder :=
  { b with fragment := some fragment }

/--
Builds a complete URI from the builder state, encoding all components.
Defaults to "https" scheme if none is specified.
-/
def build (b : Builder) : URI :=
  let scheme := b.scheme.getD "https"

  let authority :=
    if b.host.isSome then
      some {
        userInfo := b.userInfo
        host := b.host.get!
        port := b.port
      }
    else none

  let path : Path := {
    segments := b.pathSegments.map EncodedString.encode
    absolute := true
  }

  let query :=
    b.query.map fun (k, v) =>
      (EncodedQueryString.encode k, EncodedQueryString.encode (v.getD ""))

  let query := URI.Query.ofList query.toList

  {
    scheme := scheme
    authority := authority
    path
    query := query
    fragment := b.fragment.map EncodedString.encode
  }

end Builder
end URI

/--
HTTP request target forms as defined in RFC 7230 Section 5.3.

Reference: https://www.rfc-editor.org/rfc/rfc7230.html#section-5.3
-/
inductive RequestTarget where
  /--
  Origin-form request target (most common for HTTP requests).
  Consists of a path, optional query string, and optional fragment.
  Example: `/path/to/resource?key=value#section`
  -/
  | originForm (path : URI.Path) (query : Option URI.Query) (fragment : Option URI.EncodedString)

  /--
  Absolute-form request target containing a complete URI.
  Used when making requests through a proxy.
  Example: `http://example.com:8080/path?key=value`
  -/
  | absoluteForm (uri : URI)

  /--
  Authority-form request target (used for CONNECT requests).
  Example: `example.com:443`
  -/
  | authorityForm (authority : URI.Authority)

  /--
  Asterisk-form request target (used with OPTIONS requests).
  Example: `*`
  -/
  | asteriskForm
deriving Inhabited, Repr

namespace RequestTarget

/--
Extracts the path component from a request target, if available.
Returns an empty relative path for targets without a path.
-/
def path : RequestTarget → URI.Path
  | .originForm p _ _ => p
  | .absoluteForm u => u.path
  | _ => { segments := #[], absolute := false }

/--
Extracts the query component from a request target, if available.
Returns an empty array for targets without a query.
-/
def query : RequestTarget → URI.Query
  | .originForm _ q _ => q.getD URI.Query.empty
  | .absoluteForm u => u.query
  | _ => URI.Query.empty

/--
Extracts the authority component from a request target, if available.
-/
def authority? : RequestTarget → Option URI.Authority
  | .authorityForm a => some a
  | .absoluteForm u => u.authority
  | _ => none

/--
Extracts the fragment component from a request target, if available.
-/
def fragment? : RequestTarget → Option URI.EncodedString
  | .originForm _ _ frag => frag
  | .absoluteForm u => u.fragment
  | _ => none

/--
Extracts the full URI if the request target is in absolute form.
-/
def uri? : RequestTarget → Option URI
  | .absoluteForm u => some u
  | _ => none

end RequestTarget

-- ToString implementations

instance : ToString URI.Host where
  toString
    | .name n => toString n
    | .ipv4 addr => toString addr
    | .ipv6 addr => s!"[{toString addr}]"

instance : ToString URI.Authority where
  toString auth :=
    let userPart := match auth.userInfo with
      | none => ""
      | some ⟨name, some pass⟩ => s!"{toString name}:{toString pass}@"
      | some ⟨name, none⟩ => s!"{toString name}@"
    let hostPart := toString auth.host
    let portPart := match auth.port with
      | none => ""
      | some p => s!":{p}"
    s!"{userPart}{hostPart}{portPart}"

instance : ToString URI.Path where
  toString
    | ⟨segs, abs⟩ =>
      let encodedSegs := segs.map toString |>.toList
      let core := String.intercalate "/" encodedSegs
      if abs then s!"/{core}" else core

instance : ToString URI.Query where
  toString q :=
    if q.isEmpty then "" else
      let encodedParams := q.toList.map fun (key, value) =>
        URI.Query.encodeQueryParam key value
      "?" ++ String.intercalate "&" encodedParams

instance : ToString URI where
  toString uri :=
    let schemePart :=  uri.scheme
    let authorityPart := match uri.authority with
      | none => ""
      | some auth => s!"//{toString auth}"
    let pathPart := toString uri.path
    let queryPart := toString uri.query
    let fragmentPart := match uri.fragment with
      | none => ""
      | some f => s!"#{toString f}"
    s!"{schemePart}:{authorityPart}{pathPart}{queryPart}{fragmentPart}"

instance : ToString RequestTarget where
  toString
    | .originForm path query frag =>
        let pathStr := toString path
        let queryStr := query.map toString |>.getD ""
        let frag := frag.map (fun f => "#" ++ toString f) |>.getD ""
        s!"{pathStr}{queryStr}{frag}"
    | .absoluteForm uri => toString uri
    | .authorityForm auth => toString auth
    | .asteriskForm => "*"

end Std.Http
