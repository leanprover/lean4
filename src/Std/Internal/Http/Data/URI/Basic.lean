/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
import Init.Data.ToString
public import Std.Net
public import Std.Internal.Http.Data.URI.Encoding
public import Std.Internal.Http.Internal

public section

/-!
# URI Structure

This module defines the complete URI structure following RFC 3986, including schemes, authorities,
paths, queries, fragments, and request targets.

All text components use the encoding types from `Std.Http.URI.Encoding` to ensure proper
percent-encoding is maintained throughout.
-/

namespace Std.Http

set_option linter.all true

open Internal Char

namespace URI

/--
URI scheme identifier (e.g., "http", "https", "ftp").
-/
abbrev Scheme := { s : String // IsLowerCase s }

instance : Inhabited Scheme where
  default := ⟨"", .isLowerCase_empty⟩

/--
User information component containing the username and optional password. Both fields store decoded
(unescaped) values.
-/
structure UserInfo where
  /--
  The username (decoded).
  -/
  username : String

  /--
  The optional password (decoded).
  -/
  password : Option String
deriving Inhabited, Repr

/--
Checks if a character is valid for use in a domain name.
Valid characters are ASCII alphanumeric, hyphens, and dots.
-/
def isValidDomainNameChar (c : Char) : Bool :=
  c.isAlphanum || c == '-' || c == '.'

/--
Proposition that asserts all characters in a string are valid domain name characters.
-/
abbrev IsValidDomainName (s : String) : Prop :=
  s.toList.all isValidDomainNameChar

/--
A domain name represented as a validated, lowercase-normalized string.
Only ASCII alphanumeric characters, hyphens, and dots are allowed.
Internationalized domain names must be converted to punycode before use.
-/
abbrev DomainName := { s : String // IsLowerCase s ∧ IsValidDomainName s }

/--
Host component of a URI, supporting domain names and IP addresses.
-/
inductive Host
  /--
  A domain name (lowercase-normalized).
  -/
  | name (name : DomainName)

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

instance : ToString Host where
  toString
    | .name n => n
    | .ipv4 addr => toString addr
    | .ipv6 addr => s!"[{toString addr}]"

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

instance : ToString Authority where
  toString auth :=
    let userPart := match auth.userInfo with
      | none => ""
      | some ⟨name, some pass⟩ => s!"{toString (EncodedString.encode name (r := isUnreserved))}:{toString (EncodedString.encode pass (r := isUnreserved))}@"
      | some ⟨name, none⟩ => s!"{toString (EncodedString.encode name (r := isUnreserved))}@"
    let hostPart := toString auth.host
    let portPart := match auth.port with
      | none => ""
      | some p => s!":{p}"
    s!"{userPart}{hostPart}{portPart}"

namespace Authority
end Authority

/--
Hierarchical path component of a URI. Each segment is stored as an `EncodedSegment` to maintain
proper percent-encoding.
-/
structure Path where
  /--
  The path segments making up the hierarchical structure (each segment is percent-encoded).
  -/
  segments : Array (EncodedSegment)

  /--
  Whether the path is absolute (begins with '/') or relative.
  -/
  absolute : Bool
deriving Inhabited, Repr

instance : ToString Path where
  toString path :=
    let result := String.intercalate "/" (path.segments.map toString).toList
    if path.absolute then "/" ++ result else result

namespace Path

/--
Returns true if the path has no segments.
-/
def isEmpty (p : Path) : Bool := p.segments.isEmpty

/--
Returns the parent path by removing the last segment. If the path is empty, returns the path unchanged.
-/
def parent (p : Path) : Path :=
  if p.segments.isEmpty then p
  else { p with segments := p.segments.pop }

/--
Joins two paths. If the second path is absolute, it is returned as-is. Otherwise, the second path's
segments are appended to the first path.
-/
def join (p1 : Path) (p2 : Path) : Path :=
  if p2.absolute then p2
  else { p1 with segments := p1.segments ++ p2.segments }

/--
Appends a single segment to the path. The segment will be percent-encoded.
-/
def append (p : Path) (segment : String) : Path :=
  { p with segments := p.segments.push (EncodedSegment.encode segment) }

/--
Appends an already-encoded segment to the path.
-/
def appendEncoded (p : Path) (segment : EncodedSegment) : Path :=
  { p with segments := p.segments.push segment }

/--
Removes dot segments from the path according to RFC 3986 Section 5.2.4. This handles "."
(current directory) and ".." (parent directory) segments.
-/
def normalize (p : Path) : Path :=
  let rec loop (input : List (EncodedSegment)) (output : List (EncodedSegment)) : List (EncodedSegment) :=
    match input with
    | [] =>
      output.reverse
    | segStr :: rest =>
      if toString segStr == "." then
        loop rest output
      else if toString segStr == ".." then
        match output with
        | [] => loop rest []
        | _ :: tail => loop rest tail
      else
        loop rest (segStr :: output)

  { p with segments := (loop p.segments.toList []).toArray }

/--
Returns the path segments as decoded strings.
Segments that cannot be decoded as UTF-8 are returned as their raw encoded form.
-/
def toDecodedSegments (p : Path) : Array String :=
  p.segments.map fun seg =>
    seg.decode.getD (toString seg)

end Path

/--
Query string represented as an array of key-value pairs. Both keys and values are stored as
`EncodedQueryParam` for proper application/x-www-form-urlencoded encoding. Values are optional to
support parameters without values (e.g., "?flag"). Order is preserved based on insertion order.
-/
@[expose]
def Query := Array (EncodedQueryParam × Option EncodedQueryParam)
deriving Repr, Inhabited

namespace Query

/--
Extracts all unique query parameter names.
-/
@[expose]
def names (query : Query) : Array EncodedQueryParam :=
  query.map (fun p => p.fst)
  |> Array.toList
  |> List.eraseDups
  |> List.toArray

/--
Extracts all query parameter values.
-/
@[expose]
def values (query : Query) : Array (Option EncodedQueryParam) :=
  query.map (fun p => p.snd)

/--
Returns the query as an array of (key, value) pairs. This is an identity function since Query is
already an array of pairs.
-/
@[expose]
def toArray (query : Query) : Array (EncodedQueryParam × Option EncodedQueryParam) :=
  query

/--
Formats a query parameter as a string in the format "key" or "key=value". The key and value are
already percent-encoded as `EncodedQueryParam`.
-/
def formatQueryParam (key : EncodedQueryParam) (value : Option EncodedQueryParam) : String :=
  match value with
  | none => toString key
  | some v => s!"{toString key}={toString v}"

/--
Finds the first value of a query parameter by key name. Returns `none` if the key is not found.
The value remains encoded as `EncodedQueryParam`.
-/
def find? (query : Query) (key : String) : Option (Option EncodedQueryParam) :=
  let encodedKey : EncodedQueryParam := EncodedQueryParam.encode key
  let matchingKey := Array.find? (fun x => x.fst.toByteArray = encodedKey.toByteArray) query
  matchingKey.map (fun x => x.snd)

/--
Finds all values of a query parameter by key name. Returns an empty array if the key is not found.
The values remain encoded as `EncodedQueryParam`.
-/
def findAll (query : Query) (key : String) : Array (Option EncodedQueryParam) :=
  let encodedKey : EncodedQueryParam := EncodedQueryParam.encode key
  query.filterMap (fun x =>
    if x.fst.toByteArray = encodedKey.toByteArray then
      some (x.snd)
    else none)

/--
Adds a query parameter to the query string.
-/
def insert (query : Query) (key : String) (value : String) : Query :=
  let encodedKey : EncodedQueryParam := EncodedQueryParam.encode key
  let encodedValue : EncodedQueryParam := EncodedQueryParam.encode value
  query.push (encodedKey, some encodedValue)

/--
Adds a query parameter to the query string.
-/
def insertEncoded (query : Query) (key : EncodedQueryParam) (value : Option EncodedQueryParam) : Query :=
  query.push (key, value)

/--
Creates an empty query string.
-/
def empty : Query := #[]

/--
Creates a query string from a list of key-value pairs.
-/
def ofList (pairs : List (EncodedQueryParam × Option EncodedQueryParam)) : Query :=
  pairs.toArray

/--
Checks if a query parameter exists.
-/
def contains (query : Query) (key : String) : Bool :=
  let encodedKey : EncodedQueryParam := EncodedQueryParam.encode key
  query.any (fun x => x.fst.toByteArray = encodedKey.toByteArray)

/--
Removes all occurrences of a query parameter by key name.
-/
def erase (query : Query) (key : String) : Query :=
  let encodedKey : EncodedQueryParam := EncodedQueryParam.encode key
  -- Filter out matching keys
  query.filter (fun x => x.fst.toByteArray ≠ encodedKey.toByteArray)

/--
Gets the first value of a query parameter by key name, decoded as a string.
Returns `none` if the key is not found or if the value cannot be decoded as UTF-8.
-/
def get (query : Query) (key : String) : Option String :=
  match query.find? key with
  | none => none
  | some none => some ""  -- Key exists but has no value
  | some (some encoded) => encoded.decode

/--
Gets the first value of a query parameter by key name, decoded as a string.
Returns the default value if the key is not found or if the value cannot be decoded.
-/
def getD (query : Query) (key : String) (default : String) : String :=
  query.get key |>.getD default

/--
Sets a query parameter, replacing all existing values for that key.
Both key and value will be automatically percent-encoded.
-/
def set (query : Query) (key : String) (value : String) : Query :=
  query.erase key |>.insert key value

/--
Converts the query to a properly encoded query string format.
Example: "key1=value1&key2=value2&flag"
-/
def toRawString (query : Query) : String :=
  let params := query.map (fun (k, v) => formatQueryParam k v)
  String.intercalate "&" params.toList

instance : EmptyCollection Query :=
  ⟨Query.empty⟩

instance : Singleton (String × String) Query :=
  ⟨fun ⟨k, v⟩ => Query.empty.insert k v⟩

instance : Insert (String × String) Query :=
  ⟨fun ⟨k, v⟩ q => q.insert k v⟩

instance : ToString Query where
  toString q :=
    if q.isEmpty then "" else
      let encodedParams := q.toList.map fun (key, value) =>
        Query.formatQueryParam key value
      "?" ++ String.intercalate "&" encodedParams

end Query

end URI

/--
Complete URI structure following RFC 3986. All text components use encoded string types to ensure
proper percent-encoding.

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
  fragment : Option String
deriving Repr, Inhabited

instance : ToString URI where
  toString uri :=
    let schemePart := uri.scheme
    let authorityPart := match uri.authority with
      | none => ""
      | some auth => s!"//{toString auth}"
    let pathPart := toString uri.path
    let queryPart := toString uri.query
    let fragmentPart := uri.fragment.map (fun f => "#" ++ toString (URI.EncodedFragment.encode f)) |>.getD ""
    s!"{schemePart}:{authorityPart}{pathPart}{queryPart}{fragmentPart}"

namespace URI

/--
Fluent builder for constructing URIs. Takes raw (unencoded) strings and handles encoding
automatically when building the final URI.
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
      username := username
      password := password
    }
  }

/--
Sets the host as a domain name, returning `none` if the name contains invalid characters.
The domain name will be automatically lowercased.
Only ASCII alphanumeric characters, hyphens, and dots are allowed.
Internationalized domain names must be converted to punycode before use.
-/
def setHost? (b : Builder) (name : String) : Option Builder :=
  let lower := name.toLower
  if h : IsValidDomainName lower then
    some { b with host := some (Host.name ⟨lower, IsLowerCase.isLowerCase_toLower, h⟩) }
  else
    none

/--
Sets the host as a domain name, panicking if the name contains invalid characters.
The domain name will be automatically lowercased.
Only ASCII alphanumeric characters, hyphens, and dots are allowed.
Internationalized domain names must be converted to punycode before use.
-/
def setHost! (b : Builder) (name : String) : Builder :=
  match b.setHost? name with
  | some b => b
  | none   => panic! s!"invalid domain name: {name.quote}"

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
Replaces all path segments. Segments will be automatically percent-encoded when building.
-/
def setPath (b : Builder) (segments : Array String) : Builder :=
  { b with pathSegments := segments }

/--
Appends a single segment to the path. The segment will be automatically percent-encoded when building.
-/
def appendPathSegment (b : Builder) (segment : String) : Builder :=
  { b with pathSegments := b.pathSegments.push segment }

/--
Adds a query parameter with a value. Both key and value will be automatically percent-encoded when
building.
-/
def addQueryParam (b : Builder) (key : String) (value : String) : Builder :=
  { b with query := b.query.push (key, some value) }

/--
Adds a query parameter without a value (flag parameter). The key will be automatically
percent-encoded when building.
-/
def addQueryFlag (b : Builder) (key : String) : Builder :=
  { b with query := b.query.push (key, none) }

/--
Replaces all query parameters. Keys and values will be automatically percent-encoded when building.
-/
def setQuery (b : Builder) (query : Array (String × Option String)) : Builder :=
  { b with query := query }

/--
Sets the fragment identifier. The fragment will be automatically percent-encoded when building.
-/
def setFragment (b : Builder) (fragment : String) : Builder :=
  { b with fragment := some fragment }

/--
Builds a complete URI from the builder state, encoding all components. Defaults to "https" scheme if
none is specified.
-/
def build (b : Builder) : URI :=
  let scheme := b.scheme.getD "https"

  let authority :=
    if b.host.isSome then
      some {
        userInfo := b.userInfo
        host := b.host.getD default
        port := b.port
      }
    else none

  let path : Path := {
    segments := b.pathSegments.map EncodedSegment.encode
    absolute := true
  }

  let query :=
    b.query.map fun (k, v) =>
      (EncodedQueryParam.encode k, v.map EncodedQueryParam.encode)

  let query := URI.Query.ofList query.toList

  {
    scheme := ⟨scheme.toLower, IsLowerCase.isLowerCase_toLower⟩
    authority := authority
    path
    query := query
    fragment := b.fragment
  }

end Builder

end URI

namespace URI

/--
Returns a new URI with the scheme replaced.
-/
def withScheme (uri : URI) (scheme : String) : URI :=
  { uri with scheme := ⟨scheme.toLower, IsLowerCase.isLowerCase_toLower⟩ }

/--
Returns a new URI with the authority replaced.
-/
def withAuthority (uri : URI) (authority : Option URI.Authority) : URI :=
  { uri with authority }

/--
Returns a new URI with the path replaced.
-/
def withPath (uri : URI) (path : URI.Path) : URI :=
  { uri with path }

/--
Returns a new URI with the query replaced.
-/
def withQuery (uri : URI) (query : URI.Query) : URI :=
  { uri with query }

/--
Returns a new URI with the fragment replaced.
-/
def withFragment (uri : URI) (fragment : Option String) : URI :=
  { uri with fragment }

/--
Normalizes a URI according to RFC 3986 Section 6.
-/
def normalize (uri : URI) : URI :=
  { uri with
    scheme := uri.scheme
    authority := uri.authority
    path := uri.path.normalize
  }

end URI

/--
HTTP request target forms as defined in RFC 7230 Section 5.3.

Reference: https://www.rfc-editor.org/rfc/rfc7230.html#section-5.3
-/
inductive RequestTarget where
  /--
  Origin-form request target (most common for HTTP requests). Consists of a path and an optional query string.
  Example: `/path/to/resource?key=value`
  -/
  | originForm (path : URI.Path) (query : Option URI.Query)

  /--
  Absolute-form request target containing a complete URI. Used when making requests through a proxy.
  Example: `http://example.com:8080/path?key=value`
  -/
  | absoluteForm (uri : URI) (noFrag : uri.fragment.isNone)

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
  | .originForm p _ => p
  | .absoluteForm u _ => u.path
  | _ => { segments := #[], absolute := false }

/--
Extracts the query component from a request target, if available.
Returns an empty array for targets without a query.
-/
def query : RequestTarget → URI.Query
  | .originForm _ q => q.getD URI.Query.empty
  | .absoluteForm u _ => u.query
  | _ => URI.Query.empty

/--
Extracts the authority component from a request target, if available.
-/
def authority? : RequestTarget → Option URI.Authority
  | .authorityForm a => some a
  | .absoluteForm u _ => u.authority
  | _ => none

/--
Extracts the fragment component from a request target, if available.
-/
def fragment? : RequestTarget → Option String
  | .originForm _ _ => none
  | .absoluteForm u _ => u.fragment
  | _ => none

/--
Extracts the full URI if the request target is in absolute form.
-/
def uri? : RequestTarget → Option URI
  | .absoluteForm u _ => some u
  | _ => none

instance : ToString RequestTarget where
  toString
    | .originForm path query =>
        let pathStr := toString path
        let queryStr := query.map toString |>.getD ""
        s!"{pathStr}{queryStr}"
    | .absoluteForm uri _ => toString uri
    | .authorityForm auth => toString auth
    | .asteriskForm => "*"

instance : Encode .v11 RequestTarget where
  encode buffer target := buffer.writeString (toString target)

end Std.Http.RequestTarget
