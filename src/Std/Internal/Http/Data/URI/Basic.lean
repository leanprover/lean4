/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
import Init.Data.ToString
public import Std.Net
public import Std.Internal.Http.Internal
public import Std.Internal.Http.Data.URI.Encoding
public import Init.Data.String.Search

public section

/-!
# URI Structure

This module defines an HTTP-oriented URI structure aligned with RFC 3986 and RFC 9110, including
schemes, authorities, paths, queries, fragments, and request targets.

Host handling is intentionally strict: this module accepts IPv4, bracketed IPv6, and DNS-style
domain names (LDH labels). RFC 3986 `reg-name` forms that are not DNS-compatible are rejected.

All text components use the encoding types from `Std.Http.URI.Encoding` to ensure proper
percent-encoding is maintained throughout.

References:
* https://www.rfc-editor.org/rfc/rfc3986.html
* https://www.rfc-editor.org/rfc/rfc9110.html#name-uri-references
-/

namespace Std.Http

set_option linter.all true

open Internal Char

namespace URI

/--
Proposition that `s` is a valid URI scheme per RFC 3986:
`scheme = ALPHA *( ALPHA / DIGIT / "+" / "-" / "." )`.

The scheme value stored in this module is normalized to lowercase.

Reference: https://www.rfc-editor.org/rfc/rfc3986.html#section-3.1
-/
abbrev IsValidScheme (s : String) : Prop :=
  IsLowerCase s ∧
  s.toList.all isValidSchemeChar ∧
  (s.toList.head?.map isAlpha |>.getD false) -- first character must be ALPHA

/--
URI scheme identifier (e.g., "http", "https", "ftp").
-/
abbrev Scheme := { s : String // IsValidScheme s }

instance : Inhabited Scheme where
  default := ⟨"http", ⟨by decide, by decide, by decide⟩⟩

namespace Scheme

/--
Attempts to create a `Scheme` from a string, normalizing to lowercase.
Returns `none` if the scheme is invalid per RFC 3986 Section 3.1.
-/
def ofString? (s : String) : Option Scheme :=
  let lower := s.toLower

  if h : IsValidScheme lower then
    some ⟨lower, h⟩
  else
    none

/--
Creates a `Scheme` from a string, normalizing to lowercase. Panics if invalid.
-/
def ofString! (s : String) : Scheme :=
  match ofString? s with
  | some scheme => scheme
  | none => panic! s!"invalid URI scheme: {s.quote}"

/--
Returns the default port number for this URI scheme: 443 for `https`, 80 for everything else.
-/
def defaultPort (scheme : URI.Scheme) : UInt16 :=
  if scheme.val == "https" then 443 else 80

/--
Returns the URI scheme for a given port: `"https"` for 443, `"http"` otherwise.
-/
def ofPort (port : UInt16) : URI.Scheme :=
  if port == 443 then ⟨"https", by decide⟩ else ⟨"http", by decide⟩

end Scheme

/--
User information component containing an encoded username and optional encoded password.

The stored strings use URI userinfo percent-encoding so parsed URIs can be rendered without
losing percent-encoding choices (for example, `%3A` versus `:`).

Note: embedding passwords in URIs is deprecated per RFC 9110 Section 4.2.4. Avoid using the
password field in new code, and never include it in logs or error messages.

Reference: https://www.rfc-editor.org/rfc/rfc3986.html#section-3.2.1
-/
structure UserInfo where
  /--
  The encoded username.
  -/
  username : EncodedUserInfo

  /--
  The optional encoded password.
  -/
  password : Option EncodedUserInfo
deriving Inhabited, Repr, BEq

namespace UserInfo

/--
Builds a `UserInfo` value from raw strings by applying userinfo percent-encoding.
-/
@[inline]
def ofStrings (username : String) (password : Option String := none) : UserInfo where
  username := EncodedUserInfo.encode username
  password := EncodedUserInfo.encode <$> password

/--
Returns the decoded username, or `none` if decoding fails UTF-8 validation.
-/
@[inline]
def username? (ui : UserInfo) : Option String :=
  ui.username.decode

/--
Returns the decoded password when present, or `none` if absent or decoding fails UTF-8 validation.
-/
@[inline]
def password? (ui : UserInfo) : Option String :=
  ui.password.bind EncodedUserInfo.decode

end UserInfo

/--
Checks whether a single domain label is valid. A label must be non-empty, contain only ASCII
alphanumeric characters and `-`, cannot start or end with `-`, and must be at most 63 characters.

References:
* https://www.rfc-editor.org/rfc/rfc1034.html#section-3.5
* https://www.rfc-editor.org/rfc/rfc1123.html#section-2.1
-/
def isValidDomainLabel (s : String) : Bool :=
  let chars := s.toList
  decide (chars.length ≤ 63) &&
    chars.all (fun c => isAsciiAlphaNumChar c ∨ c = '-') &&
    (chars.head?.map isAsciiAlphaNumChar |>.getD false) &&
    (chars.getLast?.map isAsciiAlphaNumChar |>.getD false)

/--
Proposition that asserts `s` is a valid dot-separated domain name.
Each label must satisfy `IsValidDomainLabel`, and the full name must be at most 255 characters.
-/
abbrev IsValidDomainName (s : String) : Prop :=
  let labels := s.split '.'
  ¬labels.isEmpty ∧ labels.all (fun s => isValidDomainLabel s.copy) ∧ s.length ≤ 255

/--
A domain name represented as a validated, lowercase-normalized string.
Only ASCII alphanumeric characters, hyphens, and dots are allowed.
Each label cannot start or end with `-` and is limited to 63 characters.
Internationalized domain names must be converted to punycode before use.

Reference: https://www.rfc-editor.org/rfc/rfc3986.html#section-3.2.2
-/
abbrev DomainName := { s : String // IsLowerCase s ∧ IsValidDomainName s ∧ ¬s.isEmpty }

namespace DomainName

/--
Attempts to create a normalized domain name from a string.
Returns `none` if the name is empty, longer than 255 characters, or any label violates DNS label
constraints.
-/
def ofString? (s : String) : Option DomainName :=
  let lower := s.toLower
  if h₁ : lower.isEmpty then
    none
  else if h₃ : IsValidDomainName lower then
    some ⟨lower, IsLowerCase.isLowerCase_toLower, h₃, h₁⟩
  else
    none

end DomainName

/--
Host component of a URI, supporting domain names and IP addresses.

Reference: https://www.rfc-editor.org/rfc/rfc3986.html#section-3.2.2
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
deriving Inhabited, BEq

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
Authority port representation, preserving the distinction between:
* no port separator (`example.com`)
* empty port (`example.com:`)
* numeric port (`example.com:443`)
-/
inductive Port where
  /--
  No `:` port separator is present (for example, `example.com`).
  -/
  | omitted

  /--
  A `:` port separator is present with no digits after it (for example, `example.com:`).
  -/
  | empty

  /--
  A numeric port value is present (for example, `example.com:443`).
  -/
  | value (port : UInt16)
deriving Inhabited, Repr, DecidableEq

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
  Port component, preserving whether it is omitted (`example.com`),
  explicitly empty (`example.com:`), or numeric (`example.com:443`).
  -/
  port : Port := .omitted
deriving Inhabited, Repr, BEq

instance : ToString Authority where
  toString auth :=
    let userPart := match auth.userInfo with
      | none => ""
      | some ⟨name, some pass⟩ => s!"{name}:{pass}@"
      | some ⟨name, none⟩ => s!"{name}@"
    let hostPart := toString auth.host
    let portPart := match auth.port with
      | .omitted => ""
      | .empty => ":"
      | .value p => s!":{p}"
    s!"{userPart}{hostPart}{portPart}"

/--
Hierarchical path component of a URI. Each segment is stored as an `EncodedSegment` to maintain
proper percent-encoding.

Reference: https://www.rfc-editor.org/rfc/rfc3986.html#section-3.3
-/
structure Path where
  /--
  The path segments making up the hierarchical structure (each segment is percent-encoded).
  -/
  segments : Array EncodedSegment

  /--
  Whether the path is absolute (begins with '/') or relative.
  -/
  absolute : Bool
deriving Inhabited, Repr, BEq

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

Reference: https://www.rfc-editor.org/rfc/rfc3986.html#section-3.4
-/
@[expose]
def Query := Array (EncodedQueryParam × Option EncodedQueryParam)
deriving Repr, Inhabited, BEq

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
def findEncoded? (query : Query) (key : EncodedQueryParam) : Option (Option EncodedQueryParam) :=
  let matchingKey := Array.find? (fun x => x.fst.toByteArray = key.toByteArray) query
  matchingKey.map (fun x => x.snd)

/--
Finds the first value of a query parameter by raw key string. The key is percent-encoded before
matching. This avoids aliasing between raw and pre-encoded spellings.
-/
def find? (query : Query) (key : String) : Option (Option EncodedQueryParam) :=
  query.findEncoded? (EncodedQueryParam.encode key)

/--
Finds all values of a query parameter by key name. Returns an empty array if the key is not found.
The values remain encoded as `EncodedQueryParam`.
-/
def findAllEncoded (query : Query) (key : EncodedQueryParam) : Array (Option EncodedQueryParam) :=
  query.filterMap (fun x =>
    if x.fst.toByteArray = key.toByteArray then
      some x.snd
    else
      none)

/--
Finds all values of a query parameter by raw key string. The key is percent-encoded before matching.
-/
def findAll (query : Query) (key : String) : Array (Option EncodedQueryParam) :=
  query.findAllEncoded (EncodedQueryParam.encode key)

/--
Adds a query parameter to the query string.
-/
def insert (query : Query) (key : String) (value : String) : Query :=
  let encodedKey : EncodedQueryParam := EncodedQueryParam.encode key
  let encodedValue : EncodedQueryParam := EncodedQueryParam.encode value
  query.push (encodedKey, some encodedValue)

/--
Adds an already-encoded key-value pair to the query string.
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
def containsEncoded (query : Query) (key : EncodedQueryParam) : Bool :=
  query.any (fun x => x.fst.toByteArray = key.toByteArray)

/--
Checks if a query parameter exists by raw key string. The key is percent-encoded before matching.
-/
def contains (query : Query) (key : String) : Bool :=
  query.containsEncoded (EncodedQueryParam.encode key)

/--
Removes all occurrences of a query parameter by key name.
-/
def eraseEncoded (query : Query) (key : EncodedQueryParam) : Query :=
  query.filter (fun x =>
    x.fst.toByteArray ≠ key.toByteArray
  )

/--
Removes all occurrences of a query parameter by raw key string. The key is percent-encoded before matching.
-/
def erase (query : Query) (key : String) : Query :=
  query.eraseEncoded (EncodedQueryParam.encode key)

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
deriving Repr, Inhabited, BEq

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
  scheme : Option URI.Scheme := none

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
  port : URI.Port := .omitted

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
Attempts to set the URI scheme (e.g., "http", "https").
Returns `none` if the scheme is not a valid RFC 3986 scheme.
The stored scheme is normalized to lowercase.
-/
def setScheme? (b : Builder) (scheme : String) : Option Builder :=
  URI.Scheme.ofString? scheme |>.map (fun scheme => { b with scheme := some scheme })

/--
Sets the URI scheme (e.g., "http", "https"). Panics if the scheme is invalid.
Use `setScheme?` if you need a safe option-returning version.
-/
def setScheme! (b : Builder) (scheme : String) : Builder :=
  match b.setScheme? scheme with
  | some b => b
  | none   => panic! s!"invalid URI scheme: {scheme.quote}"

/--
Sets the user information with username and optional password.
The strings will be automatically percent-encoded.
-/
def setUserInfo (b : Builder) (username : String) (password : Option String := none) : Builder :=
  { b with userInfo := some (UserInfo.ofStrings username password) }

/--
Sets the host as a domain name, returning `none` if the name contains invalid characters.
The domain name will be automatically lowercased.
Only ASCII alphanumeric characters, hyphens, and dots are allowed.
Each label cannot start or end with `-` and is limited to 63 characters.
Internationalized domain names must be converted to punycode before use.
-/
def setHost? (b : Builder) (name : String) : Option Builder :=
  URI.DomainName.ofString? name |>.map (fun name => { b with host := some (Host.name name) })

/--
Sets the host as a domain name, panicking if the name contains invalid characters.
The domain name will be automatically lowercased.
Only ASCII alphanumeric characters, hyphens, and dots are allowed.
Each label cannot start or end with `-` and is limited to 63 characters.
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
def setPort (b : Builder) (port : UInt16) : Builder :=
  { b with port := .value port }

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
  let scheme := (b.scheme.getD ⟨"https", by decide⟩)

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
    scheme
    authority := authority
    path
    query := query
    fragment := b.fragment
  }

end Builder

/--
Returns a new URI with the scheme replaced.
-/
def withScheme! (uri : URI) (scheme : String) : URI :=
  { uri with scheme := URI.Scheme.ofString! scheme }

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
Partially normalizes a URI by removing dot-segments from the path (`.` and `..`)
according to RFC 3986 Section 5.2.4.

This does not apply the full normalization set from RFC 3986 Section 6 — for example,
case normalization, percent-encoding normalization, and default-port normalization are
not performed.
-/
def normalize (uri : URI) : URI :=
  { uri with path := uri.path.normalize }

end URI

/--
HTTP request target forms as defined in RFC 9112 Section 3.3.

Reference: https://www.rfc-editor.org/rfc/rfc9112.html#section-3.3
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
  | .originForm p _ => p
  | .absoluteForm uri => uri.path
  | _ => { segments := #[], absolute := false }

/--
Extracts the query component from a request target, if available.
Returns an empty array for targets without a query.
-/
def query : RequestTarget → URI.Query
  | .originForm _ q => q.getD URI.Query.empty
  | .absoluteForm uri => uri.query
  | _ => URI.Query.empty

/--
Extracts the authority component from a request target, if available.
-/
def authority? : RequestTarget → Option URI.Authority
  | .authorityForm a => some a
  | .absoluteForm uri => uri.authority
  | _ => none

instance : ToString RequestTarget where
  toString
    | .originForm path query =>
        let pathStr := toString path
        let queryStr := query.map toString |>.getD ""
        s!"{pathStr}{queryStr}"
    | .absoluteForm uri => toString uri
    | .authorityForm auth => toString auth
    | .asteriskForm => "*"

instance : Encode .v11 RequestTarget where
  encode buffer target := buffer.writeString (toString target)

end Std.Http.RequestTarget
