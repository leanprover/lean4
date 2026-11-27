/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Sync.Mutex
public import Std.Http.Data.Cookie
public import Std.Http.Data.Headers
import Init.Data.String.Search
import Init.Data.Array.QSort

public section

/-!
# Cookie store and jar

`Cookie.Store` is the cookie store of RFC 6265 §5.3 as a pure value: it takes the current time as
an argument, so its decisions can be tested without a clock. `Cookie.Jar` keeps a store behind a
mutex and reads the wall clock, for a client to share between requests.

The store refuses a `Domain` attribute that is a public suffix, as §5.3 step 5 allows, so that one
site cannot set a cookie for every site under `com`. Without a public-suffix list it treats every
single-label domain as one; `isPublicSuffix` takes a real list.

Reference: https://www.rfc-editor.org/rfc/rfc6265#section-5.3
-/

namespace Std.Http.Cookie

set_option linter.all true

open Std.Time

/--
A cookie store (RFC 6265 §5.3), with the limits of §6.1.
-/
structure Store where
  /--
  The cookies, in no particular order.
  -/
  cookies : Array Cookie := #[]

  /--
  The most cookies the store keeps; past it, the least recently used go first.
  -/
  maxCookies : Nat := 3000

  /--
  The most cookies the store keeps for one domain; past it, that domain's least recently used go
  first.
  -/
  maxPerDomain : Nat := 50

  /--
  The longest `Set-Cookie` value, in bytes, the store accepts; longer ones are dropped.
  -/
  maxCookieSize : Nat := 4096

  /--
  Whether a domain is a public suffix, under which no site may set a cookie for others.
  -/
  isPublicSuffix : String → Bool := fun domain => !domain.contains '.'

namespace Store

/-- The path of a request target, as RFC 6265 compares it: `/` for an empty path. -/
private def requestPath (target : RequestTarget) : String :=
  match toString target.path with
  | "" => "/"
  | path => path

@[inline] private def isExpired (now : Timestamp) (cookie : Cookie) : Bool :=
  cookie.expiry.any (· ≤ now)

@[inline] private def sameKey (a b : Cookie) : Bool :=
  a.name == b.name && a.domain == b.domain && a.path == b.path

/-- Whether `a` goes before `b` when evicting: used less recently, then created earlier. -/
@[inline] private def evictsBefore (a b : Cookie) : Bool :=
  a.lastAccess < b.lastAccess || (a.lastAccess == b.lastAccess && a.creation < b.creation)

/-- Removes the cookie of `cookies` that `evictsBefore` all others, among those `pick` selects. -/
private def evictOne (cookies : Array Cookie) (pick : Cookie → Bool) : Array Cookie :=
  let victim := cookies.foldl (init := none) fun victim c =>
    if !pick c then victim
    else match victim with
      | some v => if evictsBefore c v then some c else some v
      | none => some c
  match victim with
  | some v => cookies.filter (!sameKey · v)
  | none => cookies

/--
Evicts what RFC 6265 §5.3 asks: every expired cookie, then the least recently used of `domain`
past `maxPerDomain`, then the least recently used of all past `maxCookies`.
-/
private def evict (store : Store) (now : Timestamp) (domain : String) : Store :=
  let cookies := store.cookies.filter (!isExpired now ·)
  let perDomain := cookies.foldl (fun n c => if c.domain == domain then n + 1 else n) 0
  let cookies := (List.range (perDomain - store.maxPerDomain)).foldl
    (fun cookies _ => evictOne cookies (·.domain == domain)) cookies
  let cookies := (List.range (cookies.size - store.maxCookies)).foldl
    (fun cookies _ => evictOne cookies fun _ => true) cookies
  { store with cookies }

/--
Stores the cookie of one `Set-Cookie` header value, received at `now` in the response to a
request for `target` at `origin` (RFC 6265 §5.3). A header that does not parse, is longer than
`maxCookieSize`, or has a `Domain` the host does not domain-match or that is a public suffix other
than the host itself, is ignored. A cookie with the name, domain and path of a stored one replaces
it and keeps its creation time; an expired one only removes it.
-/
def receive (store : Store) (now : Timestamp) (origin : URI.Origin) (target : RequestTarget)
    (header : String) : Store := Id.run do
  if header.utf8ByteSize > store.maxCookieSize then return store
  let some parsed := parseSetCookie header | return store
  let host := origin.host
  let hostName := toString host
  let domainAttribute := parsed.domain.getD ""
  -- `some none`: host-only; `some (some d)`: domain `d`; `none`: the cookie is ignored.
  let domain? : Option (Option String) :=
    if domainAttribute.isEmpty then some none
    else if store.isPublicSuffix domainAttribute then
      if domainAttribute == hostName then some none else none
    else if domainMatch host domainAttribute then some (some domainAttribute)
    else none
  let some domain := domain? | return store
  let cookie : Cookie := {
    name := parsed.name
    value := parsed.value
    domain := domain.getD hostName
    path := parsed.path.getD (defaultPath (requestPath target))
    -- RFC 6265 §5.3 step 3: `Max-Age` wins over `Expires`.
    expiry := match parsed.maxAge with
      | some seconds => some (now.addSeconds (.ofInt seconds))
      | none => parsed.expires
    creation := now
    lastAccess := now
    hostOnly := domain.isNone
    secure := parsed.secure
    httpOnly := parsed.httpOnly }
  let cookie := match store.cookies.find? (sameKey · cookie) with
    | some old => { cookie with creation := old.creation }
    | none => cookie
  let cookies := store.cookies.filter (!sameKey · cookie)
  let cookies := if isExpired now cookie then cookies else cookies.push cookie
  return { store with cookies }.evict now cookie.domain

/-- Stores the cookies of every `Set-Cookie` field in `headers`, in order (see `receive`). -/
def receiveAll (store : Store) (now : Timestamp) (origin : URI.Origin) (target : RequestTarget)
    (headers : Headers) : Store :=
  match headers.getAll? .setCookie with
  | some values => values.foldl (fun store value => store.receive now origin target value.value) store
  | none => store

/--
The `Cookie` header for a request for `target` at `origin` at `now` (RFC 6265 §5.4), or `none`
when no cookie applies. A cookie applies when the host is its domain (or domain-matches it, unless
it is host-only), the path path-matches its path, and the channel is `https` if it is secure.
Longer paths go first, then older cookies. The store returned drops expired cookies and records
the access of those sent.
-/
def header (store : Store) (now : Timestamp) (origin : URI.Origin) (target : RequestTarget) :
    Store × Option Header.Value :=
  let host := origin.host
  let hostName := toString host
  let path := requestPath target
  let secure := origin.scheme.val == "https"
  let applies (c : Cookie) :=
    (if c.hostOnly then hostName == c.domain else domainMatch host c.domain) &&
      pathMatch path c.path && (!c.secure || secure)
  let cookies := store.cookies.filter (!isExpired now ·)
  let cookies := cookies.map fun c => if applies c then { c with lastAccess := now } else c
  let sent := (cookies.filter applies).qsort fun a b =>
    a.path.utf8ByteSize > b.path.utf8ByteSize ||
      (a.path.utf8ByteSize == b.path.utf8ByteSize && a.creation < b.creation)
  let value :=
    if sent.isEmpty then none
    else Header.Value.ofString? ("; ".intercalate (sent.map (fun c => c.name ++ "=" ++ c.value)).toList)
  ({ store with cookies }, value)

end Store

/--
A cookie store shared between requests: a `Store` behind a mutex, on the wall clock.
-/
structure Jar where
  private mk ::
  private state : Mutex Store

namespace Jar

/-- Creates a jar holding `store`, by default an empty store with the default limits. -/
def new (store : Store := {}) : BaseIO Jar :=
  return .mk (← Mutex.new store)

/--
Stores the cookies of the `Set-Cookie` fields of a response to a request for `target` at `origin`.
-/
def store (jar : Jar) (origin : URI.Origin) (target : RequestTarget) (headers : Headers) :
    IO Unit := do
  let now ← Timestamp.now
  jar.state.atomically (modify (·.receiveAll now origin target headers))

/--
The `Cookie` header values for a request for `target` at `origin`: one value, or none when no
cookie applies.
-/
def load (jar : Jar) (origin : URI.Origin) (target : RequestTarget) : IO (Array Header.Value) := do
  let now ← Timestamp.now
  jar.state.atomically do
    let (store, value) := (← get).header now origin target
    set store
    return value.toArray

/-- The store the jar holds now. -/
def snapshot (jar : Jar) : BaseIO Store :=
  jar.state.atomically get

end Std.Http.Cookie.Jar
