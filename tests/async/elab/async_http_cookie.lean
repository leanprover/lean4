import Std.Http

open Std Http
open Std.Http.Client Std.Async

/-!
Tests `Std.Http.Cookie` against the user-agent algorithms of RFC 6265: the `Set-Cookie` parser
(§5.2), the cookie-date parser (§5.1.1), domain and path matching (§5.1.3, §5.1.4), the storage
model (§5.3) and the `Cookie` header (§5.4), all through `Cookie.Store` with an explicit clock;
`Cookie.Jar`, its thread-safe wrapper on the wall clock; and the client's `CookieHandler`, including
`CookieHandler.ofJar`.
-/

def ts (s : Int) : Std.Time.Timestamp := .ofSecondsSinceUnixEpoch (.ofInt s)

def t0 : Std.Time.Timestamp := ts 1700000000

def origin (url : String) : URI.Origin :=
  (URI.parse! url).origin?.getD { scheme := URI.Scheme.ofString! "http", host := .empty, port := 0 }

def hostOf (name : String) : URI.Host := (URI.parse! s!"http://{name}/").host?.get!

def target (path : String) : RequestTarget := RequestTarget.parse! path

def receive (store : Cookie.Store) (url path setCookie : String) (now := t0) : Cookie.Store :=
  store.receive now (origin url) (target path) setCookie

/-- The `Cookie` header for a request, or `""` when no cookie is sent. -/
def header (store : Cookie.Store) (url path : String) (now := t0) : String :=
  ((store.header now (origin url) (target path)).2.map (·.value)).getD ""

def parsed (s : String) : Option Cookie.SetCookie := Cookie.parseSetCookie s

/-! ## §5.2: the `Set-Cookie` header -/

#guard (parsed "SID=31d4d96e407aad42").map (fun c => (c.name, c.value)) == some ("SID", "31d4d96e407aad42")

-- A user agent takes any value up to `;`, and trims whitespace around the name and the value.
#guard (parsed " a b = x, y z ; Path=/").map (fun c => (c.name, c.value)) == some ("a b", "x, y z")
#guard (parsed "q=\"quoted\"").map (·.value) == some "\"quoted\""
#guard (parsed "e=").map (·.value) == some ""
#guard (parsed "e==x").map (fun c => (c.name, c.value)) == some ("e", "=x")

-- No `=` in the name-value pair, or an empty name: the whole header is ignored.
#guard parsed "novalue" == none
#guard parsed "novalue; Path=/" == none
#guard parsed "=v" == none
#guard parsed "  =v" == none

-- Attribute names are case-insensitive, and the last occurrence wins.
#guard (parsed "a=1; pATh=/x; PATH=/y; domain=A.example; DOMAIN=.B.Example").map
  (fun c => (c.path, c.domain)) == some (some "/y", some "b.example")
#guard (parsed "a=1; Secure; HTTPONLY").map (fun c => (c.secure, c.httpOnly)) == some (true, true)
#guard (parsed "a=1; Secure=yes").map (·.secure) == some true

-- An empty `Domain` is ignored; a `Path` that does not start with `/` leaves the default.
#guard (parsed "a=1; Domain=; Domain").map (·.domain) == some none
#guard (parsed "a=1; Path=x/y").map (·.path) == some none
#guard (parsed "a=1; Path=").map (·.path) == some none

-- `Max-Age` needs a DIGIT or `-` first and DIGITs after it; otherwise it is ignored.
#guard (parsed "a=1; Max-Age=3600").map (·.maxAge) == some (some 3600)
#guard (parsed "a=1; Max-Age=-5").map (·.maxAge) == some (some (-5))
#guard ["", "-", "+5", "5s", " 5x", "1.5"].all fun v => (parsed s!"a=1; Max-Age={v}").map (·.maxAge) == some none
#guard (parsed "a=1; Max-Age=10; Max-Age=bad").map (·.maxAge) == some (some 10)

-- An `Expires` that is no cookie-date is ignored.
#guard (parsed "a=1; Expires=tomorrow").map (·.expires) == some none

/-! ## §5.1.1: cookie dates -/

def sunday1994 : Std.Time.Timestamp := ts 784111777  -- 1994-11-06 08:49:37 UTC

#guard Cookie.parseDate "Sun, 06 Nov 1994 08:49:37 GMT" == some sunday1994
#guard Cookie.parseDate "Sunday, 06-Nov-94 08:49:37 GMT" == some sunday1994
#guard Cookie.parseDate "Sun Nov  6 08:49:37 1994" == some sunday1994
#guard Cookie.parseDate "06 nov 1994 8:49:37" == some sunday1994
#guard Cookie.parseDate "Wed, 09 Jun 2021 10:18:14 GMT" == some (ts 1623233894)
-- Two-digit years: 70–99 are 19xx, 00–69 are 20xx.
#guard Cookie.parseDate "01 Jan 70 00:00:00" == some (ts 0)
#guard Cookie.parseDate "01 Jan 69 00:00:00" == some (ts 3124224000)
-- A month token is matched by its first three letters.
#guard Cookie.parseDate "1 January 2000 00:00:00" == some (ts 946684800)

-- No time, no month, a day out of range, a year before 1601, an hour past 23, a date that does not
-- exist: no date.
#guard ["Sun, 06 Nov 1994", "06 1994 08:49:37", "32 Nov 1994 08:49:37", "01 Jan 1600 00:00:00",
  "01 Jan 2000 24:00:00", "01 Jan 2000 00:60:00", "30 Feb 2001 00:00:00", "29 Feb 2001 00:00:00",
  ""].all (Cookie.parseDate · == none)
#guard (Cookie.parseDate "29 Feb 2000 00:00:00").isSome

/-! ## §5.1.3, §5.1.4: domain and path matching -/

#guard Cookie.domainMatch (hostOf "a.example.com") "example.com"
#guard Cookie.domainMatch (hostOf "example.com") "example.com"
#guard !Cookie.domainMatch (hostOf "badexample.com") "example.com"
#guard !Cookie.domainMatch (hostOf "example.com") "a.example.com"
-- An IP address only matches itself.
#guard Cookie.domainMatch (hostOf "10.0.0.1") "10.0.0.1"
#guard !Cookie.domainMatch (hostOf "10.0.0.1") "0.0.1"

#guard [("", "/"), ("x", "/"), ("/", "/"), ("/a", "/"), ("/a/b", "/a"), ("/a/b/", "/a/b")].all
  fun (p, d) => Cookie.defaultPath p == d

#guard Cookie.pathMatch "/a" "/a"
#guard Cookie.pathMatch "/a/b" "/a"
#guard Cookie.pathMatch "/a/b" "/a/"
#guard Cookie.pathMatch "/anything" "/"
#guard !Cookie.pathMatch "/ab" "/a"
#guard !Cookie.pathMatch "/a" "/a/b"

/-! ## §5.3, §5.4: storing cookies and sending them back -/

-- A cookie without `Domain` is host-only: sent to the host that set it, not to its subdomains.
#guard
  let s := receive {} "https://example.com" "/" "a=1"
  header s "https://example.com" "/" == "a=1" && header s "https://www.example.com" "/" == ""

-- With `Domain`, subdomains get it too.
#guard
  let s := receive {} "https://www.example.com" "/" "a=1; Domain=example.com"
  header s "https://example.com" "/" == "a=1" && header s "https://x.www.example.com" "/" == "a=1"

-- A `Domain` the host does not domain-match is refused, and so is a public suffix: a single label
-- by default.
#guard (receive {} "https://www.example.com" "/" "a=1; Domain=other.com").cookies.isEmpty
#guard (receive {} "https://www.example.com" "/" "a=1; Domain=com").cookies.isEmpty
-- A public suffix the host is itself becomes host-only.
#guard
  let s := receive {} "http://localhost" "/" "a=1; Domain=localhost"
  header s "http://localhost" "/" == "a=1" && s.cookies.all (·.hostOnly)
-- A custom public-suffix list.
#guard
  let st : Cookie.Store := { isPublicSuffix := fun d => d == "co.uk" || !d.contains '.' }
  (receive st "https://a.co.uk" "/" "a=1; Domain=co.uk").cookies.isEmpty &&
    !(receive st "https://a.example.co.uk" "/" "a=1; Domain=example.co.uk").cookies.isEmpty

-- No `Path`: the directory of the request path.
#guard
  let s := receive {} "https://example.com" "/app/login" "sid=1"
  header s "https://example.com" "/app/profile" == "sid=1" && header s "https://example.com" "/other" == ""

-- `Secure` cookies only go out over https.
#guard
  let s := receive {} "https://example.com" "/" "a=1; Secure"
  header s "https://example.com" "/" == "a=1" && header s "http://example.com" "/" == ""

-- Longer paths first; equal lengths in creation order.
#guard
  let s := receive {} "https://example.com" "/" "a=1; Path=/"
  let s := receive s "https://example.com" "/" "b=2; Path=/x/y" (now := ts 1700000001)
  let s := receive s "https://example.com" "/" "c=3; Path=/x" (now := ts 1700000002)
  let s := receive s "https://example.com" "/" "d=4; Path=/" (now := ts 1700000003)
  header s "https://example.com" "/x/y/z" == "b=2; c=3; a=1; d=4"

-- Same name, domain and path: replaced, keeping its creation time and so its place.
#guard
  let s := receive {} "https://example.com" "/" "a=1"
  let s := receive s "https://example.com" "/" "b=2" (now := ts 1700000001)
  let s := receive s "https://example.com" "/" "a=3" (now := ts 1700000002)
  header s "https://example.com" "/" == "a=3; b=2" && s.cookies.size == 2

-- Expiry: `Max-Age` wins over `Expires`; an expired cookie is never sent and is dropped.
#guard
  let s := receive {} "https://example.com" "/"
    "a=1; Expires=Wed, 09 Jun 2021 10:18:14 GMT; Max-Age=60"
  header s "https://example.com" "/" (now := ts 1700000059) == "a=1" &&
    header s "https://example.com" "/" (now := ts 1700000060) == ""
#guard
  let s := receive {} "https://example.com" "/" "a=1; Expires=Wed, 09 Jun 2021 10:18:14 GMT"
  s.cookies.isEmpty
#guard
  let s := receive {} "https://example.com" "/" "a=1; Max-Age=60"
  let (s, _) := s.header (ts 1700000100) (origin "https://example.com") (target "/")
  s.cookies.isEmpty

-- `Max-Age=0` deletes the stored cookie.
#guard
  let s := receive {} "https://example.com" "/" "a=1"
  (receive s "https://example.com" "/" "a=; Max-Age=0").cookies.isEmpty

-- Sending updates the last-access time.
#guard
  let s := receive {} "https://example.com" "/" "a=1"
  let (s, _) := s.header (ts 1700000500) (origin "https://example.com") (target "/")
  s.cookies.all (·.lastAccess == ts 1700000500)

/-! ## Limits -/

-- Past `maxPerDomain`, the cookie of that domain used least recently goes.
#guard
  let st : Cookie.Store := { maxPerDomain := 2 }
  let s := receive st "https://example.com" "/" "a=1"
  let s := receive s "https://example.com" "/" "b=2" (now := ts 1700000001)
  let (s, _) := s.header (ts 1700000002) (origin "https://example.com") (target "/")
  let s := receive s "https://example.com" "/" "c=3" (now := ts 1700000003)
  -- `a` and `b` were both read at 1700000002; `a` was created first, so it goes.
  s.cookies.size == 2 && header s "https://example.com" "/" (now := ts 1700000004) == "b=2; c=3"

-- Past `maxCookies`, the least recently used cookie of any domain goes.
#guard
  let st : Cookie.Store := { maxCookies := 2 }
  let s := receive st "https://a.example" "/" "a=1"
  let s := receive s "https://b.example" "/" "b=2" (now := ts 1700000001)
  let s := receive s "https://c.example" "/" "c=3" (now := ts 1700000002)
  s.cookies.size == 2 && header s "https://a.example" "/" (now := ts 1700000003) == ""

-- A `Set-Cookie` longer than `maxCookieSize` is dropped.
#guard (receive { maxCookieSize := 16 } "https://example.com" "/" "a=0123456789abcdef").cookies.isEmpty
#guard !(receive { maxCookieSize := 16 } "https://example.com" "/" "a=0123456789").cookies.isEmpty

/-! ## `Cookie.Store.receiveAll` and `Cookie.Jar` -/

#guard
  let headers := Headers.empty
    |>.insert .setCookie (.mk "a=1") |>.insert .setCookie (.mk "b=2; Path=/x")
  let s := ({} : Cookie.Store).receiveAll t0 (origin "https://example.com") (target "/") headers
  header s "https://example.com" "/x" == "b=2; a=1"

#eval show IO Unit from do
  let jar ← Cookie.Jar.new
  jar.store (origin "https://example.com") (target "/login")
    (Headers.empty |>.insert .setCookie (.mk "sid=abc; Path=/; HttpOnly"))
  let values ← jar.load (origin "https://example.com") (target "/account")
  unless values.map (·.value) == #["sid=abc"] do
    throw <| IO.userError s!"jar: unexpected Cookie header {values.map (·.value)}"
  let none ← jar.load (origin "https://other.example") (target "/")
  unless none.isEmpty do
    throw <| IO.userError "jar: a cookie went to another host"

/-! ## `CookieHandler` -/

-- A handler observes `store` and replays what it recorded from `load`.
#eval show IO Unit from do
  let jar ← IO.mkRef (#[] : Array Header.Value)
  let handler : CookieHandler :=
    { load := fun _ _ => return (← jar.get),
      store := fun _ _ headers => jar.modify (· ++ (headers.getAll? .setCookie).getD #[]) }
  let response := (Headers.empty.insert .setCookie (.mk "a=1")).insert .setCookie (.mk "b=2")
  handler.store (origin "http://example.com") (target "/") response |>.block
  let sent ← handler.load (origin "http://example.com") (target "/") |>.block
  unless sent.map (·.value) == #["a=1", "b=2"] do
    throw <| IO.userError s!"cookie handler replayed {sent.map (·.value)}"

-- `ofJar` stores into the jar and loads the RFC 6265 `Cookie` header from it.
#eval show IO Unit from do
  let handler := CookieHandler.ofJar (← Cookie.Jar.new)
  let response := (Headers.empty.insert .setCookie (.mk "a=1")).insert .setCookie (.mk "b=2; Path=/x")
  handler.store (origin "http://example.com") (target "/login") response |>.block
  let sent ← handler.load (origin "http://example.com") (target "/x/y") |>.block
  unless sent.map (·.value) == #["b=2; a=1"] do
    throw <| IO.userError s!"ofJar sent {sent.map (·.value)}"
  let other ← handler.load (origin "http://other.example") (target "/") |>.block
  unless other.isEmpty do
    throw <| IO.userError "ofJar sent a cookie to another host"
