module

import Std.Http.Protocol.H1

open Std.Http
open Std.Http.Protocol.H1

/-!
Differential test of redirect target resolution: `decideRedirect` is checked against an independent
string-based implementation of RFC 3986 §5.2 over the §5.4 examples and a generated corpus of valid
and invalid `Location` values, and every followed plan must put an RFC 9112 request-target on the
wire.
-/

/-! ## RFC 3986 §5.2 reference resolution -/

abbrev Str := List Char

structure Ref where
  scheme? : Option Str
  authority? : Option Str
  path : Str
  query? : Option Str
  fragment? : Option Str

/-- Appendix B: `^(([^:/?#]+):)?(//([^/?#]*))?([^?#]*)(\?([^#]*))?(#(.*))?` -/
def splitRef (s : Str) : Ref :=
  let (pre, rest) := s.span (fun c => c != ':' && c != '/' && c != '?' && c != '#')
  let (scheme?, s) :=
    if rest.head? == some ':' && !pre.isEmpty then (some pre, rest.tail) else (none, s)
  let (authority?, s) :=
    match s with
    | '/' :: '/' :: r =>
      let (a, r) := r.span (fun c => c != '/' && c != '?' && c != '#')
      (some a, r)
    | _ => (none, s)
  let (path, s) := s.span (fun c => c != '?' && c != '#')
  let (query?, s) :=
    match s with
    | '?' :: r => let (q, r) := r.span (· != '#'); (some q, r)
    | _ => (none, s)
  let fragment? := match s with
    | '#' :: r => some r
    | _ => none
  { scheme?, authority?, path, query?, fragment? }

/-- §5.2.4. The output buffer is a reversed list of the pieces rule E moved. -/
partial def removeDotSegmentsLoop : Str → List Str → List Str
  | [], out => out
  | '.' :: '.' :: '/' :: r, out => removeDotSegmentsLoop r out
  | '.' :: '/' :: r, out => removeDotSegmentsLoop r out
  | '/' :: '.' :: '/' :: r, out => removeDotSegmentsLoop ('/' :: r) out
  | ['/', '.'], out => removeDotSegmentsLoop ['/'] out
  | '/' :: '.' :: '.' :: '/' :: r, out => removeDotSegmentsLoop ('/' :: r) (out.drop 1)
  | ['/', '.', '.'], out => removeDotSegmentsLoop ['/'] (out.drop 1)
  | ['.'], out => removeDotSegmentsLoop [] out
  | ['.', '.'], out => removeDotSegmentsLoop [] out
  | c :: r, out =>
    if c == '/' then
      let (seg, rest) := r.span (· != '/')
      removeDotSegmentsLoop rest (('/' :: seg) :: out)
    else
      let (seg, rest) := (c :: r).span (· != '/')
      removeDotSegmentsLoop rest (seg :: out)

def removeDotSegments (p : Str) : Str :=
  (removeDotSegmentsLoop p []).reverse.flatten

/-- §5.2.3 -/
def merge (baseHasAuthority : Bool) (basePath refPath : Str) : Str :=
  if baseHasAuthority && basePath.isEmpty then '/' :: refPath
  else (basePath.reverse.dropWhile (· != '/')).reverse ++ refPath

/-- §5.2.2, strict: a reference's scheme is never ignored. -/
def resolve (base r : Ref) : Ref :=
  if r.scheme?.isSome then
    { r with path := removeDotSegments r.path }
  else if r.authority?.isSome then
    { r with scheme? := base.scheme?, path := removeDotSegments r.path }
  else if r.path.isEmpty then
    { r with scheme? := base.scheme?, authority? := base.authority?, path := base.path,
             query? := r.query?.orElse fun _ => base.query? }
  else if r.path.head? == some '/' then
    { r with scheme? := base.scheme?, authority? := base.authority?,
             path := removeDotSegments r.path }
  else
    { r with scheme? := base.scheme?, authority? := base.authority?,
             path := removeDotSegments (merge base.authority?.isSome base.path r.path) }

/-- §5.3 -/
def recompose (t : Ref) : String :=
  (t.scheme?.map (String.ofList · ++ ":")).getD ""
    ++ (t.authority?.map ("//" ++ String.ofList ·)).getD ""
    ++ String.ofList t.path
    ++ (t.query?.map ("?" ++ String.ofList ·)).getD ""
    ++ (t.fragment?.map ("#" ++ String.ofList ·)).getD ""

/-- The resolver reproduces every example of RFC 3986 §5.4 (base `http://a/b/c/d;p?q`). -/
def rfcTable : List (String × String) := [
  ("g:h", "g:h"), ("g", "http://a/b/c/g"), ("./g", "http://a/b/c/g"), ("g/", "http://a/b/c/g/"),
  ("/g", "http://a/g"), ("//g", "http://g"), ("?y", "http://a/b/c/d;p?y"),
  ("g?y", "http://a/b/c/g?y"), ("#s", "http://a/b/c/d;p?q#s"), ("g#s", "http://a/b/c/g#s"),
  ("g?y#s", "http://a/b/c/g?y#s"), (";x", "http://a/b/c/;x"), ("g;x", "http://a/b/c/g;x"),
  ("g;x?y#s", "http://a/b/c/g;x?y#s"), ("", "http://a/b/c/d;p?q"), (".", "http://a/b/c/"),
  ("./", "http://a/b/c/"), ("..", "http://a/b/"), ("../", "http://a/b/"),
  ("../g", "http://a/b/g"), ("../..", "http://a/"), ("../../", "http://a/"),
  ("../../g", "http://a/g"), ("../../../g", "http://a/g"), ("../../../../g", "http://a/g"),
  ("/./g", "http://a/g"), ("/../g", "http://a/g"), ("g.", "http://a/b/c/g."),
  (".g", "http://a/b/c/.g"), ("g..", "http://a/b/c/g.."), ("..g", "http://a/b/c/..g"),
  ("./../g", "http://a/b/g"), ("./g/.", "http://a/b/c/g/"), ("g/./h", "http://a/b/c/g/h"),
  ("g/../h", "http://a/b/c/h"), ("g;x=1/./y", "http://a/b/c/g;x=1/y"),
  ("g;x=1/../y", "http://a/b/c/y"), ("g?y/./x", "http://a/b/c/g?y/./x"),
  ("g?y/../x", "http://a/b/c/g?y/../x"), ("g#s/./x", "http://a/b/c/g#s/./x"),
  ("g#s/../x", "http://a/b/c/g#s/../x"), ("http:g", "http:g")]

/-- info: [] -/
#guard_msgs in
#eval rfcTable.filter fun (r, want) =>
  recompose (resolve (splitRef "http://a/b/c/d;p?q".toList) (splitRef r.toList)) != want

/-! ## RFC 3986 syntax -/

def hexVal? (c : Char) : Option Nat :=
  if c.isDigit then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c.toLower && c.toLower ≤ 'f' then some (c.toLower.toNat - 'a'.toNat + 10)
  else none

def isUnreserved (c : Char) : Bool :=
  c.isAlphanum || c == '-' || c == '.' || c == '_' || c == '~'

def isPchar (c : Char) : Bool :=
  isUnreserved c || "!$&'()*+,;=:@".contains c

partial def wellFormedPercent : Str → Bool
  | '%' :: a :: b :: r => (hexVal? a).isSome && (hexVal? b).isSome && wellFormedPercent r
  | '%' :: _ => false
  | _ :: r => wellFormedPercent r
  | [] => true

/-- `URI-reference`, checked per component of the Appendix B split. -/
def isValidReference (s : String) : Bool :=
  let r := splitRef s.toList
  let ok (extra : String) (cs : Str) :=
    cs.all (fun c => isPchar c || c == '%' || extra.contains c) && wellFormedPercent cs
  let schemeOk := r.scheme?.all fun sc =>
    sc.head?.any Char.isAlpha && sc.all (fun c => c.isAlphanum || c == '+' || c == '-' || c == '.')
  let hostPortOk (hostPort : Str) :=
    match hostPort with
    | '[' :: rest =>
      let (inner, after) := rest.span (· != ']')
      !inner.isEmpty && inner.all (fun c => (hexVal? c).isSome || c == ':' || c == '.')
        && !(String.ofList inner).contains ":::"
        && match after with
          | [']'] => true
          | ']' :: ':' :: port => port.all Char.isDigit
          | _ => false
    | _ =>
      let (host, port) := match hostPort.reverse.span (· != ':') with
        | (_, []) => (hostPort, [])
        | (p, _ :: h) => (h.reverse, p.reverse)
      ok "" host && !host.contains ':' && !host.contains '@' && port.all Char.isDigit
  let authorityOk := r.authority?.all fun a =>
    match a.reverse.span (· != '@') with
    | (_, []) => hostPortOk a
    | (hp, _ :: ui) => ok "" ui.reverse && !ui.contains '@' && hostPortOk hp.reverse
  let noScheme := r.scheme?.isNone && r.authority?.isNone
  let pathOk := ok "/" r.path
    && !(r.authority?.isNone && r.path.take 2 == ['/', '/'])
    && !(noScheme && (r.path.takeWhile (· != '/')).contains ':')
  schemeOk && authorityOk && pathOk && r.query?.all (ok "/?") && r.fragment?.all (ok "/?")

/-- RFC 9112 §3.2: `absolute-path [ "?" query ]`, or for absolute-form
`scheme "://" authority absolute-path [ "?" query ]` without userinfo or fragment. -/
def wellFormedTarget (target : String) : Bool :=
  let originForm (s : Str) : Bool :=
    let (path, q) := s.span (· != '?')
    path.head? == some '/' && path.all (fun c => isPchar c || c == '/' || c == '%')
      && (q.drop 1).all (fun c => isPchar c || c == '/' || c == '?' || c == '%')
      && wellFormedPercent s
  match target.toList with
  | '/' :: r => originForm ('/' :: r)
  | cs =>
    let (scheme, rest) := cs.span (· != ':')
    match rest with
    | ':' :: '/' :: '/' :: rest =>
      let (authority, pq) := rest.span (fun c => c != '/' && c != '?')
      !scheme.isEmpty && scheme.all (fun c => c.isAlphanum || c == '+' || c == '-' || c == '.')
        && !authority.isEmpty && authority.all (fun c => c.isAlphanum || "-._~:[]".contains c)
        && originForm (if pq.head? == some '/' then pq else '/' :: pq)
    | _ => false

/-! ## Expected and planned outcomes -/

def lower (s : Str) : Str := s.map Char.toLower

/-- §6.2.2.1–2: uppercase percent-encoding hex digits and decode unreserved characters. -/
partial def normalizePercent : Str → Str
  | '%' :: a :: b :: r =>
    match hexVal? a, hexVal? b with
    | some x, some y =>
      let c := Char.ofNat (16 * x + y)
      if isUnreserved c then c :: normalizePercent r
      else '%' :: a.toUpper :: b.toUpper :: normalizePercent r
    | _, _ => '%' :: normalizePercent (a :: b :: r)
  | c :: r => c :: normalizePercent r
  | [] => []

/-- A registered name for DNS lookup (RFC 3986 §3.2.2, RFC 1034 §3.5): non-empty labels of at most 63
alphanumerics and `-` that do not start or end with `-`, and an optional trailing `.`. `_` is also
accepted, as the client does. -/
def isDnsName (host : Str) : Bool :=
  let labels := (String.ofList (if host.getLast? == some '.' then host.dropLast else host)).splitOn "."
  host.length ≤ 255 && labels.all fun l =>
    let cs := l.toList
    !cs.isEmpty && cs.length ≤ 63 && cs.all (fun c => c.isAlphanum || c == '-' || c == '_')
      && cs.head? != some '-' && cs.getLast? != some '-'

/-- `(host, port)` of an authority, with the host normalized as in §6.2.2.1–2, or `none` when it names
no usable host: it is empty (RFC 9110 §4.2.1), a registered name that is not a DNS name, or has an
invalid port. -/
def hostPort? (scheme authority : Str) : Option (Str × Nat) :=
  let hostPort := match authority.reverse.span (· != '@') with
    | (_, []) => authority
    | (hp, _) => hp.reverse
  let (host, port) :=
    if hostPort.head? == some '[' then
      let (h, r) := hostPort.span (· != ']')
      (h ++ [']'], (r.drop 1).drop 1)
    else
      match hostPort.reverse.span (· != ':') with
      | (_, []) => (hostPort, [])
      | (p, _ :: h) => (h.reverse, p.reverse)
  let host := lower (normalizePercent host)
  let defaultPort := if scheme == "https".toList then 443 else 80
  if host.isEmpty || (host.head? != some '[' && !isDnsName host) then none
  else if port.isEmpty then some (host, defaultPort)
  else if port.all Char.isDigit then
    let n := port.foldl (fun n c => n * 10 + (c.toNat - '0'.toNat)) 0
    if n < 65536 then some (host, n) else none
  else none

def notFollowed : String := "<not followed>"

/-- The RFC 3986 outcome as `form scheme://host:port path?query`, from origin `http://example.com`. -/
def expected (baseTarget location : String) : String :=
  let b := splitRef baseTarget.toList
  let base := { b with scheme? := some "http".toList, authority? := some "example.com".toList }
  let t := resolve base (splitRef location.toList)
  let scheme := lower (t.scheme?.getD [])
  if scheme != "http".toList && scheme != "https".toList then notFollowed else
  match t.authority? >>= hostPort? scheme with
  | none => notFollowed
  | some (host, port) =>
    let form :=
      if scheme != "http".toList || host != "example.com".toList || port != 80 then "absolute-form"
      else "origin-form"
    let path := if t.path.isEmpty then "/" else String.ofList t.path
    let query := (t.query?.map ("?" ++ String.ofList ·)).getD ""
    s!"{form} {String.ofList scheme}://{String.ofList host}:{port} {path}{query}"

def current : URI.Origin :=
  { scheme := URI.Scheme.ofString! "http", host := (URI.parse! "http://example.com/").host?.get!,
    port := 80 }

/-- The plan in the form of `expected`, and the request-target exactly as it goes on the wire. -/
def planned (baseTarget : String) (location : Header.Value) : String × String :=
  let request : Request.Head :=
    { method := .get, version := .v11, uri := RequestTarget.parse! baseTarget }
  match decideRedirect current request false .found (Headers.empty.insert .location location) with
  | .done => (notFollowed, "")
  | .follow p =>
    let (form, pathQuery) := match p.target with
      | .originForm path query => ("origin-form", toString (RequestTarget.originForm path query))
      | .absoluteForm uri =>
        ("absolute-form", toString (RequestTarget.originForm uri.path uri.query))
      | other => ("other-form", toString other)
    (s!"{form} {p.origin.scheme.val}://{p.origin.host}:{p.origin.port} {pathQuery}",
      toString p.target)

/-- Splits `form origin path?query`. -/
def parts (s : String) : String × String × Str × Option Str :=
  match s.splitOn " " with
  | [form, origin, pq] =>
    let (path, q) := pq.toList.span (· != '?')
    (form, origin, path, if q.isEmpty then none else some q.tail)
  | _ => (s, "", [], none)

/-- A reference shape RFC 3986 forbids that `URIReference.parse?` still returns. -/
def parserViolation? (location : String) : Option String :=
  match URIReference.parse? location with
  | some (.relative { authority := none, path, .. }) =>
    let p := toString path
    if p.startsWith "//" then
      some "parsed as a path starting with \"//\", which needs an authority (RFC 3986 §3.3)"
    else if !path.absolute && ((p.splitOn "/").head!).contains ':' then
      some "parsed as a relative path whose first segment has a \":\" (RFC 3986 §4.2)"
    else none
  | _ => none

/-- A query parameter whose value contains `=` (#16021). -/
def hasEqualsInValue (location : String) : Bool :=
  let query := ((location.splitOn "#").head!.splitOn "?").drop 1
  query.any fun q => (q.splitOn "&").any fun kv => (kv.splitOn "=").length > 2

/-- `none` when the plan agrees with RFC 3986 (up to §6.2.2 normalization of the path), otherwise
the failure category. -/
def check (location want got wire : String) : Option String :=
  if got != notFollowed && !wellFormedTarget wire then
    some "malformed request-target on the wire"
  else if !isValidReference location then
    if got == notFollowed then none
    else some ((parserViolation? location).getD "invalid reference followed")
  else if want == got then none
  else if let some v := parserViolation? location then some v
  else if got == notFollowed then
    if hasEqualsInValue location then some "query value containing \"=\" rejected (#16021)"
    else if (URIReference.parse? (location.splitOn "#").head!).isSome then
      some "rejected because of its fragment"
    else some "valid reference not followed"
  else if want == notFollowed then some "followed a reference that names no http(s) host"
  else
    let (wf, wo, wp, wq) := parts want
    let (gf, go, gp, gq) := parts got
    if wf != gf || wo != go then some "origin or request-target form differs"
    else if wq.map normalizePercent != gq.map normalizePercent then some "query differs"
    else if removeDotSegments (normalizePercent wp) != removeDotSegments (normalizePercent gp) then
      some "path differs"
    else none

/-! ## Corpus -/

def rfcExamples : List String :=
  rfcTable.map (·.1) ++ ["/", "/?y", "/#f", "///g", "//", "//?y", "http://", "http:///g"]

def baseTargets : List String := [
  "/b/c/d;p?q", "/", "/a", "/a/", "/a/b/", "/a//b", "/a/b?x=1&y=2", "/x/y/z?", "/%7Euser/doc",
  "/a%2Fb/c", "/.well-known/x", "/a/b/c/d/e/f", "http://example.com/b/c/d;p?q", "/a/./b/../c"]

def segments : Array String := #[
  "g", "h", "x", "", "", ".", ".", "..", "..", "g.", ".g", "..g", "g..", "...", "%2E", "%2e",
  "%2E%2E", ".%2E", "a;b", "a=b", "a:b", "@", "!$&'()*+,;=", "%7E", "~", "%41", "%2F", "%25",
  "%3F", "%23", "a%20b", "-_.~", "%C3%A9", "%E9", "*", "a+b", "%2f", "%3A"]

def queries : Array String := #[
  "", "y", "a=b", "a=b=c", "a&b", "a&&b", "&", "=", "a=", "=b", "/./x", "../x", "?", "a+b",
  "%2B", "a%3Db", "%20", "q=%41", "a;b", ":@", "!$'()*,", "%26=%3D", "a=b&a=c", "%7e", "caf%E9"]

def fragments : Array String := #["", "s", "s/../x", "?y", "%C3%A9", "caf%E9"]

def authorities : Array String := #[
  "example.com", "EXAMPLE.com", "example.com:80", "example.com:", "example.com:8080",
  "example.com:443", "other.com", "user:pw@example.com", "user@other.com:81", "127.0.0.1",
  "[::1]", "[::1]:8080", "a.b-c.example", "example.com:65536", "", ":80", "example.com.",
  "a_b.example", "ex%41mple.com"]

def schemes : Array String := #["http", "HTTP", "https", "HtTpS", "ftp", "file", "mailto"]

/-- Pieces that make a reference invalid in most positions. -/
def invalidPieces : Array String := #[
  " ", "<", ">", "\"", "{", "}", "|", "\\", "^", "`", "%", "%G1", "%2", "é", "[", "]",
  "a b", "%%", "#", "?#", "//", ":", "@", "%00", "%0D%0A"]

structure Rng where
  state : UInt64

def Rng.next (g : Rng) : Nat × Rng :=
  let s := g.state * 6364136223846793005 + 1442695040888963407
  ((s >>> 33).toNat, ⟨s⟩)

def Rng.below (g : Rng) (n : Nat) : Nat × Rng :=
  let (m, g) := g.next
  (m % n, g)

def Rng.pick (g : Rng) (xs : Array String) : String × Rng :=
  let (n, g) := g.below xs.size
  (xs[n]!, g)

/-- `/`-separated segments. A relative path whose first segment is empty or has a `:` gets a `./`
prefix, and an absolute one a `.` segment so it cannot start with `//` (RFC 3986 §4.2). -/
def genPath (g : Rng) (absolute : Bool) : String × Rng := Id.run do
  let (n, g) := g.below 5
  let mut g := g
  let mut segs : Array String := #[]
  for _ in [0:n + 1] do
    let (s, g') := g.pick segments
    g := g'
    segs := segs.push s
  let body := "/".intercalate segs.toList
  if absolute then
    return ("/" ++ (if body.startsWith "/" then "." ++ body else body), g)
  else if segs[0]!.contains ':' || segs[0]!.isEmpty then
    return ("./" ++ body, g)
  else
    return (body, g)

def genReference (g : Rng) : String × Rng := Id.run do
  let (kind, g) := g.below 10
  let mut g := g
  let mut out := ""
  -- 0-1: scheme and authority, 2: authority, 3: scheme without authority, else no prefix.
  if kind ≤ 1 then
    let (s, g') := g.pick schemes
    let (a, g'') := g'.pick authorities
    g := g''
    out := s ++ "://" ++ a
  else if kind == 2 then
    let (a, g') := g.pick authorities
    g := g'
    out := "//" ++ a
  else if kind == 3 then
    let (s, g') := g.pick schemes
    g := g'
    out := s ++ ":"
  let (pathKind, g') := g.below 4
  g := g'
  if pathKind != 0 then
    let (p, g') := genPath g (pathKind == 1 || kind ≤ 2)
    g := g'
    out := out ++ p
  let (hasQuery, g') := g.below 3
  g := g'
  if hasQuery == 0 then
    let (n, g') := g.below 3
    g := g'
    let mut qs : Array String := #[]
    for _ in [0:n + 1] do
      let (q, g') := g.pick queries
      g := g'
      qs := qs.push q
    out := out ++ "?" ++ "&".intercalate qs.toList
  let (hasFragment, g') := g.below 5
  g := g'
  if hasFragment == 0 then
    let (f, g') := g.pick fragments
    g := g'
    out := out ++ "#" ++ f
  return (out, g)

def corpus (count : Nat) : Array String := Id.run do
  let mut g : Rng := ⟨20261029⟩
  let mut out := rfcExamples.toArray
  for i in [0:count] do
    let (r, g') := genReference g
    g := g'
    if i % 4 == 0 then
      let (piece, g') := g.pick invalidPieces
      let (at_, g'') := g'.below (r.length + 1)
      g := g''
      let cs := r.toList
      out := out.push (String.ofList (cs.take at_ ++ piece.toList ++ cs.drop at_))
    else
      out := out.push r
  return out

/-! ## Run -/

/-- Checks every base against every reference and reports each failure category with its count and
a few samples. -/
def run (count : Nat) (samplesPerCategory : Nat := 3) : IO Unit := do
  let refs := corpus count
  let mut checked := 0
  let mut failures : Array (String × Nat × Array String) := #[]
  for base in baseTargets do
    for raw in refs do
      -- Field values carry no leading or trailing whitespace (RFC 9110 §5.5).
      let some value := Header.Value.ofString? raw | continue
      let location := value.value
      checked := checked + 1
      let want := expected base location
      let (got, wire) := planned base value
      if let some category := check location want got wire then
        let sample := s!"  {base} + {location.quote}\n    rfc:  {want}\n    plan: {got}"
        failures := match failures.findIdx? (·.1 == category) with
          | some i =>
            failures.modify i fun (c, n, xs) =>
              (c, n + 1, if xs.size < samplesPerCategory then xs.push sample else xs)
          | none => failures.push (category, 1, #[sample])
  if failures.isEmpty then
    IO.println s!"{checked} redirects agree with RFC 3986"
  else
    for (category, n, samples) in failures do
      IO.println s!"{n} × {category}"
      for s in samples do IO.println s

/-- info: 42700 redirects agree with RFC 3986 -/
#guard_msgs in
#eval run 3000
