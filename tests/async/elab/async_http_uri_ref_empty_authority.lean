import Std.Http

open Std Http
open Std.Http.Protocol.H1

/-!
A network-path reference may have an empty authority: RFC 3986 §4.2 reads `"//" authority
path-abempty`, and a `reg-name` may be empty (§3.2.2), as after a scheme in `file:///x`.
`URIReference.parse?` accepts such a reference and prints it back unchanged, and so does every prefix
of one. A redirect to it names no host (RFC 9110 §4.2.1), so it is not followed.
-/

def check (cond : Bool) (msg : String) : IO Unit :=
  unless cond do throw (IO.userError msg)

def emptyAuthority? (s : String) : Option URI.RelativeRef :=
  match URIReference.parse? s with
  | some (.relative r) => if r.authority.any (·.host == .empty) then some r else none
  | _ => none

#eval do
  for s in ["//", "///", "///a", "///a/b?c#d", "//?q", "//#f", "//?", "//#", "////a"] do
    let some r := emptyAuthority? s
      | throw (IO.userError s!"{s.quote}: expected a reference with an empty authority")
    check (toString r == s) s!"{s.quote}: printed back as {(toString r).quote}"
    check (r.authority.all fun (a : URI.Authority) => a.userInfo.isNone && a.port == URI.Port.omitted)
      s!"{s.quote}: unexpected userinfo or port"

-- After a scheme the same authority and path come out.
#eval do
  let some (.absolute u) := URIReference.parse? "file:///a/b" | throw (IO.userError "file:///a/b")
  let some r := emptyAuthority? "///a/b" | throw (IO.userError "///a/b")
  check (u.authority == r.authority && u.path == r.path) "///a/b differs from file:///a/b"

-- Every prefix of a reference is a reference.
#eval do
  let s := "///a/b?c#d"
  for i in [0:s.length + 1] do
    let p := (s.take i).toString
    let some r := URIReference.parse? p | throw (IO.userError s!"prefix {p.quote} does not parse")
    check (toString r == p) s!"prefix {p.quote}: printed back as {(toString r).quote}"

-- Still rejected, as after a scheme (`http://@/x`, `http://:80/x`): userinfo or a port needs a host.
#eval do
  for s in ["//@/x", "//:80/x", "//a@/x", "//[/x"] do
    check (URIReference.parse? s).isNone s!"{s.quote}: expected no parse"

private def base : URI := URI.parse! "http://example.com/a/b"

private def origin : URI.Origin :=
  { scheme := base.scheme, host := base.host?.get!, port := base.port }

private def request : Request.Head :=
  { method := .get, version := .v11, uri := base.originTarget, headers := .empty }

-- A redirect to a reference with an empty authority is not followed.
#eval do
  for loc in ["//", "///", "///evil.com", "///evil.com/x", "////evil.com", "//?q", "//#f"] do
    let headers := Headers.empty.insert .location (Header.Value.ofString! loc)
    for status in [Status.movedPermanently, .found, .seeOther, .temporaryRedirect, .permanentRedirect] do
      match decideRedirect origin request true status headers with
      | .done => pure ()
      | .follow p => throw (IO.userError s!"{loc.quote}: followed to {repr p.origin}")
