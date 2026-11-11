import Std.Http
import Std.Http.Test.Helpers

open Std Http
open Std.Http.Internal.Test
open Std.Http.Protocol.H1

/-!
Tests how URIs, request-targets, ports, host names and status codes are read and written:
- a `:` in a username is escaped, since the first `:` separates it from the password (RFC 3986
  §3.2.1);
- absolute-form and authority-form targets carry no userinfo or fragment (RFC 9110 §4.2.4,
  RFC 9112 §3.2.2–3.2.3);
- a port may have leading zeros (`port = *DIGIT`, RFC 3986 §3.2.3);
- a host name of the maximal 253 characters may end with the root `.`;
- a status code of 600–999 counts as a server error (RFC 9110 §15).
-/

def expect (cond : Bool) (msg : String) : IO Unit :=
  unless cond do throw (IO.userError msg)

def run (machine : Machine dir) (n : Nat := 4) : Machine dir × String := Id.run do
  let mut machine := machine
  let mut out := ByteArray.empty
  for _ in [0:n] do
    let (next, step) := machine.step
    machine := next
    out := out ++ step.output.toByteArray
  return (machine, String.fromUTF8! out)

-- A `:` in a username.
#eval show IO Unit from do
  let uri := URI.Builder.empty |>.setScheme! "http" |>.setHost! "example.com"
    |>.setUserInfo "a:b" (some "pw") |>.build
  expect (toString uri == "http://a%3Ab:pw@example.com/") s!"printed {toString uri}"
  let back := URI.parse! (toString uri)
  let userInfo := back.authority.bind (·.userInfo)
  expect (userInfo.bind (·.username?) == some "a:b" && userInfo.bind (·.password?) == some "pw")
    s!"read back as username {userInfo.bind (·.username?)}, password {userInfo.bind (·.password?)}"

-- Request-targets.
#eval show IO Unit from do
  let absolute := RequestTarget.absoluteForm (URI.parse! "http://user:secret@example.com/x?q#frag")
  expect (toString absolute == "http://example.com/x?q") s!"absolute-form printed as {toString absolute}"
  let some authority := (URI.parse! "http://u:p@example.com:443/").authority
    | throw (IO.userError "no authority")
  let target := RequestTarget.authorityForm authority
  expect (toString target == "example.com:443") s!"authority-form printed as {toString target}"
  -- On the wire, the target reads back as a request-target.
  let headers := Headers.empty.insert Header.Name.host (.mk "example.com")
  let head : Request.Head := { method := .get, version := .v11, uri := absolute, headers }
  let m : Machine .sending := { config := {} }
  let (_, out) := run (m.setKnownSize (.fixed 0) |>.send head |>.userClosedBody)
  expect (out.startsWith "GET http://example.com/x?q HTTP/1.1\x0d\n") s!"request line {out.quote}"

-- Ports with leading zeros.
#eval show IO Unit from do
  let port := (Header.Host.parse (.mk "example.com:000080")).map (·.port)
  expect (port == some (.value 80)) s!"Host example.com:000080 gave port {repr port}"
  let port := (URI.parse? "http://example.com:0000000000080/").bind (·.authority) |>.map (·.port)
  expect (port == some (.value 80)) s!"URI with port 0000000000080 gave {repr port}"
  expect (URI.parse? "http://example.com:00065536/").isNone "port 00065536 was accepted"

#eval runGroup "Host with a padded port" do
  check "Host: example.com:000080" "GET / HTTP/1.1\x0d\nHost: example.com:000080\x0d\nConnection: close\x0d\n\x0d\n"
    okHandler fun r => assertStatus r "HTTP/1.1 200"

-- A maximal host name with its trailing dot.
#eval show IO Unit from do
  let name := ".".intercalate [String.join (List.replicate 63 "a"), String.join (List.replicate 63 "b"),
    String.join (List.replicate 63 "c"), String.join (List.replicate 61 "d")]
  expect (name.length == 253) "test setup"
  for host in [name, name ++ "."] do
    expect (URI.parse? s!"http://{host}/").isSome s!"URI with a {host.length}-character host was rejected"
    expect (Header.Host.parse (.ofString! host)).isSome s!"Host of {host.length} characters was rejected"
    expect (URI.DomainName.ofString? host).isSome s!"DomainName.ofString? rejected {host.length} characters"
  -- Control: 254 characters without the dot are too long.
  expect (URI.parse? s!"http://e{name}/").isNone "URI with a 254-character host was accepted"

-- Status codes 600–999.
#eval show IO Unit from do
  for code in [600, 700, 999] do
    let some status := Status.ofCode none code | throw (IO.userError s!"ofCode {code}")
    expect (status.isServerError && status.isError) s!"status {code} is not a server error"
  let some status := Status.ofCode none 599 | throw (IO.userError "ofCode 599")
  expect status.isServerError "599 is not a server error"
  let some status := Status.ofCode none 499 | throw (IO.userError "ofCode 499")
  expect (!status.isServerError && status.isClientError) "499 is not a client error"
