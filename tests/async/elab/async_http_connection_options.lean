import Std.Http
import Std.Http.Test.Helpers

open Std Http
open Std.Http.Internal.Test
open Std.Http.Protocol.H1

/-!
Tests the `Connection` field: `close` ends the connection for every HTTP version, even next to
`keep-alive` (RFC 9112 §9.3, §9.6), and empty list elements are ignored (RFC 9110 §5.6.1.2).
-/

/-- Steps `machine` `n` times and returns it with the bytes it wrote. -/
def run (machine : Machine dir) (n : Nat := 4) : Machine dir × String := Id.run do
  let mut machine := machine
  let mut out := ByteArray.empty
  for _ in [0:n] do
    let (next, step) := machine.step
    machine := next
    out := out ++ step.output.toByteArray
  return (machine, String.fromUTF8! out)

def expect (cond : Bool) (msg : String) : IO Unit :=
  unless cond do throw (IO.userError msg)

-- `close` wins over `keep-alive` on an HTTP/1.0 request, in either order: one response, and the
-- request pipelined after it is never served.
#eval runGroup "HTTP/1.0 close wins" do
  for value in ["keep-alive, close", "close, keep-alive"] do
    check s!"Connection: {value}"
      s!"GET /1 HTTP/1.0\x0d\nConnection: {value}\x0d\n\x0d\nGET /2 HTTP/1.0\x0d\n\x0d\n"
      uriHandler fun r => do
        assertResponseCount r 1
        assertContains r "Connection: close"
        assertAbsent r "/2"
  -- Control: `keep-alive` alone keeps an HTTP/1.0 connection open.
  check "Connection: keep-alive"
    "GET /1 HTTP/1.0\x0d\nConnection: keep-alive\x0d\n\x0d\nGET /2 HTTP/1.0\x0d\n\x0d\n"
    uriHandler fun r => assertResponseCount r 2

-- A client's HTTP/1.0 request that lists both `keep-alive` and `close` goes out with `close`, and
-- the machine does not keep the connection.
#eval show IO Unit from do
  let headers := Headers.empty
    |>.insert Header.Name.host (.mk "a")
    |>.insert Header.Name.connection (.mk "keep-alive, close")
  let head : Request.Head := { method := .get, version := .v10, uri := RequestTarget.parse! "/", headers }
  let m : Machine .sending := { config := {} }
  let (m, out) := run (m.setKnownSize (.fixed 0) |>.send head |>.userClosedBody)
  expect (out.contains "Connection: close" && !out.contains "keep-alive")
    s!"client HTTP/1.0 request: expected Connection: close, got {out.quote}"
  expect (!m.keepAlive) "client HTTP/1.0 request with close: the machine kept the connection"

-- Empty elements of a `Connection` list are skipped, so both pipelined requests are answered.
#eval runGroup "empty list elements" do
  for value in ["keep-alive, ", ", keep-alive", "keep-alive,,", ""] do
    check s!"Connection: {value.quote}"
      (mkGet "/1" s!"Connection: {value}\x0d\n" ++ mkGetClose "/2")
      uriHandler fun r => assertResponseCount r 2

#eval show IO Unit from do
  for (value, tokens) in [("keep-alive, ", #["keep-alive"]), (", upgrade,, close", #["upgrade", "close"]),
      ("", #[])] do
    let got := (Header.Connection.parse (.ofString! value)).map (·.tokens)
    expect (got == some tokens) s!"Connection.parse {value.quote}: expected {tokens}, got {got}"

-- A handler's `upgrade` option survives a trailing empty element.
#eval runGroup "handler options" do
  check "handler Connection: upgrade," (mkGetClose "/")
    (fun _ => Response.ok |>.header! "Connection" "upgrade," |>.text "ok")
    fun r => assertContains r "Connection: upgrade, close"
