import Std.Http
import Std.Http.Test.Helpers

open Std Http
open Std.Http.Internal.Test
open Std.Http.Protocol.H1

/-!
Tests that no HTTP/1.0 message is framed with a transfer coding, which HTTP/1.0 does not define
(RFC 9112 §6.1). A client's HTTP/1.0 request of unknown length is held until its body ends and goes
out with `Content-Length`. A server answers `500` when a handler's response to an HTTP/1.0 request
carries a transfer coding, instead of sending the coded bytes as an identity body.
-/

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

def post (version : Version) : Request.Head :=
  { method := .post, version, uri := RequestTarget.parse! "/",
    headers := Headers.empty.insert Header.Name.host (.mk "a") }

/-- Sends a POST whose body arrives in a later step than its head, and returns the wire bytes. -/
def sendLateBody (version : Version) : Machine .sending × String :=
  let m : Machine .sending := { config := {} }
  let (m, first) := run (m.send (post version) |>.sendData #[Chunk.ofByteArray "hello".toUTF8]) 2
  let (m, rest) := run m.userClosedBody 3
  (m, first ++ rest)

#eval show IO Unit from do
  let (_, out) := sendLateBody .v10
  expect (!out.contains "Transfer-Encoding" && out.contains "Content-Length: 5\x0d\n"
      && out.endsWith "\x0d\n\x0d\nhello")
    s!"client HTTP/1.0 POST of unknown length: {out.quote}"
  -- Control: an HTTP/1.1 request of unknown length streams chunked.
  let (_, out) := sendLateBody .v11
  expect (out.contains "Transfer-Encoding: chunked") s!"client HTTP/1.1 POST of unknown length: {out.quote}"

-- A length set as `chunked` cannot be sent over HTTP/1.0: the exchange ends with nothing written.
#eval show IO Unit from do
  let m : Machine .sending := { config := {} }
  let (m, out) := run (m.setKnownSize .chunked |>.send (post .v10)
    |>.sendData #[Chunk.ofByteArray "hello".toUTF8] |>.userClosedBody)
  expect (out.isEmpty && m.error.isSome)
    s!"client HTTP/1.0 POST set as chunked: expected nothing written and an error, got {out.quote}"

def codedHandler : TestHandler := fun _ =>
  Response.ok
    |>.header! "Transfer-Encoding" "gzip, chunked"
    |>.stream fun out => out.send (Chunk.ofByteArray "GZIPPED".toUTF8)

#eval runGroup "transfer coding to an HTTP/1.0 client" do
  check "HTTP/1.0 GET" "GET / HTTP/1.0\x0d\nHost: a\x0d\n\x0d\n" codedHandler fun r => do
    assertStatus r "HTTP/1.1 500"
    assertAbsent r "GZIPPED"
  -- Control: an HTTP/1.1 client gets the coding and the coded bytes.
  check "HTTP/1.1 GET" (mkGetClose "/") codedHandler fun r => do
    assertStatus r "HTTP/1.1 200"
    assertContains r "Transfer-Encoding: gzip, chunked"
    assertContains r "GZIPPED"
