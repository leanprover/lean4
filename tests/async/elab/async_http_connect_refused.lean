import Std.Http.Test.Helpers

open Std.Async
open Std Http Internal Test

/-!
Tests that the server closes the connection after any answer to `CONNECT` other than a 2xx. A client
may send the tunnel's bytes right after its request, before it reads the answer. Once the tunnel is
refused, those bytes must not be read as requests, so the answer says `Connection: close` and the
server reads nothing more (RFC 9110 §9.3.6).
-/

def connectRequest : String :=
  "CONNECT example.com:443 HTTP/1.1\x0d\nHost: example.com:443\x0d\n\x0d\n"

/-- Bytes a client sends through the tunnel it expects. -/
def tunnelBytes : String :=
  "GET /admin HTTP/1.1\x0d\nHost: a\x0d\nConnection: close\x0d\n\x0d\n"

def refusing (status : Response.Builder) : TestHandler := fun req =>
  if req.line.method == .connect then status |>.text "refused"
  else Response.ok |>.text s!"handled {req.line.uri}"

#eval runGroup "non-2xx to CONNECT" do
  for (name, status) in [("403", Response.forbidden), ("400", Response.badRequest),
      ("500", Response.internalServerError)] do
    checkTimed name (raw := connectRequest ++ tunnelBytes) (handler := refusing status)
      (expect := fun r => do
        assertStatus r s!"HTTP/1.1 {name}"
        assertContains r "Connection: close"
        assertResponseCount r 1
        assertAbsent r "handled")
