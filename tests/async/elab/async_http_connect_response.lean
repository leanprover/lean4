import Std.Http
import Std.Http.Test.Helpers

open Std Http
open Std.Http.Internal.Test

/-!
Tests the server's answer to `CONNECT`. A 2xx turns the connection into a tunnel right after the
head, so it carries no framing fields and no content (RFC 9110 §9.3.6). The server does not tunnel,
so it closes the connection instead of parsing the tunnel's bytes as HTTP.
-/

def connectRequest : String :=
  "CONNECT example.com:443 HTTP/1.1\x0d\nHost: example.com:443\x0d\n\x0d\n"

/-- Bytes a client sends through the tunnel it believes is open. -/
def tunnelBytes : String :=
  "GET /admin HTTP/1.1\x0d\nHost: a\x0d\nConnection: close\x0d\n\x0d\n"

def handledHandler : TestHandler := fun req =>
  Response.ok |>.text s!"handled {req.line.method} {req.line.uri}"

#eval runGroup "2xx to CONNECT" do
  check "200 with content" (connectRequest ++ tunnelBytes) handledHandler fun r => do
    assertStatus r "HTTP/1.1 200 OK"
    assertResponseCount r 1
    assertAbsent r "Content-Length"
    assertAbsent r "Transfer-Encoding"
    assertAbsent r "handled"
  check "200 streamed" (connectRequest ++ tunnelBytes)
    (fun _ => Response.ok |>.stream fun out => out.send (Chunk.ofByteArray "tunnel".toUTF8))
    fun r => do
      assertResponseCount r 1
      assertAbsent r "Transfer-Encoding"
      assertAbsent r "tunnel"

-- Any other answer to CONNECT is an ordinary response.
#eval runGroup "non-2xx to CONNECT" do
  checkClose "403" connectRequest (fun _ => Response.forbidden |>.text "no") fun r => do
    assertStatus r "HTTP/1.1 403"
    assertContains r "Content-Length: 2"
    assertContains r "\x0d\n\x0d\nno"
