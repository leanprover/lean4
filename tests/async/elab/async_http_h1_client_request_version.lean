import Std.Http

open Std Http
open Std.Http.Protocol.H1

/-!
A client's request head depends only on the request: the `Connection` field must not change when
the response's status line (here `HTTP/1.0`) has already arrived when the request is written.
-/

def get (method : Method) : Request.Head :=
  { method, version := .v11, uri := RequestTarget.parse! "/", headers := Headers.empty.insert .host (.mk "a") }

/-- Sends a GET and reads its response, then sends a HEAD and reads `early` before the HEAD is
written; returns the bytes written for it. -/
def secondRequest (early : ByteArray) : ByteArray := Id.run do
  let mut m : Machine .sending := { config := {} }
  m := m.send (get .get) |>.userClosedBody
  let (m1, _) := m.step
  m := m1.feed "HTTP/1.1 204 No Content\r\n\r\n".toUTF8
  for _ in [0:4] do
    m := m.step.1
  m := (m.send (get .head) |>.userClosedBody).feed early
  let mut out := ByteArray.empty
  for _ in [0:4] do
    let (m', res) := m.step
    m := m'
    out := out ++ res.output.toByteArray
  return out

#eval show IO Unit from do
  let late := secondRequest .empty
  let early := secondRequest "HTTP/1.0 200 OK\r\n".toUTF8
  unless late == early do
    throw <| IO.userError s!"request head changed: {(String.fromUTF8! late).quote} vs {(String.fromUTF8! early).quote}"
  unless late == "HEAD / HTTP/1.1\r\nHost: a\r\n\r\n".toUTF8 do
    throw <| IO.userError s!"unexpected request head: {(String.fromUTF8! late).quote}"
