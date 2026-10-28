import Std.Http

open Std Http Protocol.H1

/-!
Benchmarks the sans-I/O HTTP/1.1 client state machine (`Protocol.H1.Machine .sending`): on one
keep-alive connection, each exchange encodes a request head, feeds the whole response, parses its
status line and headers, and pulls its body.

- `fixed_small`: a minimal `Content-Length` response.
- `fixed_typical`: a 1 KiB response with the headers of a typical API server.
- `chunked`: a 1 KiB response sent as eight 128-byte chunks followed by a trailer.
-/

def request : Request.Head := {
  method := .get
  version := .v11
  uri := RequestTarget.parse! "/api/v1/items?page=2&per_page=50"
  headers := Headers.empty
    |>.insert .host (.mk "api.example.com")
    |>.insert .userAgent (.mk "lean-bench/1.0")
    |>.insert .accept (.mk "application/json")
}

/-- Runs one request/response exchange and returns the number of response body bytes pulled. -/
def exchange (machine : Machine .sending) (response : ByteArray) : IO (Machine .sending × Nat) := do
  let mut machine := machine.send request |>.userClosedBody |>.feed response
  let mut bodyBytes := 0
  let mut done := false
  let mut fuel := 64
  while !done do
    if fuel == 0 then
      throw <| .userError "exchange made no progress"
    fuel := fuel - 1
    let (next, res) := machine.step
    machine := next
    for event in res.events do
      if let .failed err := event then
        throw <| .userError s!"machine failed: {err}"
    while machine.canPullBodyNow do
      let (next, pulled?) := machine.pullBody
      machine := next
      if let some pulled := pulled? then
        bodyBytes := bodyBytes + pulled.chunk.data.size
        done := pulled.final
  -- Completes the exchange so the next request can be sent.
  let (ready, _) := machine.step
  unless ready.isWaitingMessage do
    throw <| .userError "connection not ready for the next request"
  return (ready, bodyBytes)

def run (name : String) (n : Nat) (response : String) (bodySize : Nat) : IO Unit := do
  let response := response.toUTF8
  let mut machine : Machine .sending := { config := { maxMessages := n + 1 } }
  let mut total := 0
  let t1 ← IO.monoNanosNow
  for _ in *...n do
    let (next, bytes) ← exchange machine response
    machine := next
    total := total + bytes
  let t2 ← IO.monoNanosNow

  unless total == n * bodySize do
    throw <| .userError s!"{name}: expected {n * bodySize} body bytes, got {total}"
  IO.println s!"measurement: {name} {(t2 - t1).toFloat / 1000000000.0} s"

def main (args : List String) : IO Unit := do
  let n := args[0]!.toNat!

  run "fixed_small" n "HTTP/1.1 200 OK\r\nContent-Type: text/plain\r\nContent-Length: 2\r\n\r\nok" 2

  let body := String.ofList (List.replicate 1024 'x')
  run "fixed_typical" n
    ("HTTP/1.1 200 OK\r\n" ++
    "Date: Tue, 27 Oct 2026 12:00:00 GMT\r\n" ++
    "Server: nginx/1.27.2\r\n" ++
    "Content-Type: application/json; charset=utf-8\r\n" ++
    "Content-Length: 1024\r\n" ++
    "Cache-Control: private, max-age=0, must-revalidate\r\n" ++
    "ETag: \"5f3a9c2e-400\"\r\n" ++
    "Vary: Accept-Encoding, Origin\r\n" ++
    "Set-Cookie: session=6f1e3c2a9b8d4e7f; Path=/; HttpOnly; Secure; SameSite=Lax\r\n" ++
    "Strict-Transport-Security: max-age=63072000; includeSubDomains\r\n" ++
    "X-Request-Id: 0c6f1b52-8d3e-4b7a-9f21-3c4d5e6f7a8b\r\n\r\n" ++ body) 1024

  let chunk := s!"80\r\n{String.ofList (List.replicate 128 'y')}\r\n"
  run "chunked" n
    ("HTTP/1.1 200 OK\r\nContent-Type: text/plain\r\nTransfer-Encoding: chunked\r\n\r\n" ++
    String.join (List.replicate 8 chunk) ++ "0\r\nX-Checksum: 1234\r\n\r\n") 1024
