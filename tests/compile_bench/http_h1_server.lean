import Std.Http

open Std Http Protocol.H1

/-!
Benchmarks the sans-I/O HTTP/1.1 server state machine (`Protocol.H1.Machine .receiving`) without
the `Async` connection loop (see `http_server.lean` for that): a pipeline of requests is fed at
once and every request is answered synchronously, so all the work measured is parsing, framing and
encoding.

- `get_small`: minimal `GET`s answered with a fixed `"ok"` body.
- `get_browser`: `GET`s carrying the ten headers of a typical browser page request.
- `post_fixed`: `Content-Length` uploads, echoed back.
- `post_chunked`: chunked uploads, echoed back.
-/

/-- A synchronously driven server connection. -/
structure Conn where
  machine : Machine .receiving
  /-- Whether a request head was parsed and is still unanswered. -/
  pending : Bool := false
  /-- Body of the pending request pulled so far. -/
  body : ByteArray := .empty
  bodyDone : Bool := false
  /-- Body bytes of all answered requests. -/
  received : Nat := 0
  responses : Nat := 0
  outBytes : Nat := 0

def responseHead : Response.Head :=
  { headers := Headers.empty.insert .contentType (.mk "text/plain") }

/-- Echoes the pending request's body, or answers `"ok"` when it has none. -/
def respond (c : Conn) : Conn :=
  let data := if c.body.isEmpty then "ok".toUTF8 else c.body
  let machine := c.machine.setKnownSize (.fixed data.size)
    |>.send responseHead
    |>.sendData #[{ data }]
    |>.userClosedBody
  { c with
    machine, pending := false, body := .empty, bodyDone := false, received := c.received + c.body.size
    responses := c.responses + 1 }

/-- Steps the machine until it halts or needs more input, answering each complete request. -/
partial def pump (c : Conn) : IO Conn := do
  let (machine, res) := c.machine.step
  let mut c := { c with machine, outBytes := c.outBytes + res.output.size }
  let mut progress := res.output.size != 0
  for event in res.events do
    match event with
    | .failed err => throw <| .userError s!"machine failed: {err}"
    | .needMoreData _ => pure ()
    | .endHeaders _ =>
      c := { c with pending := true }
      progress := true
    | _ => progress := true
  while c.machine.canPullBodyNow do
    let (machine, pulled?) := c.machine.pullBody
    c := { c with machine }
    if let some pulled := pulled? then
      c := { c with body := c.body ++ pulled.chunk.data, bodyDone := pulled.final }
      progress := true
  if c.pending && c.bodyDone && c.machine.isWaitingMessage then
    c := respond c
    progress := true
  if c.machine.halted || !progress then
    return c
  pump c

/-- Serves `n - 1` copies of `keep` and then `close`, each carrying `bodySize` body bytes. -/
def run (name : String) (n : Nat) (bodySize : Nat) (keep close : String) : IO Unit := do
  let keep := keep.toUTF8
  let mut input := ByteArray.empty
  for _ in *...(n - 1) do
    input := input ++ keep
  input := input ++ close.toUTF8

  let machine : Machine .receiving := { config := Config.toH1Config { maxRequests := n + 1 } }
  let t1 ← IO.monoNanosNow
  let c ← pump { machine := machine.feed input |>.noMoreInput }
  let t2 ← IO.monoNanosNow

  -- Every response carries at least its status line and its body (`"ok"` for requests without one).
  let minResponse := "HTTP/1.1 200 OK\r\n".utf8ByteSize + (if bodySize == 0 then 2 else bodySize)
  unless c.responses == n ∧ c.machine.halted ∧ c.received == n * bodySize ∧
      c.outBytes ≥ n * minResponse do
    throw <| .userError <|
      s!"{name}: expected {n} responses with {n * bodySize} body bytes, got {c.responses} " ++
      s!"with {c.received}, in {c.outBytes} output bytes"
  IO.println s!"measurement: {name} {(t2 - t1).toFloat / 1000000000.0} s"

def browserGet (connection : String) : String :=
  "GET /articles/2026/10/http-benchmarks?utm_source=feed HTTP/1.1\r\n" ++
  "Host: www.example.com\r\n" ++
  "User-Agent: Mozilla/5.0 (X11; Linux aarch64; rv:131.0) Gecko/20100101 Firefox/131.0\r\n" ++
  "Accept: text/html,application/xhtml+xml,application/xml;q=0.9,image/avif,image/webp,*/*;q=0.8\r\n" ++
  "Accept-Language: en-US,en;q=0.5\r\n" ++
  "Accept-Encoding: gzip, deflate, br, zstd\r\n" ++
  "Referer: https://www.example.com/articles/2026/10/http-benchmarks\r\n" ++
  s!"Connection: {connection}\r\n" ++
  "Cookie: session=6f1e3c2a9b8d4e7f; theme=dark; _ga=GA1.2.1234567890.1700000000\r\n" ++
  "Upgrade-Insecure-Requests: 1\r\n" ++
  "Sec-Fetch-Dest: document\r\n\r\n"

def main (args : List String) : IO Unit := do
  let n := args[0]!.toNat!

  run "get_small" n 0
    "GET /bench HTTP/1.1\r\nHost: example.com\r\n\r\n"
    "GET /bench HTTP/1.1\r\nHost: example.com\r\nConnection: close\r\n\r\n"

  run "get_browser" n 0 (browserGet "keep-alive") (browserGet "close")

  let body := "{\"id\":12345,\"name\":\"lean\",\"tags\":[\"http\",\"bench\"]}"
  let post (extra : String) :=
    s!"POST /api/items HTTP/1.1\r\nHost: example.com\r\nContent-Type: application/json\r\n" ++
    s!"Content-Length: {body.utf8ByteSize}\r\n{extra}\r\n{body}"
  run "post_fixed" n body.utf8ByteSize (post "") (post "Connection: close\r\n")

  let chunked (extra : String) :=
    "POST /api/upload HTTP/1.1\r\nHost: example.com\r\nTransfer-Encoding: chunked\r\n" ++
    s!"{extra}\r\n10\r\n0123456789abcdef\r\n6\r\nghijkl\r\n0\r\n\r\n"
  run "post_chunked" n 22 (chunked "") (chunked "Connection: close\r\n")
