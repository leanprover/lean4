import Std.Http

open Std Http Protocol.H1

/-!
Benchmarks the sans-I/O HTTP/1.1 server state machine when input arrives in pieces, as it does
from a socket: every `feed` is followed by stepping the machine until it asks for more data, so the
cost of resuming a partially parsed message is measured.

- `get_browser_bytes`: browser `GET`s fed one byte at a time (worst case for resumption).
- `get_browser_segments`: browser `GET`s fed in 61-byte segments that straddle every line boundary.
- `upload_fixed`: 16 KiB `Content-Length` uploads, each fed in 1000-byte reads and pulled as they
  arrive.
- `upload_chunked`: 16 KiB chunked uploads (1 KiB chunks), each fed in 1000-byte reads, so chunk-size
  lines straddle reads.
-/

/-- A synchronously driven server connection. -/
structure Conn where
  machine : Machine .receiving
  /-- Whether a request head was parsed and is still unanswered. -/
  pending : Bool := false
  /-- Number of body bytes of the pending request pulled so far. -/
  bodyBytes : Nat := 0
  bodyDone : Bool := false
  responses : Nat := 0
  outBytes : Nat := 0

def responseHead : Response.Head :=
  { headers := Headers.empty.insert .contentType (.mk "text/plain") }

/-- Answers the pending request with the number of body bytes it carried. -/
def respond (c : Conn) : Conn :=
  let data := (toString c.bodyBytes).toUTF8
  let machine := c.machine.setKnownSize (.fixed data.size)
    |>.send responseHead
    |>.sendData #[{ data }]
    |>.userClosedBody
  { c with machine, pending := false, bodyBytes := 0, bodyDone := false, responses := c.responses + 1 }

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
      c := { c with bodyBytes := c.bodyBytes + pulled.chunk.data.size, bodyDone := pulled.final }
      progress := true
  if c.pending && c.bodyDone && c.machine.isWaitingMessage then
    c := respond c
    progress := true
  if c.machine.halted || !progress then
    return c
  pump c

/-- Splits `data` into consecutive pieces of at most `size` bytes. -/
def segments (data : ByteArray) (size : Nat) : Array ByteArray := Id.run do
  let mut parts := #[]
  let mut pos := 0
  while pos < data.size do
    parts := parts.push (data.extract pos (pos + size))
    pos := pos + size
  return parts

def feedAll (c : Conn) (parts : Array ByteArray) : IO Conn :=
  parts.foldlM (fun c part => pump { c with machine := c.machine.feed part }) c

/--
Feeds `n - 1` copies of `keep` and then `close` as reads of `segmentSize` bytes. With `perRequest`,
every request starts a fresh read, as a lock-step client's would; otherwise reads straddle requests.
-/
def run (name : String) (n : Nat) (segmentSize : Nat) (perRequest : Bool) (keep close : String) :
    IO Unit := do
  let keep := keep.toUTF8
  let close := close.toUTF8
  let keepParts := segments keep segmentSize
  let closeParts := segments close segmentSize
  let mut pipelineParts := #[]
  unless perRequest do
    let mut input := ByteArray.empty
    for _ in *...(n - 1) do
      input := input ++ keep
    pipelineParts := segments (input ++ close) segmentSize

  let mut c : Conn := { machine := { config := Config.toH1Config { maxRequests := n + 1 } } }
  let t1 ← IO.monoNanosNow
  if perRequest then
    for i in *...n do
      c ← feedAll c (if i + 1 < n then keepParts else closeParts)
  else
    c ← feedAll c pipelineParts
  c ← pump { c with machine := c.machine.noMoreInput }
  let t2 ← IO.monoNanosNow

  unless c.responses == n ∧ c.machine.halted do
    throw <| .userError s!"{name}: expected {n} responses, got {c.responses}"
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

  run "get_browser_bytes" (n / 10 + 1) 1 false (browserGet "keep-alive") (browserGet "close")
  run "get_browser_segments" n 61 false (browserGet "keep-alive") (browserGet "close")

  let body := String.ofList (List.replicate 16384 'x')
  let fixed (extra : String) :=
    s!"POST /upload HTTP/1.1\r\nHost: example.com\r\nContent-Length: {body.utf8ByteSize}\r\n{extra}\r\n{body}"
  run "upload_fixed" n 1000 true (fixed "") (fixed "Connection: close\r\n")

  let chunk := s!"400\r\n{String.ofList (List.replicate 1024 'y')}\r\n"
  let chunkedBody := String.join (List.replicate 16 chunk) ++ "0\r\n\r\n"
  let chunked (extra : String) :=
    s!"POST /upload HTTP/1.1\r\nHost: example.com\r\nTransfer-Encoding: chunked\r\n{extra}\r\n{chunkedBody}"
  run "upload_chunked" n 1000 true (chunked "") (chunked "Connection: close\r\n")
