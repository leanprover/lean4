import Std.Http

open Std Http Protocol.H1

/-!
Benchmarks the sans-I/O HTTP/1.1 server state machine when input arrives in pieces, as it does
from a socket: every `feed` is followed by stepping the machine until it asks for more data, so the
cost of resuming a partially parsed message is measured.

- `get_browser_bytes`: browser `GET`s fed one byte at a time (worst case for resumption).
- `get_browser_segments`: browser `GET`s fed in 61-byte segments, so reads end mid-line and
  straddle requests.
- `upload_fixed`: 16 KiB `Content-Length` uploads, each fed in 1000-byte reads and pulled as they
  arrive.
- `upload_chunked`: 16 KiB chunked uploads (1 KiB chunks), each read ending two bytes into a
  chunk-size line, so every size line is resumed.
-/

/-- A synchronously driven server connection. -/
structure Conn where
  machine : Machine .receiving
  /-- Whether a request head was parsed and is still unanswered. -/
  pending : Bool := false
  /-- Number of body bytes of the pending request pulled so far. -/
  bodyBytes : Nat := 0
  bodyDone : Bool := false
  /-- Body bytes of all answered requests. -/
  received : Nat := 0
  /-- Header fields parsed across all requests. -/
  headers : Nat := 0
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
  { c with
    machine, pending := false, bodyBytes := 0, bodyDone := false, received := c.received + c.bodyBytes
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
    | .endHeaders head =>
      c := { c with pending := true, headers := c.headers + head.headers.size }
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

/-- Splits `data` at each of the ascending offsets `cuts`. -/
def cutAt (data : ByteArray) (cuts : Array Nat) : Array ByteArray := Id.run do
  let mut parts := #[]
  let mut pos := 0
  for cut in cuts do
    parts := parts.push (data.extract pos cut)
    pos := cut
  return parts.push (data.extract pos data.size)

/-- Returns the offset just past the blank line that ends the head of `request`. -/
def headEnd (request : ByteArray) : Nat := Id.run do
  for i in *...(request.size - 3) do
    if request[i]! == 13 && request[i + 1]! == 10 && request[i + 2]! == 13 && request[i + 3]! == 10 then
      return i + 4
  return request.size

def feedAll (c : Conn) (parts : Array ByteArray) : IO Conn :=
  parts.foldlM (fun c part => pump { c with machine := c.machine.feed part }) c

/--
Feeds `n - 1` copies of `keep` and then `close` as the reads produced by `split`, and checks that
each request carried `bodySize` body bytes and `keepHeaders` or `closeHeaders` header fields. With
`perRequest`, every request is split on its own, as a lock-step client's would be; otherwise the
whole pipeline is split, so reads straddle requests.
-/
def run (name : String) (n bodySize keepHeaders closeHeaders : Nat) (perRequest : Bool)
    (split : ByteArray → Array ByteArray) (keep close : String) : IO Unit := do
  let keep := keep.toUTF8
  let close := close.toUTF8
  let keepParts := split keep
  let closeParts := split close
  let mut pipelineParts := #[]
  unless perRequest do
    let mut input := ByteArray.empty
    for _ in *...(n - 1) do
      input := input ++ keep
    pipelineParts := split (input ++ close)

  let mut c : Conn := { machine := { config := Config.toH1Config { maxRequests := n + 1 } } }
  let t1 ← IO.monoNanosNow
  if perRequest then
    for i in *...n do
      c ← feedAll c (if i + 1 < n then keepParts else closeParts)
  else
    c ← feedAll c pipelineParts
  c ← pump { c with machine := c.machine.noMoreInput }
  let t2 ← IO.monoNanosNow

  -- Every response carries at least its status line, the headers set here and the decimal body
  -- size it answers with.
  let length := (toString bodySize).length
  let minResponse := length +
    s!"HTTP/1.1 200 OK\r\nContent-Type: text/plain\r\nContent-Length: {length}\r\n\r\n".utf8ByteSize
  let headers := (n - 1) * keepHeaders + closeHeaders
  unless c.responses == n ∧ c.machine.halted ∧ c.received == n * bodySize ∧ c.headers == headers ∧
      c.outBytes ≥ n * minResponse do
    throw <| .userError <|
      s!"{name}: expected {n} responses with {n * bodySize} body bytes and {headers} headers, got " ++
      s!"{c.responses} with {c.received} and {c.headers}, in {c.outBytes} output bytes"
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

  run "get_browser_bytes" (n / 20 + 1) 0 10 10 false (segments · 1) (browserGet "keep-alive") (browserGet "close")
  run "get_browser_segments" n 0 10 10 false (segments · 61) (browserGet "keep-alive") (browserGet "close")

  let body := String.ofList (List.replicate 16384 'x')
  let fixed (extra : String) :=
    s!"POST /upload HTTP/1.1\r\nHost: example.com\r\nContent-Length: {body.utf8ByteSize}\r\n{extra}\r\n{body}"
  run "upload_fixed" n 16384 2 3 true (segments · 1000) (fixed "") (fixed "Connection: close\r\n")

  let chunk := s!"400\r\n{String.ofList (List.replicate 1024 'y')}\r\n"
  let chunkedBody := String.join (List.replicate 16 chunk) ++ "0\r\n\r\n"
  let chunked (extra : String) :=
    s!"POST /upload HTTP/1.1\r\nHost: example.com\r\nTransfer-Encoding: chunked\r\n{extra}\r\n{chunkedBody}"
  -- One cut two bytes into each of the 16 data chunks' size lines and into the last chunk's.
  let inSizeLines (request : ByteArray) :=
    cutAt request ((Array.range 17).map (headEnd request + · * chunk.utf8ByteSize + 2))
  run "upload_chunked" n 16384 2 3 true inSizeLines (chunked "") (chunked "Connection: close\r\n")
