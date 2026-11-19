import Std.Http

open Std Http Protocol.H1

/-!
Benchmarks the response-writing side of the sans-I/O HTTP/1.1 server state machine: each `GET` of
a pipeline is answered with a body streamed through `sendData`, stepping the machine after every
chunk as the connection loop does.

- `chunked_large`: 128 chunks of 4 KiB with unknown length, so chunked transfer encoding is used.
- `fixed_large`: the same 128 chunks with a known `Content-Length`.
- `chunked_small`: 256 chunks of 16 bytes (event-stream style writes).
-/

/-- A synchronously driven server connection. -/
structure Conn where
  machine : Machine .receiving
  /-- Whether a request was fully read and is still unanswered. -/
  pending : Bool := false
  responses : Nat := 0
  outBytes : Nat := 0

def responseHead : Response.Head :=
  { headers := Headers.empty.insert .contentType (.mk "application/octet-stream") }

/-- Answers the pending request by streaming `count` copies of `chunk`. -/
def respond (count : Nat) (chunk : Chunk) (knownSize : Bool) (c : Conn) : Conn := Id.run do
  let mut machine := c.machine
  if knownSize then
    machine := machine.setKnownSize (.fixed (count * chunk.data.size))
  machine := machine.send responseHead
  let mut outBytes := c.outBytes
  for _ in *...count do
    let (next, res) := (machine.sendData #[chunk]).step
    machine := next
    outBytes := outBytes + res.output.size
  return { c with machine := machine.userClosedBody, outBytes, pending := false, responses := c.responses + 1 }

/-- Steps the machine until it halts or needs more input, answering each complete request. -/
partial def pump (answer : Conn → Conn) (c : Conn) : IO Conn := do
  let (machine, res) := c.machine.step
  let mut c := { c with machine, outBytes := c.outBytes + res.output.size }
  let mut progress := res.output.size != 0
  for event in res.events do
    match event with
    | .failed err => throw <| .userError s!"machine failed: {err}"
    | .needMoreData _ => pure ()
    | _ => progress := true
  while c.machine.canPullBodyNow do
    let (machine, pulled?) := c.machine.pullBody
    c := { c with machine }
    if let some pulled := pulled? then
      if pulled.final then
        c := { c with pending := true }
      progress := true
  if c.pending && c.machine.isWaitingMessage then
    c := answer c
    progress := true
  if c.machine.halted || !progress then
    return c
  pump answer c

def run (name : String) (n count chunkSize : Nat) (knownSize : Bool) : IO Unit := do
  let chunk : Chunk := { data := ByteArray.mk (Array.replicate chunkSize 'z'.toUInt8) }
  let keep := "GET /stream HTTP/1.1\r\nHost: example.com\r\n\r\n".toUTF8
  let mut input := ByteArray.empty
  for _ in *...(n - 1) do
    input := input ++ keep
  input := input ++ "GET /stream HTTP/1.1\r\nHost: example.com\r\nConnection: close\r\n\r\n".toUTF8

  let machine : Machine .receiving := { config := Config.toH1Config { maxRequests := n + 1 } }
  let t1 ← IO.monoNanosNow
  let c ← pump (respond count chunk knownSize) { machine := machine.feed input |>.noMoreInput }
  let t2 ← IO.monoNanosNow

  -- A chunk frame adds at least a hex size and two line breaks; a fixed body adds only the head.
  let framed :=
    if knownSize then n * count * chunkSize < c.outBytes ∧ c.outBytes ≤ n * (count * chunkSize + 256)
    else c.outBytes ≥ n * count * (chunkSize + 6)
  unless c.responses == n ∧ c.machine.halted ∧ framed do
    throw <| .userError s!"{name}: expected {n} framed responses, got {c.responses} in {c.outBytes} bytes"
  IO.println s!"measurement: {name} {(t2 - t1).toFloat / 1000000000.0} s"

def main (args : List String) : IO Unit := do
  let n := args[0]!.toNat!
  run "chunked_large" n 128 4096 false
  run "fixed_large" n 128 4096 true
  run "chunked_small" n 256 16 false
