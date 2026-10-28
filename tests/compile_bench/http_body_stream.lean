import Std.Http

open Std Async
open Std Http

/-!
Benchmarks the body types that carry data between the HTTP connection loop and handlers.

- `stream_handoff`: a producer task streams 1 KiB chunks through one rendezvous `Body.Stream` to a
  consumer, as the connection loop hands request bodies to a handler.
- `stream_read_all`: a fresh `Body.Stream` per request, filled with four chunks and collected with
  `readAll`, as handlers that read whole request bodies do.
- `full_response`: building a `Body.Full` text response and draining it, as the connection loop does
  for `Response.ok |>.text`.
-/

def chunk : Chunk := { data := ByteArray.mk (Array.replicate 1024 'b'.toUInt8) }

@[noinline]
def benchHandoff (n : Nat) : IO Nat := Async.block do
  let stream ← Body.mkStream
  let producer ← async do
    for _ in *...n do
      stream.send chunk
    stream.close
  let mut total := 0
  repeat
    match ← stream.recv with
    | some chunk => total := total + chunk.data.size
    | none => break
  await producer
  return total

@[noinline]
def benchReadAll (n : Nat) : IO Nat := Async.block do
  let mut total := 0
  for _ in *...n do
    let stream ← Body.mkStream
    let producer ← async do
      for _ in *...4 do
        stream.send chunk
      stream.close
    let body : ByteArray ← stream.readAll
    await producer
    total := total + body.size
  return total

@[noinline]
def benchFullResponse (n : Nat) : IO Nat := Async.block do
  let mut total := 0
  for i in *...n do
    let response ← Response.ok |>.text s!"hello, world {i % 10}"
    if let some (.fixed size) ← Body.getKnownSize response.body then
      total := total + size
    while true do
      match ← response.body.recv with
      | some chunk => total := total + chunk.data.size
      | none => break
  return total

def run (name : String) (expected : Nat) (act : IO Nat) : IO Unit := do
  let t1 ← IO.monoNanosNow
  let total ← act
  let t2 ← IO.monoNanosNow
  unless total == expected do
    throw <| .userError s!"{name}: expected {expected} bytes, got {total}"
  IO.println s!"measurement: {name} {(t2 - t1).toFloat / 1000000000.0} s"

def main (args : List String) : IO Unit := do
  let n := args[0]!.toNat!
  run "stream_handoff" (n * 1024) (benchHandoff n)
  run "stream_read_all" ((n / 4 + 1) * 4 * 1024) (benchReadAll (n / 4 + 1))
  run "full_response" (2 * n * 14) (benchFullResponse n)
