import Std.Http

open Std.Async
open Std Http

/-!
Tests that a `Body.Stream` reassembles many pieces exactly: the pieces of an incomplete `send` are
joined in order into one chunk, carrying the extensions of the oldest piece that has any, whether
the chunk is completed by a `send` or by `close`; and `readAll` of many chunks returns every byte
in order and enforces `maximumSize` exactly. The pieces are joined once, so this is linear in the
body size; a test cannot bound that without timing, so it is checked by the audit probe instead.
-/

def expect (cond : Bool) (msg : String) : IO Unit :=
  unless cond do throw (IO.userError msg)

def piece (i : Nat) : ByteArray :=
  ByteArray.mk (Array.ofFn (n := 7) fun j => (i * 7 + j.val) % 251 |>.toUInt8)

def expected (n : Nat) : ByteArray := Id.run do
  let mut out := ByteArray.empty
  for i in [0:n] do out := out ++ piece i
  out

-- Many incomplete pieces, completed by a `send`.
#eval show IO Unit from Async.block do
  let s ← Body.mkStream
  let reader ← async s.recv
  for i in [0:300] do
    let chunk := Chunk.ofByteArray (piece i)
    let chunk := if i == 5 then chunk.insertExtension (.ofString! "first") (.ofString! "1")
      else if i == 9 then chunk.insertExtension (.ofString! "second") (.ofString! "2")
      else chunk
    s.send chunk (incomplete := true)
  s.send (Chunk.ofByteArray (piece 300))
  let some chunk ← await reader | throw (IO.userError "no chunk")
  expect (chunk.data == expected 301) s!"joined {chunk.data.size} bytes out of order"
  expect (chunk.extensions.map (·.1.value) == #["first"]) "extensions of the oldest piece"

-- Many incomplete pieces, completed by `close`.
#eval show IO Unit from Async.block do
  let s ← Body.mkStream
  for i in [0:300] do
    s.send (Chunk.ofByteArray (piece i)) (incomplete := true)
  s.close
  let some chunk ← s.recv | throw (IO.userError "pieces dropped by close")
  expect (chunk.data == expected 300) "pieces joined by close"
  expect (← s.recv).isNone "end of stream after the pieces"

-- `readAll` of many chunks, with and without an exact limit.
#eval show IO Unit from Async.block do
  let producer : Async Body.Stream := Body.stream fun s => do
    for i in [0:500] do s.send (Chunk.ofByteArray (piece i))
  let bytes : ByteArray ← (← producer).readAll
  expect (bytes == expected 500) "readAll bytes"
  let bytes : ByteArray ← (← producer).readAll (maximumSize := some (500 * 7))
  expect (bytes.size == 500 * 7) "limit equal to the size"
  let stream ← producer
  let over : Except IO.Error ByteArray ←
    try pure (.ok (← stream.readAll (maximumSize := some (500 * 7 - 1))))
    catch e => pure (.error e)
  expect (over matches .error _) "limit one below the size"
  let single : ByteArray ← (← Body.fromBytes (piece 1)).readAll
  expect (single == piece 1) "single chunk"
  let empty : ByteArray ← (← Body.empty).readAll
  expect empty.isEmpty "empty"
