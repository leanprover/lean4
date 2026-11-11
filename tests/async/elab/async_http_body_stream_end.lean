import Std.Http

open Std.Async
open Std Http

/-!
Tests how a `Body.Stream` ends:
- bytes an incomplete `send` already accepted are delivered before the end of the stream, whether a
  reader is already waiting or not, and before the error of `closeWithError`;
- `readAll` in `ContextAsync` throws when the context is cancelled before the body ends, instead of
  returning the bytes read so far as if they were the whole body.
-/

def expect (cond : Bool) (msg : String) : IO Unit :=
  unless cond do throw (IO.userError msg)

def text (chunk : Option Chunk) : Option String :=
  chunk.map (String.fromUTF8! ·.data)

-- No reader waits when the stream closes.
#eval show IO Unit from Async.block do
  let s ← Body.mkStream
  s.send (Chunk.ofByteArray "abc".toUTF8) (incomplete := true)
  s.close
  let first ← s.recv
  expect (text first == some "abc") s!"after close: first recv {text first}"
  let second ← s.recv
  expect second.isNone s!"after close: second recv {text second}"

-- A reader already waits when the stream closes.
#eval show IO Unit from Async.block do
  let s ← Body.mkStream
  s.send (Chunk.ofByteArray "abc".toUTF8) (incomplete := true)
  let pending ← async s.recv
  sleep 20
  s.close
  let first ← await pending
  expect (text first == some "abc") s!"waiting reader: got {text first}"

-- `closeWithError` delivers the accepted bytes, then the error.
#eval show IO Unit from Async.block do
  let s ← Body.mkStream
  s.send (Chunk.ofByteArray "abc".toUTF8) (incomplete := true)
  s.closeWithError (.userError "peer went away")
  let first ← s.recv
  expect (text first == some "abc") s!"closeWithError: first recv {text first}"
  let second : Except String (Option Chunk) ←
    try pure (.ok (← s.recv)) catch e => pure (.error (toString e))
  match second with
  | .error _ => pure ()
  | .ok chunk => throw (IO.userError s!"closeWithError: expected the error, got {text chunk}")

-- The context is cancelled after the first chunk, while `readAll` waits for the rest.
#eval show IO Unit from Async.block do
  let ctx ← CancellationContext.new
  let s ← Body.mkStream
  s.setKnownSize (some (.fixed 10))
  background do
    s.send (Chunk.ofByteArray "abc".toUTF8)
    sleep 50
    ctx.cancel .shutdown
  let read : ContextAsync (Except String ByteArray) := do
    try
      return .ok (← s.readAll)
    catch e =>
      return .error (toString e)
  match ← read ctx with
  | .error _ => pure ()
  | .ok bytes => throw (IO.userError s!"cancelled readAll returned {String.fromUTF8! bytes |>.quote} as the whole body")
  -- Control: `readAll` in `Async` reads to the end.
  let s ← Body.mkStream
  background do
    s.send (Chunk.ofByteArray "abc".toUTF8)
    s.close
  let bytes : ByteArray ← s.readAll
  expect (bytes == "abc".toUTF8) "readAll in Async"
