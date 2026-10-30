import Std.Http.Data.Body

/-!
Tests replayability for HTTP bodies, including reset behavior for full and empty bodies and
erased replayability through `Body.Any`.
-/

open Std.Async
open Std.Http
open Std.Http.Body

-- resetInPlace lets a body be read again after being consumed

def fullResetInPlaceAfterRead : Async Unit := do
  let full ← Body.Full.ofString "reset"
  let first ← full.recv
  assert! first.isSome
  assert! (← full.recv).isNone
  assert! (← full.isClosed)
  Replayable.resetInPlace full
  assert! !(← full.isClosed)
  let second ← full.recv
  assert! second.isSome
  assert! second.get!.data == "reset".toUTF8

#eval fullResetInPlaceAfterRead.block

-- resetInPlace after close restores readability

def fullResetInPlaceAfterClose : Async Unit := do
  let full ← Body.Full.ofString "revive"
  full.close
  assert! (← full.isClosed)
  Replayable.resetInPlace full
  let r ← full.recv
  assert! r.isSome
  assert! r.get!.data == "revive".toUTF8

#eval fullResetInPlaceAfterClose.block

-- resetInPlace on a fresh body is a no-op: body is still readable

def fullResetInPlaceOnFresh : Async Unit := do
  let full ← Body.Full.ofString "fresh"
  Replayable.resetInPlace full
  let r ← full.recv
  assert! r.isSome
  assert! r.get!.data == "fresh".toUTF8

#eval fullResetInPlaceOnFresh.block

-- An empty Full body is closed after reaching EOF and reset makes it fresh again

def fullEmptyIsClosedAfterRead : Async Unit := do
  let full ← Body.Full.ofByteArray ByteArray.empty
  assert! !(← full.isClosed)
  assert! (← full.recv).isNone
  assert! (← full.isClosed)
  Replayable.resetInPlace full
  assert! !(← full.isClosed)

#eval fullEmptyIsClosedAfterRead.block

-- resetInPlace can be called multiple times

def fullResetInPlaceMultiple : Async Unit := do
  let full ← Body.Full.ofString "multi"
  for _ in List.range 3 do
    let _ ← full.recv
    Replayable.resetInPlace full
  let r ← full.recv
  assert! r.isSome
  assert! r.get!.data == "multi".toUTF8

#eval fullResetInPlaceMultiple.block

-- resetInPlace restores the known size after reads and closes

def fullResetInPlaceKnownSize : Async Unit := do
  let full ← Body.Full.ofString "sized"
  assert! (← full.getKnownSize) == some (.fixed 5)
  let _ ← full.recv
  assert! (← full.getKnownSize) == some (.fixed 0)
  Replayable.resetInPlace full
  assert! (← full.getKnownSize) == some (.fixed 5)
  full.close
  assert! (← full.getKnownSize) == some (.fixed 0)
  Replayable.resetInPlace full
  assert! (← full.getKnownSize) == some (.fixed 5)

#eval fullResetInPlaceKnownSize.block

-- Empty.resetInPlace is a no-op; body remains at EOF

def emptyResetInPlace : Async Unit := do
  let e : Body.Empty := {}
  Replayable.resetInPlace e
  assert! (← e.recv).isNone

#eval emptyResetInPlace.block

/-! ## Body.Any — reset? action -/

-- Any wrapping a Full via Coe carries a reset action

def anyFromFullIsReplayable : Async Unit := do
  let full ← Body.Full.ofString "r"
  let any : Body.Any := full
  assert! any.reset?.isSome

#eval anyFromFullIsReplayable.block

-- Any wrapping a Stream (non-replayable) has no reset action

def anyFromStreamNotReplayable : Async Unit := do
  let stream ← Body.mkStream
  let any := Body.Any.ofBody stream
  assert! any.reset?.isNone

#eval anyFromStreamNotReplayable.block

-- Any wrapping an Empty via Coe carries a reset action: an empty body is trivially
-- replayable because reset is a no-op.

def anyFromEmptyIsReplayable : Async Unit := do
  let e : Body.Empty := {}
  let any : Body.Any := e
  assert! any.reset?.isSome
  any.reset?.getD (pure ())
  assert! (← any.recv).isNone

#eval anyFromEmptyIsReplayable.block

-- Any.ofReplayableBody sets reset? and replaying re-reads from the start

def anyReplayableResetInPlace : Async Unit := do
  let full ← Body.Full.ofString "via-any"
  let any := Body.Any.ofReplayableBody full
  assert! any.reset?.isSome
  let r1 ← any.recv
  assert! r1.isSome
  assert! r1.get!.data == "via-any".toUTF8
  any.reset?.getD (pure ())
  let r2 ← any.recv
  assert! r2.isSome
  assert! r2.get!.data == "via-any".toUTF8

#eval anyReplayableResetInPlace.block

-- Any.ofBody does not claim replayability, even for an underlying replayable body

def anyOfBodyFullNotReplayable : Async Unit := do
  let full ← Body.Full.ofString "manual"
  let any := Body.Any.ofBody full
  assert! any.reset?.isNone
  let first ← any.recv
  assert! first.isSome
  any.reset?.getD (pure ())
  assert! (← any.recv).isNone

#eval anyOfBodyFullNotReplayable.block

-- The reset action of a non-replayable Any is absent; running the default is a no-op

def anyNonReplayableResetIsNoop : Async Unit := do
  let stream ← Body.mkStream
  let any := Body.Any.ofBody stream
  any.reset?.getD (pure ())  -- should not throw
  assert! any.reset?.isNone

#eval anyNonReplayableResetIsNoop.block
