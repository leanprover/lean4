/-
Copyright (c) 2020 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Wojciech Nawrocki, Marc Huisinga
-/
import Lean.Server.Utils
import Lean.Server.Snapshots
import Lean.Server.AsyncList
import Lean.Server.Rpc.Basic

namespace Lean.Server.FileWorker
open Snapshots
open IO

inductive ElabTaskError where
  | aborted
  | ioError (e : IO.Error)

instance : Coe IO.Error ElabTaskError :=
  ⟨ElabTaskError.ioError⟩

instance : MonadLift IO (EIO ElabTaskError) where
  monadLift act := act.toEIO (↑ ·)

structure CancelToken where
  ref : IO.Ref Bool

namespace CancelToken

def new : IO CancelToken :=
  CancelToken.mk <$> IO.mkRef false

def check [MonadExceptOf ElabTaskError m] [MonadLiftT (ST RealWorld) m] [Monad m] (tk : CancelToken) : m Unit := do
  let c ← tk.ref.get
  if c then
    throw ElabTaskError.aborted

def set (tk : CancelToken) : IO Unit :=
  tk.ref.set true

end CancelToken

-- TEMP: translate from new heterogeneous snapshot tree to old homegenous async list
private partial def mkCmdSnaps (initSnap : Language.Lean.InitialSnapshot) :
    AsyncList ElabTaskError Snapshot := Id.run do
  let some headerParsed := initSnap.success? | return .nil
  .delayed <| headerParsed.processed.task.bind fun headerProcessed => Id.run do
    let some headerSuccess := headerProcessed.success? | return .pure <| .ok .nil
    return .pure <| .ok <| .cons {
      stx := initSnap.stx
      mpState := headerParsed.parserState
      cmdState := headerSuccess.cmdState
      interactiveDiags := .empty  -- TODO
    } <| .delayed <| headerSuccess.next.task.bind go
where go cmdParsed :=
  cmdParsed.data.sig.task.bind fun sig =>
    sig.finished.task.map fun finished =>
      .ok <| .cons {
        stx := cmdParsed.data.stx
        mpState := cmdParsed.data.parserState
        cmdState := finished.cmdState
        interactiveDiags := .empty  -- TODO
      } (match cmdParsed.next? with
        | some next => .delayed <| next.task.bind go
        | none => .nil)

structure RpcSession where
  objects         : RpcObjectStore
  /-- The `IO.monoMsNow` time when the session expires. See `$/lean/rpc/keepAlive`. -/
  expireTime      : Nat

namespace RpcSession

def keepAliveTimeMs : Nat :=
  30000

def new : IO (UInt64 × RpcSession) := do
  /- We generate a random ID to ensure that session IDs do not repeat across re-initializations
  and worker restarts. Otherwise, the client may attempt to use outdated references. -/
  let newId ← ByteArray.toUInt64LE! <$> IO.getRandomBytes 8
  let newSesh := {
    objects := {}
    expireTime := (← IO.monoMsNow) + keepAliveTimeMs
  }
  return (newId, newSesh)

def keptAlive (monoMsNow : Nat) (s : RpcSession) : RpcSession :=
  { s with expireTime := monoMsNow + keepAliveTimeMs }

def hasExpired (s : RpcSession) : IO Bool :=
  return s.expireTime ≤ (← IO.monoMsNow)

end RpcSession

end Lean.Server.FileWorker
