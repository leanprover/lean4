/-
Copyright (c) 2020 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Wojciech Nawrocki, Marc Huisinga
-/
prelude
import Lean.Language.Lean
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

-- TEMP: translate from new heterogeneous snapshot tree to old homogeneous async list
private partial def mkCmdSnaps (initSnap : Language.Lean.InitialSnapshot) :
    AsyncList ElabTaskError Snapshot := Id.run do
  let some headerParsed := initSnap.success? | return .nil
  .delayed <| headerParsed.processed.task.bind fun headerProcessed => Id.run do
    let some headerSuccess := headerProcessed.success? | return .pure <| .ok .nil
    return .pure <| .ok <| .cons {
      stx := initSnap.stx
      mpState := headerParsed.parserState
      cmdState := headerSuccess.cmdState
    } <| .delayed <| headerSuccess.next.task.bind go
where go cmdParsed :=
  cmdParsed.data.sig.task.bind fun sig =>
    sig.finished.task.map fun finished =>
      .ok <| .cons {
        stx := cmdParsed.data.stx
        mpState := cmdParsed.data.parserState
        cmdState := finished.cmdState
      } (match cmdParsed.next? with
        | some next => .delayed <| next.task.bind go
        | none => .nil)

/-- A map from Diagnostics ID to resulting interactive objects. -/
abbrev DiagnosticsCache := RBMap Nat (Array Widget.InteractiveDiagnostic) compare

/--
A document bundled with processing information. Turned into `EditableDocument` as soon as the
reporter task has been started.
-/
structure EditableDocumentCore where
  /-- The document. -/
  meta       : DocumentMeta
  /-- Initial processing snapshot. -/
  -- TODO: generalize to other languages by moving request handlers into `Language`
  initSnap : Language.Lean.InitialSnapshot
  /-- Old representation for backward compatibility. -/
  cmdSnaps : AsyncList ElabTaskError Snapshot := mkCmdSnaps initSnap
  /--
  Interactive versions of diagnostics reported so far. Filled by `reportSnapshots` and read by
  `handleGetInteractiveDiagnosticsRequest`.
  -/
  diagnosticsRef : IO.Ref (Array Widget.InteractiveDiagnostic)

/-- `EditableDocumentCore` with reporter task. -/
structure EditableDocument extends EditableDocumentCore where
  /--
    Task reporting processing status back to client. We store it here for implementing
    `waitForDiagnostics`. -/
  reporter : Task Unit

namespace EditableDocument

/-- Construct a VersionedTextDocumentIdentifier from an EditableDocument --/
def versionedIdentifier (ed : EditableDocument) : Lsp.VersionedTextDocumentIdentifier := {
  uri := ed.meta.uri
  version? := some ed.meta.version
}

end EditableDocument

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
