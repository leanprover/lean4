/-
Copyright (c) 2020 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Wojciech Nawrocki, Marc Huisinga
-/
module

prelude
public import Lean.Language.Lean.Types
public import Lean.Server.Snapshots
public import Lean.Server.AsyncList
public import Std.Sync.Mutex

public section

namespace Lean.Server.FileWorker
open Snapshots
open IO

-- TEMP: translate from new heterogeneous snapshot tree to old homogeneous async list
private partial def mkCmdSnaps (initSnap : Language.Lean.InitialSnapshot) :
    AsyncList IO.Error Snapshot := Id.run do
  let some headerParsed := initSnap.result? | return .nil
  .delayed <| headerParsed.processedSnap.task.asServerTask.bindCheap fun headerProcessed => Id.run do
    let some headerSuccess := headerProcessed.result? | return .pure <| .ok .nil
    return .pure <| .ok <| .cons {
      stx := initSnap.stx
      mpState := headerParsed.parserState
      cmdState := headerSuccess.cmdState
    } <| .delayed <| headerSuccess.firstCmdSnap.task.asServerTask.bindCheap go
where
  go cmdParsed :=
    cmdParsed.elabSnap.resultSnap.task.asServerTask.mapCheap fun result =>
      .ok <| .cons {
        stx := cmdParsed.stx
        mpState := cmdParsed.parserState
        cmdState := result.cmdState
      } (match cmdParsed.nextCmdSnap? with
        | some next => .delayed <| next.task.asServerTask.bindCheap go
        | none => .nil)

/--
Tracks diagnostics and incremental diagnostic reporting state for a single document version.

The sticky diagnostics are shared across all document versions via an `IO.Ref`, while per-version
diagnostics are stored directly. The whole state is wrapped in a `Std.Mutex` on
`EditableDocumentCore` to ensure atomic updates.
-/
structure DiagnosticsState where
  /--
  Diagnostics that persist across document versions (e.g. stale dependency warnings).
  Shared across all versions via an `IO.Ref`.
  -/
  stickyDiagsRef : IO.Ref (PersistentArray Widget.InteractiveDiagnostic)
  /-- Diagnostics accumulated during snapshot reporting. -/
  diags : PersistentArray Widget.InteractiveDiagnostic := {}
  /-- Whether the next `publishDiagnostics` call should be incremental. -/
  isIncremental : Bool := false
  /-- Amount of diagnostics reported in `publishDiagnostics` so far. -/
  publishedDiagsAmount : Nat := 0

/--
A document bundled with processing information. Turned into `EditableDocument` as soon as the
reporter task has been started.
-/
structure EditableDocumentCore where
  /-- The document. -/
  «meta»   : DocumentMeta
  /-- Initial processing snapshot. -/
  initSnap : Language.Lean.InitialSnapshot
  /-- Old representation for backward compatibility. -/
  cmdSnaps : AsyncList IO.Error Snapshot := private_decl% mkCmdSnaps initSnap
  /-- Per-version diagnostics state, protected by a mutex. -/
  diagnosticsMutex : Std.Mutex DiagnosticsState

namespace EditableDocumentCore
open Widget

/-- Appends new non-sticky diagnostics. -/
def appendDiagnostics (doc : EditableDocumentCore) (diags : Array InteractiveDiagnostic) :
    BaseIO Unit :=
  doc.diagnosticsMutex.atomically do
    modify fun ds => { ds with diags := diags.foldl (init := ds.diags) fun acc d => acc.push d }

/--
Appends a sticky diagnostic and marks the next publish as non-incremental.
Removes any existing sticky diagnostic whose `message.stripTags` matches the new one.
-/
def appendStickyDiagnostic (doc : EditableDocumentCore) (diagnostic : InteractiveDiagnostic) :
    BaseIO Unit :=
  doc.diagnosticsMutex.atomically do
    let ds ← get
    ds.stickyDiagsRef.modify fun stickyDiags =>
      let stickyDiags := stickyDiags.filter
        (·.message.stripTags != diagnostic.message.stripTags)
      stickyDiags.push diagnostic
    set { ds with isIncremental := false }

/-- Returns all current diagnostics (sticky ++ doc). -/
def collectCurrentDiagnostics (doc : EditableDocumentCore) :
    BaseIO (PersistentArray InteractiveDiagnostic) :=
  doc.diagnosticsMutex.atomically do
    let ds ← get
    let stickyDiags ← ds.stickyDiagsRef.get
    return stickyDiags ++ ds.diags

/--
Creates a new `EditableDocumentCore` for a new document version, sharing the same sticky
diagnostics with the previous version.
-/
def update (doc : EditableDocumentCore) (newMeta : DocumentMeta)
    (newInitSnap : Language.Lean.InitialSnapshot) : BaseIO EditableDocumentCore := do
  let stickyDiagsRef ← doc.diagnosticsMutex.atomically do
    return (← get).stickyDiagsRef
  let diagnosticsMutex ← Std.Mutex.new { stickyDiagsRef }
  return { «meta» := newMeta, initSnap := newInitSnap, diagnosticsMutex }

/--
Collects diagnostics for a `textDocument/publishDiagnostics` notification, updates
the incremental tracking fields and writes the notification to the client.

When `incrementalDiagnosticSupport` is `true` and the state allows it, sends only
the newly added diagnostics with `isIncremental? := some true`. Otherwise, sends
all sticky and non-sticky diagnostics non-incrementally.

The state update and the write are performed atomically under the diagnostics mutex
to prevent reordering between concurrent publishers (the reporter task and the main thread).
-/
def publishDiagnostics (doc : EditableDocumentCore) (incrementalDiagnosticSupport : Bool)
    (writeDiagnostics : JsonRpc.Notification Lsp.PublishDiagnosticsParams → BaseIO Unit) :
    BaseIO Unit := do
  -- The mutex must be held across both the state update and the write to ensure that concurrent
  -- publishers (e.g. the reporter task and the main thread) cannot interleave their state reads
  -- and writes, which would reorder incremental/non-incremental messages and corrupt client state.
  doc.diagnosticsMutex.atomically do
    let ds ← get
    let useIncremental := incrementalDiagnosticSupport && ds.isIncremental
    let stickyDiags ← ds.stickyDiagsRef.get
    let diags := ds.diags
    let publishedDiagsAmount := ds.publishedDiagsAmount
    set <| { ds with publishedDiagsAmount := diags.size, isIncremental := true }
    let (diagsToSend, isIncremental) :=
      if useIncremental then
        let newDiags := diags.foldl (init := #[]) (start := publishedDiagsAmount) fun acc d =>
          acc.push d.toDiagnostic
        (newDiags, true)
      else
        let allDiags := stickyDiags.foldl (init := #[]) fun acc d =>
          acc.push d.toDiagnostic
        let allDiags := diags.foldl (init := allDiags) fun acc d =>
          acc.push d.toDiagnostic
        (allDiags, false)
    let isIncremental? :=
      if incrementalDiagnosticSupport then
        some isIncremental
      else
        none
    writeDiagnostics <| mkPublishDiagnosticsNotification doc.meta diagsToSend isIncremental?

end EditableDocumentCore

/-- `EditableDocumentCore` with reporter task. -/
structure EditableDocument extends EditableDocumentCore where
  /--
    Task reporting processing status back to client. We store it here for implementing
    `waitForDiagnostics`. -/
  reporter : ServerTask Unit

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

def new (wireFormat : Lsp.RpcWireFormat) : IO (UInt64 × RpcSession) := do
  /- We generate a random ID to ensure that session IDs do not repeat across re-initializations
  and worker restarts. Otherwise, the client may attempt to use outdated references. -/
  let newId ← ByteArray.toUInt64LE! <$> IO.getRandomBytes 8
  let newSesh := {
    objects := { wireFormat }
    expireTime := (← IO.monoMsNow) + keepAliveTimeMs
  }
  return (newId, newSesh)

def keptAlive (monoMsNow : Nat) (s : RpcSession) : RpcSession :=
  { s with expireTime := monoMsNow + keepAliveTimeMs }

def hasExpired (s : RpcSession) : IO Bool :=
  return s.expireTime ≤ (← IO.monoMsNow)

end RpcSession

end Lean.Server.FileWorker
