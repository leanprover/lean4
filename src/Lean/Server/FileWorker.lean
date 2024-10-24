/-
Copyright (c) 2020 Marc Huisinga. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Marc Huisinga, Wojciech Nawrocki
-/
prelude
import Init.System.IO
import Init.Data.Channel

import Lean.Data.RBMap
import Lean.Environment

import Lean.Data.Lsp
import Lean.Data.Json.FromToJson

import Lean.Util.FileSetupInfo
import Lean.LoadDynlib
import Lean.Language.Lean

import Lean.Server.Utils
import Lean.Server.AsyncList
import Lean.Server.References

import Lean.Server.FileWorker.Utils
import Lean.Server.FileWorker.RequestHandling
import Lean.Server.FileWorker.WidgetRequests
import Lean.Server.FileWorker.SetupFile
import Lean.Server.Rpc.Basic
import Lean.Widget.InteractiveDiagnostic
import Lean.Server.Completion.ImportCompletion

/-!
For general server architecture, see `README.md`. For details of IPC communication, see `Watchdog.lean`.
This module implements per-file worker processes.

File processing and requests+notifications against a file should be concurrent for two reasons:
- By the LSP standard, requests should be cancellable.
- Since Lean allows arbitrary user code to be executed during elaboration via the tactic framework,
  elaboration can be extremely slow and even not halt in some cases. Users should be able to
  work with the file while this is happening, e.g. make new changes to the file or send requests.

To achieve these goals, elaboration is executed in a chain of tasks, where each task corresponds to
the elaboration of one command. When the elaboration of one command is done, the next task is spawned.
On didChange notifications, we search for the task in which the change occurred. If we stumble across
a task that has not yet finished before finding the task we're looking for, we terminate it
and start the elaboration there, otherwise we start the elaboration at the task where the change occurred.

Requests iterate over tasks until they find the command that they need to answer the request.
In order to not block the main thread, this is done in a request task.
If a task that the request task waits for is terminated, a change occurred somewhere before the
command that the request is looking for and the request sends a "content changed" error.
-/

namespace Lean.Server.FileWorker

open Lsp
open IO
open Snapshots
open JsonRpc

open Widget in

structure WorkerContext where
  /-- Synchronized output channel for LSP messages. Notifications for outdated versions are
    discarded on read. -/
  chanOut              : IO.Channel JsonRpc.Message
  /--
  Latest document version received by the client, used for filtering out notifications from
  previous versions.
  -/
  maxDocVersionRef     : IO.Ref Int
  freshRequestIdRef    : IO.Ref Int
  /--
  Channel that receives a message for every a `$/lean/fileProgress` notification, indicating whether
  the notification suggests that the file is currently being processed.
  -/
  chanIsProcessing     : IO.Channel Bool
  /--
  Diagnostics that are included in every single `textDocument/publishDiagnostics` notification.
  -/
  stickyDiagnosticsRef : IO.Ref (Array InteractiveDiagnostic)
  hLog                 : FS.Stream
  initParams           : InitializeParams
  processor            : Parser.InputContext → BaseIO Lean.Language.Lean.InitialSnapshot
  clientHasWidgets     : Bool
  /--
  Options defined on the worker cmdline (i.e. not including options from `setup-file`), used for
  context-free tasks such as editing delay.
  -/
  cmdlineOpts          : Options

/-! # Asynchronous snapshot elaboration -/

section Elab
  -- Placed here instead of Lean.Server.Utils because of an import loop
  private def mkIleanInfoNotification (method : String) (m : DocumentMeta)
      (trees : Array Elab.InfoTree) : BaseIO (JsonRpc.Notification Lsp.LeanIleanInfoParams) := do
    let references ← findModuleRefs m.text trees (localVars := true) |>.toLspModuleRefs
    let param := { version := m.version, references }
    return { method, param }

  private def mkIleanInfoUpdateNotification : DocumentMeta → Array Elab.InfoTree →
      BaseIO (JsonRpc.Notification Lsp.LeanIleanInfoParams) :=
    mkIleanInfoNotification "$/lean/ileanInfoUpdate"

  private def mkIleanInfoFinalNotification : DocumentMeta → Array Elab.InfoTree →
      BaseIO (JsonRpc.Notification Lsp.LeanIleanInfoParams) :=
    mkIleanInfoNotification "$/lean/ileanInfoFinal"

  /-- Yields a `$/lean/importClosure` notification. -/
  private def mkImportClosureNotification (importClosure : Array DocumentUri)
      : JsonRpc.Notification Lsp.LeanImportClosureParams := {
    method := "$/lean/importClosure",
    param := { importClosure : LeanImportClosureParams }
  }

  /-- State of `reportSnapshots`. -/
  private structure ReportSnapshotsState where
    /-- Whether we have waited for a snapshot to finish at least once (see debouncing below). -/
    hasBlocked := false
    /-- All info trees encountered so far. -/
    allInfoTrees : Array Elab.InfoTree := #[]
    /-- New info trees encountered since we last sent a .ilean update notification. -/
    newInfoTrees : Array Elab.InfoTree := #[]
    /-- Whether we encountered any snapshot with `Snapshot.isFatal`. -/
    hasFatal := false
    /--
    Last `Snapshot.range?` encountered that was not `none`, if any. We use this as a fallback when
    reporting progress as we should always report *some* range when waiting on a task.
    -/
    lastRange? : Option String.Range := none
  deriving Inhabited

  register_builtin_option server.reportDelayMs : Nat := {
    defValue := 200
    group := "server"
    descr := "(server) time in milliseconds to wait before reporting progress and diagnostics on \
      document edit in order to reduce flickering

This option can only be set on the command line, not in the lakefile or via `set_option`."
  }

  /--
  Type of state stored in `Snapshot.Diagnostics.cacheRef?`.

  See also section "Communication" in Lean/Server/README.md.
  -/
  structure MemorizedInteractiveDiagnostics where
    diags : Array Widget.InteractiveDiagnostic
  deriving TypeName

  /--
  Sends a `textDocument/publishDiagnostics` notification to the client that contains the diagnostics
  in `ctx.stickyDiagnosticsRef` and `doc.diagnosticsRef`.
  -/
  private def publishDiagnostics (ctx : WorkerContext) (doc : EditableDocumentCore)
      : BaseIO Unit := do
    let stickyInteractiveDiagnostics ← ctx.stickyDiagnosticsRef.get
    let docInteractiveDiagnostics ← doc.diagnosticsRef.get
    let diagnostics :=
      stickyInteractiveDiagnostics ++ docInteractiveDiagnostics
      |>.map (·.toDiagnostic)
    let notification := mkPublishDiagnosticsNotification doc.meta diagnostics
    ctx.chanOut.send notification

  open Language in
  /--
    Reports status of a snapshot tree incrementally to the user: progress,
    diagnostics, .ilean reference information.

    See also section "Communication" in Lean/Server/README.md.

    Debouncing: we only report information
    * after first waiting for `reportDelayMs`, to give trivial tasks a chance to finish
    * when first blocking, i.e. not before skipping over any unchanged snapshots and such trivial
      tasks
    * afterwards, each time new information is found in a snapshot
    * at the very end, if we never blocked (e.g. emptying a file should make
      sure to empty diagnostics as well eventually) -/
  private partial def reportSnapshots (ctx : WorkerContext) (doc : EditableDocumentCore)
      (cancelTk : CancelToken) : BaseIO (Task Unit) := do
    let t ← BaseIO.asTask do
      IO.sleep (server.reportDelayMs.get ctx.cmdlineOpts).toUInt32
    BaseIO.bindTask t fun _ => do
      BaseIO.bindTask (← go (toSnapshotTree doc.initSnap) {}) fun st => do
        if (← cancelTk.isSet) then
          return .pure ()

        -- callback at the end of reporting
        if st.hasFatal then
          ctx.chanOut.send <| mkFileProgressAtPosNotification doc.meta 0 .fatalError
        else
          ctx.chanOut.send <| mkFileProgressDoneNotification doc.meta
        unless st.hasBlocked do
          publishDiagnostics ctx doc
        -- This will overwrite existing ilean info for the file, in case something
        -- went wrong during the incremental updates.
        ctx.chanOut.send (← mkIleanInfoFinalNotification doc.meta st.allInfoTrees)
        return .pure ()
  where
    go (node : SnapshotTree) (st : ReportSnapshotsState) : BaseIO (Task ReportSnapshotsState) := do
      if node.element.diagnostics.msgLog.hasUnreported then
        let diags ←
          if let some memorized ← node.element.diagnostics.interactiveDiagsRef?.bindM fun ref => do
              return (← ref.get).bind (·.get? MemorizedInteractiveDiagnostics) then
            pure memorized.diags
          else
            let diags ← node.element.diagnostics.msgLog.toArray.mapM
              (Widget.msgToInteractiveDiagnostic doc.meta.text · ctx.clientHasWidgets)
            if let some cacheRef := node.element.diagnostics.interactiveDiagsRef? then
              cacheRef.set <| some <| .mk { diags : MemorizedInteractiveDiagnostics }
            pure diags
        doc.diagnosticsRef.modify (· ++ diags)
        if st.hasBlocked then
          publishDiagnostics ctx doc

      let mut st := { st with hasFatal := st.hasFatal || node.element.isFatal }

      if let some itree := node.element.infoTree? then
        let mut newInfoTrees := st.newInfoTrees.push itree
        if st.hasBlocked then
          ctx.chanOut.send (← mkIleanInfoUpdateNotification doc.meta newInfoTrees)
          newInfoTrees := #[]
        st := { st with newInfoTrees, allInfoTrees := st.allInfoTrees.push itree }

      goSeq st node.children.toList

    goSeq (st : ReportSnapshotsState) :
        List (SnapshotTask SnapshotTree) → BaseIO (Task ReportSnapshotsState)
      | [] => return .pure st
      | t::ts => do
        let mut st := st
        st := { st with lastRange? := t.range? <|> st.lastRange? }
        unless (← IO.hasFinished t.task) do
          -- report *some* recent range even if `t.range?` is `none`; see also `State.lastRange?`
          if let some range := st.lastRange? then
            ctx.chanOut.send <| mkFileProgressAtPosNotification doc.meta range.start
          if !st.hasBlocked then
            publishDiagnostics ctx doc
            st := { st with hasBlocked := true }
        BaseIO.bindTask t.task fun t => do
          BaseIO.bindTask (← go t st) (goSeq · ts)
end Elab

-- Pending requests are tracked so they can be canceled
abbrev PendingRequestMap := RBMap RequestID (Task (Except IO.Error Unit)) compare

structure AvailableImportsCache where
  availableImports       : ImportCompletion.AvailableImports
  lastRequestTimestampMs : Nat

structure WorkerState where
  doc                : EditableDocument
  /-- Token flagged for aborting `doc.reporter` when a new document version comes in. -/
  reporterCancelTk   : CancelToken
  srcSearchPathTask  : Task SearchPath
  importCachingTask? : Option (Task (Except Error AvailableImportsCache))
  pendingRequests    : PendingRequestMap
  /-- A map of RPC session IDs. We allow asynchronous elab tasks and request handlers
  to modify sessions. A single `Ref` ensures atomic transactions. -/
  rpcSessions        : RBMap UInt64 (IO.Ref RpcSession) compare

abbrev WorkerM := ReaderT WorkerContext <| StateRefT WorkerState IO

/-- Makes sure we load imports at most once per process as they cannot be unloaded. -/
private builtin_initialize importsLoadedRef : IO.Ref Bool ← IO.mkRef false

open Language Lean in
/--
Callback from Lean language processor after parsing imports that requests necessary information from
Lake for processing imports.
-/
def setupImports (meta : DocumentMeta) (cmdlineOpts : Options) (chanOut : Channel JsonRpc.Message)
    (srcSearchPathPromise : Promise SearchPath) (stx : Syntax) :
    Language.ProcessingT IO (Except Language.Lean.HeaderProcessedSnapshot SetupImportsResult) := do
  let importsAlreadyLoaded ← importsLoadedRef.modifyGet ((·, true))
  if importsAlreadyLoaded then
    -- As we never unload imports in the server, we should not run the code below twice in the
    -- same process and instead ask the watchdog to restart the worker
    IO.sleep 200  -- give user time to make further edits before restart
    unless (← IO.checkCanceled) do
      IO.Process.exit 2  -- signal restart request to watchdog
    -- should not be visible to user as task is already canceled
    return .error { diagnostics := .empty, result? := none }

  let imports := Elab.headerToImports stx
  let fileSetupResult ← setupFile meta imports fun stderrLine => do
    let progressDiagnostic := {
      range      := ⟨⟨0, 0⟩, ⟨1, 0⟩⟩
      -- make progress visible anywhere in the file
      fullRange? := some ⟨⟨0, 0⟩, meta.text.utf8PosToLspPos meta.text.source.endPos⟩
      severity?  := DiagnosticSeverity.information
      message    := stderrLine
    }
    chanOut.send <| mkPublishDiagnosticsNotification meta #[progressDiagnostic]
  -- clear progress notifications in the end
  chanOut.send <| mkPublishDiagnosticsNotification meta #[]
  match fileSetupResult.kind with
  | .importsOutOfDate =>
    return .error {
      diagnostics := (← Language.diagnosticsOfHeaderError
        "Imports are out of date and must be rebuilt; \
          use the \"Restart File\" command in your editor.")
      result? := none
    }
  | .error msg =>
    return .error {
      diagnostics := (← diagnosticsOfHeaderError msg)
      result? := none
    }
  | _ => pure ()

  srcSearchPathPromise.resolve fileSetupResult.srcSearchPath

  let mainModuleName ← if let some path := System.Uri.fileUriToPath? meta.uri then
    EIO.catchExceptions (h := fun _ => pure Name.anonymous) do
      if let some mod ← searchModuleNameOfFileName path fileSetupResult.srcSearchPath then
        pure mod
      else
        moduleNameOfFileName path none
  else
    pure Name.anonymous

  -- override cmdline options with file options
  let opts := cmdlineOpts.mergeBy (fun _ _ fileOpt => fileOpt) fileSetupResult.fileOptions

  return .ok {
    mainModuleName
    opts
  }

/- Worker initialization sequence. -/
section Initialization
  def initializeWorker (meta : DocumentMeta) (o e : FS.Stream) (initParams : InitializeParams) (opts : Options)
      : IO (WorkerContext × WorkerState) := do
    let clientHasWidgets := initParams.initializationOptions?.bind (·.hasWidgets?) |>.getD false
    let maxDocVersionRef ← IO.mkRef 0
    let freshRequestIdRef ← IO.mkRef (0 : Int)
    let chanIsProcessing ← IO.Channel.new
    let stickyDiagnosticsRef ← IO.mkRef ∅
    let chanOut ← mkLspOutputChannel maxDocVersionRef chanIsProcessing
    let srcSearchPathPromise ← IO.Promise.new

    let processor := Language.Lean.process (setupImports meta opts chanOut srcSearchPathPromise)
    let processor ← Language.mkIncrementalProcessor processor
    let initSnap ← processor meta.mkInputContext
    let _ ← IO.mapTask (t := srcSearchPathPromise.result) fun srcSearchPath => do
      let importClosure := getImportClosure? initSnap
      let importClosure ← importClosure.filterMapM (documentUriFromModule srcSearchPath ·)
      chanOut.send <| mkImportClosureNotification importClosure
    let ctx := {
      chanOut
      hLog := e
      initParams
      processor
      clientHasWidgets
      maxDocVersionRef
      freshRequestIdRef
      chanIsProcessing
      cmdlineOpts := opts
      stickyDiagnosticsRef
    }
    let doc : EditableDocumentCore := {
      meta, initSnap
      diagnosticsRef := (← IO.mkRef ∅)
    }
    let reporterCancelTk ← CancelToken.new
    let reporter ← reportSnapshots ctx doc reporterCancelTk
    return (ctx, {
      doc := { doc with reporter }
      reporterCancelTk
      srcSearchPathTask  := srcSearchPathPromise.result
      pendingRequests    := RBMap.empty
      rpcSessions        := RBMap.empty
      importCachingTask? := none
    })
  where
    /-- Creates an LSP message output channel along with a reader that sends out read messages on
        the output FS stream after discarding outdated notifications. This is the only component of
        the worker with access to the output stream, so we can synchronize messages from parallel
        elaboration tasks here. -/
    mkLspOutputChannel maxDocVersion chanIsProcessing : IO (IO.Channel JsonRpc.Message) := do
      let chanOut ← IO.Channel.new
      let _ ← chanOut.forAsync (prio := .dedicated) fun msg => do
        -- discard outdated notifications; note that in contrast to responses, notifications can
        -- always be silently discarded
        let version? : Option Int := do match msg with
          | .notification "textDocument/publishDiagnostics" (some params) =>
            let params : PublishDiagnosticsParams ← fromJson? (toJson params) |>.toOption
            params.version?
          | .notification "$/lean/fileProgress" (some params) =>
            let params : LeanFileProgressParams ← fromJson? (toJson params) |>.toOption
            params.textDocument.version?
          | _ => none
        if let some version := version? then
          if version < (← maxDocVersion.get) then
            return
          -- note that because of `server.reportDelayMs`, we cannot simply set `maxDocVersion` here
          -- as that would allow outdated messages to be reported until the delay is over
        o.writeLspMessage msg |>.catchExceptions (fun _ => pure ())
        if let .notification "$/lean/fileProgress" (some params) := msg then
          if let some (params : LeanFileProgressParams) := fromJson? (toJson params) |>.toOption then
            chanIsProcessing.send (! params.processing.isEmpty)
      return chanOut

    getImportClosure? (snap : Language.Lean.InitialSnapshot) : Array Name := Id.run do
      let some snap := snap.result?
        | return #[]
      let some snap ← snap.processedSnap.get.result?
        | return #[]
      let importClosure := snap.cmdState.env.allImportedModuleNames
      return importClosure

end Initialization

section ServerRequests
  def sendServerRequest [ToJson α]
      (ctx    : WorkerContext)
      (method : String)
      (param  : α)
      : IO Unit := do
    let freshRequestId ← ctx.freshRequestIdRef.modifyGet fun freshRequestId =>
      (freshRequestId, freshRequestId + 1)
    let r : JsonRpc.Request α := ⟨freshRequestId, method, param⟩
    ctx.chanOut.send r
end ServerRequests

section Updates
  def updatePendingRequests (map : PendingRequestMap → PendingRequestMap) : WorkerM Unit := do
    modify fun st => { st with pendingRequests := map st.pendingRequests }

  /-- Given the new document, updates editable doc state. -/
  def updateDocument (meta : DocumentMeta) : WorkerM Unit := do
    (← get).reporterCancelTk.set
    let ctx ← read
    let initSnap ← ctx.processor meta.mkInputContext
    let doc : EditableDocumentCore := {
      meta, initSnap
      diagnosticsRef := (← IO.mkRef ∅)
    }
    let reporterCancelTk ← CancelToken.new
    let reporter ← reportSnapshots ctx doc reporterCancelTk
    modify fun st => { st with doc := { doc with reporter }, reporterCancelTk }
    -- we assume version updates are monotonous and that we are on the main thread
    ctx.maxDocVersionRef.set meta.version
end Updates

/- Notifications are handled in the main thread. They may change global worker state
such as the current file contents. -/
section NotificationHandling
  def handleDidChange (p : DidChangeTextDocumentParams) : WorkerM Unit := do
    let docId := p.textDocument
    let changes := p.contentChanges
    let oldDoc := (←get).doc
    let newVersion := docId.version?.getD 0
    if ¬ changes.isEmpty then
      let newDocText := foldDocumentChanges changes oldDoc.meta.text
      updateDocument ⟨docId.uri, newVersion, newDocText, oldDoc.meta.dependencyBuildMode⟩

  def handleCancelRequest (p : CancelParams) : WorkerM Unit := do
    updatePendingRequests (fun pendingRequests => pendingRequests.erase p.id)

  /--
  Received from the watchdog when a dependency of this file is detected as being stale.
  Issues a sticky diagnostic to the client that it should run "Restart File".
  -/
  def handleStaleDependency (_ : LeanStaleDependencyParams) : WorkerM Unit := do
    let ctx ← read
    let s ← get
    let text := s.doc.meta.text
    let importOutOfDataMessage := .text s!"Imports are out of date and should be rebuilt; \
      use the \"Restart File\" command in your editor."
    let diagnostic := {
      range      := ⟨⟨0, 0⟩, ⟨1, 0⟩⟩
      fullRange? := some ⟨⟨0, 0⟩, text.utf8PosToLspPos text.source.endPos⟩
      severity?  := DiagnosticSeverity.information
      message := importOutOfDataMessage
    }
    ctx.stickyDiagnosticsRef.modify fun stickyDiagnostics =>
      let stickyDiagnostics := stickyDiagnostics.filter
        (·.message.stripTags != importOutOfDataMessage.stripTags)
      stickyDiagnostics.push diagnostic
    publishDiagnostics ctx s.doc.toEditableDocumentCore

def handleRpcRelease (p : Lsp.RpcReleaseParams) : WorkerM Unit := do
  -- NOTE(WN): when the worker restarts e.g. due to changed imports, we may receive `rpc/release`
  -- for the previous RPC session. This is fine, just ignore.
  if let some seshRef := (← get).rpcSessions.find? p.sessionId then
    let monoMsNow ← IO.monoMsNow
    let discardRefs : StateM RpcObjectStore Unit := do
      for ref in p.refs do
        discard do rpcReleaseRef ref
    seshRef.modify fun st =>
      let st := st.keptAlive monoMsNow
      let ((), objects) := discardRefs st.objects
      { st with objects }

def handleRpcKeepAlive (p : Lsp.RpcKeepAliveParams) : WorkerM Unit := do
  match (← get).rpcSessions.find? p.sessionId with
  | none => return
  | some seshRef =>
    seshRef.modify (·.keptAlive (← IO.monoMsNow))

end NotificationHandling

/-! Requests here are handled synchronously rather than in the asynchronous `RequestM`. -/
section RequestHandling

def handleRpcConnect (_ : RpcConnectParams) : WorkerM RpcConnected := do
  let (newId, newSesh) ← RpcSession.new
  let newSeshRef ← IO.mkRef newSesh
  modify fun st => { st with rpcSessions := st.rpcSessions.insert newId newSeshRef }
  return { sessionId := newId }

end RequestHandling

section MessageHandling
  def parseParams (paramType : Type) [FromJson paramType] (params : Json) : WorkerM paramType :=
    match fromJson? params with
    | Except.ok parsed => pure parsed
    | Except.error inner => throwServerError s!"Got param with wrong structure: {params.compress}\n{inner}"

  def handleNotification (method : String) (params : Json) : WorkerM Unit := do
    let handle := fun paramType [FromJson paramType] (handler : paramType → WorkerM Unit) =>
      parseParams paramType params >>= handler
    match method with
    | "textDocument/didChange" => handle DidChangeTextDocumentParams handleDidChange
    | "$/cancelRequest"        => handle CancelParams handleCancelRequest
    | "$/lean/staleDependency" => handle Lsp.LeanStaleDependencyParams handleStaleDependency
    | "$/lean/rpc/release"     => handle RpcReleaseParams handleRpcRelease
    | "$/lean/rpc/keepAlive"   => handle RpcKeepAliveParams handleRpcKeepAlive
    | _                        => throwServerError s!"Got unsupported notification method: {method}"

  def queueRequest (id : RequestID) (requestTask : Task (Except IO.Error Unit))
      : WorkerM Unit := do
    updatePendingRequests (fun pendingRequests => pendingRequests.insert id requestTask)

  open Widget RequestM Language in
  def handleGetInteractiveDiagnosticsRequest (params : GetInteractiveDiagnosticsParams) :
      WorkerM (Array InteractiveDiagnostic) := do
    let ctx ← read
    let st ← get
    -- NOTE: always uses latest document (which is the only one we can retrieve diagnostics for);
    -- any race should be temporary as the client should re-request interactive diagnostics when
    -- they receive the non-interactive diagnostics for the new document
    let stickyDiags ← ctx.stickyDiagnosticsRef.get
    let diags ← st.doc.diagnosticsRef.get
    -- NOTE: does not wait for `lineRange?` to be fully elaborated, which would be problematic with
    -- fine-grained incremental reporting anyway; instead, the client is obligated to resend the
    -- request when the non-interactive diagnostics of this range have changed
    return (stickyDiags ++ diags).filter fun diag =>
      let r := diag.fullRange
      let diagStartLine := r.start.line
      let diagEndLine   :=
        if r.end.character == 0 then
          r.end.line
        else
          r.end.line + 1
      params.lineRange?.all fun ⟨s, e⟩ =>
        -- does [s,e) intersect [diagStartLine,diagEndLine)?
        s ≤ diagStartLine ∧ diagStartLine < e ∨
        diagStartLine ≤ s ∧ s < diagEndLine

  def handleImportCompletionRequest (id : RequestID) (params : CompletionParams)
      : WorkerM (Task (Except Error AvailableImportsCache)) := do
    let ctx ← read
    let st ← get
    let text := st.doc.meta.text

    match st.importCachingTask? with
    | none => IO.asTask (prio := Task.Priority.dedicated) do
      let availableImports ← ImportCompletion.collectAvailableImports
      let lastRequestTimestampMs ← IO.monoMsNow
      let completions := ImportCompletion.find text st.doc.initSnap.stx params availableImports
      ctx.chanOut.send <| .response id (toJson completions)
      pure { availableImports, lastRequestTimestampMs : AvailableImportsCache }

    | some task => IO.mapTask (t := task) fun result => do
      let mut ⟨availableImports, lastRequestTimestampMs⟩ ← IO.ofExcept result
      let timestampNowMs ← IO.monoMsNow
      if timestampNowMs - lastRequestTimestampMs >= 10000 then
        availableImports ← ImportCompletion.collectAvailableImports
      lastRequestTimestampMs := timestampNowMs
      let completions := ImportCompletion.find text st.doc.initSnap.stx params availableImports
      ctx.chanOut.send <| .response id (toJson completions)
      pure { availableImports, lastRequestTimestampMs : AvailableImportsCache }

  def handleRequest (id : RequestID) (method : String) (params : Json)
      : WorkerM Unit := do
    let ctx ← read
    let st ← get

    -- special cases
    try
      match method with
      -- needs access to `WorkerState.rpcSessions`
      | "$/lean/rpc/connect" =>
        let ps ← parseParams RpcConnectParams params
        let resp ← handleRpcConnect ps
        ctx.chanOut.send <| .response id (toJson resp)
        return
      | "$/lean/rpc/call" =>
        let params ← parseParams Lsp.RpcCallParams params
        -- needs access to `EditableDocumentCore.diagnosticsRef`
        if params.method == `Lean.Widget.getInteractiveDiagnostics then
          let some seshRef := st.rpcSessions.find? params.sessionId
            | ctx.chanOut.send <| .responseError id .rpcNeedsReconnect "Outdated RPC session" none
          let params ← IO.ofExcept (fromJson? params.params)
          let resp ← handleGetInteractiveDiagnosticsRequest params

          let resp ← seshRef.modifyGet fun st =>
            rpcEncode resp st.objects |>.map (·) ({st with objects := ·})
          ctx.chanOut.send <| .response id resp
          return
      | "textDocument/completion" =>
        let params ← parseParams CompletionParams params
        -- must not wait on import processing snapshot
        if ImportCompletion.isImportCompletionRequest st.doc.meta.text st.doc.initSnap.stx params
        then
          let importCachingTask ← handleImportCompletionRequest id params
          set { st with importCachingTask? := some importCachingTask }
          return
      | _ => pure ()
    catch e =>
      ctx.chanOut.send <| .responseError id .internalError (toString e) none
      return

    -- we assume that any other request requires at least the search path
    -- TODO: move into language-specific request handling
    let t ← IO.bindTask st.srcSearchPathTask fun srcSearchPath => do
      let rc : RequestContext :=
        { rpcSessions := st.rpcSessions
          srcSearchPath
          doc := st.doc
          hLog := ctx.hLog
          initParams := ctx.initParams }
      let t? ← EIO.toIO' <| handleLspRequest method params rc
      let t₁ ← match t? with
        | Except.error e =>
          IO.asTask do
            ctx.chanOut.send <| e.toLspResponseError id
        | Except.ok t => (IO.mapTask · t) fun
          | Except.ok resp =>
            ctx.chanOut.send <| .response id (toJson resp)
          | Except.error e =>
            ctx.chanOut.send <| e.toLspResponseError id
    queueRequest id t

  def handleResponse (_ : RequestID) (_ : Json) : WorkerM Unit :=
    return -- The only response that we currently expect here is always empty

end MessageHandling

section MainLoop
  variable (hIn : FS.Stream) in
  partial def mainLoop : WorkerM Unit := do
    let mut st ← get
    let msg ← hIn.readLspMessage
    let filterFinishedTasks (acc : PendingRequestMap) (id : RequestID) (task : Task (Except IO.Error Unit))
        : IO PendingRequestMap := do
      if (← hasFinished task) then
        -- Handler tasks are constructed so that the only possible errors here
        -- are failures of writing a response into the stream.
        if let Except.error e := task.get then
          throwServerError s!"Failed responding to request {id}: {e}"
        pure <| acc.erase id
      else pure acc
    let pendingRequests ← st.pendingRequests.foldM (fun acc id task => filterFinishedTasks acc id task) st.pendingRequests
    st := { st with pendingRequests }

    -- Opportunistically (i.e. when we wake up on messages) check if any RPC session has expired.
    for (id, seshRef) in st.rpcSessions do
      let sesh ← seshRef.get
      if (← sesh.hasExpired) then
        st := { st with rpcSessions := st.rpcSessions.erase id }

    set st
    match msg with
    | Message.request id method (some params) =>
      handleRequest id method (toJson params)
      mainLoop
    | Message.notification "exit" none =>
      return
    | Message.notification method (some params) =>
      handleNotification method (toJson params)
      mainLoop
    | Message.response id result =>
      handleResponse id result
      mainLoop
    | Message.responseError .. =>
      -- Ignore all errors as we currently only handle a single request with an optional response
      -- where failure is not an issue.
      mainLoop
    | _ => throwServerError "Got invalid JSON-RPC message"
end MainLoop

def runRefreshTask : WorkerM (Task (Except IO.Error Unit)) := do
  let ctx ← read
  IO.asTask (prio := Task.Priority.dedicated) do
    while ! (←IO.checkCanceled) do
      let pastProcessingStates ← ctx.chanIsProcessing.recvAllCurrent
      if pastProcessingStates.isEmpty then
        -- Processing progress has not changed since we last sent out a refresh request
        -- => do not send out another one for now so that we do not make the client spam
        --    semantic token requests while idle and already having received an up-to-date state
        IO.sleep 1000
        continue
      sendServerRequest ctx "workspace/semanticTokens/refresh" (none : Option Nat)
      IO.sleep 2000

def initAndRunWorker (i o e : FS.Stream) (opts : Options) : IO Unit := do
  let i ← maybeTee "fwIn.txt" false i
  let o ← maybeTee "fwOut.txt" true o
  let initParams ← i.readLspRequestAs "initialize" InitializeParams
  let ⟨_, param⟩ ← i.readLspNotificationAs "textDocument/didOpen" LeanDidOpenTextDocumentParams
  let doc := param.textDocument
  -- LSP always refers to characters by (line, column),
  -- so converting CRLF to LF preserves line and column numbers.
  let meta : DocumentMeta := ⟨doc.uri, doc.version, doc.text.crlfToLf.toFileMap, param.dependencyBuildMode?.getD .always⟩
  let e := e.withPrefix s!"[{param.textDocument.uri}] "
  let _ ← IO.setStderr e
  let (ctx, st) ← try
    initializeWorker meta o e initParams.param opts
  catch err =>
    writeErrorDiag meta err
    throw err
  StateRefT'.run' (s := st) <| ReaderT.run (r := ctx) do
    try
      let refreshTask ← runRefreshTask
      mainLoop i
      IO.cancel refreshTask
    catch err =>
      let st ← get
      writeErrorDiag st.doc.meta err
      throw err
where
  writeErrorDiag (meta : DocumentMeta) (err : Error) : IO Unit := do
    o.writeLspMessage <| mkPublishDiagnosticsNotification meta #[{
      range := ⟨⟨0, 0⟩, ⟨1, 0⟩⟩,
      fullRange? := some ⟨⟨0, 0⟩, meta.text.utf8PosToLspPos meta.text.source.endPos⟩
      severity? := DiagnosticSeverity.error
      message := err.toString }]

@[export lean_server_worker_main]
def workerMain (opts : Options) : IO UInt32 := do
  let i ← IO.getStdin
  let o ← IO.getStdout
  let e ← IO.getStderr
  try
    initAndRunWorker i o e opts
    IO.Process.exit 0 -- Terminate all tasks of this process
  catch err =>
    e.putStrLn err.toString
    IO.Process.exit 1 -- Terminate all tasks of this process

end Lean.Server.FileWorker
