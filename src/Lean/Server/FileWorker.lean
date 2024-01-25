/-
Copyright (c) 2020 Marc Huisinga. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Marc Huisinga, Wojciech Nawrocki
-/
import Init.System.IO
import Lean.Data.RBMap
import Lean.Environment

import Lean.Data.Lsp
import Lean.Data.Json.FromToJson

import Lean.Util.FileSetupInfo
import Lean.LoadDynlib
import Lean.Language.Basic

import Lean.Server.Utils
import Lean.Server.AsyncList
import Lean.Server.References

import Lean.Server.FileWorker.Utils
import Lean.Server.FileWorker.RequestHandling
import Lean.Server.FileWorker.WidgetRequests
import Lean.Server.FileWorker.SetupFile
import Lean.Server.Rpc.Basic
import Lean.Widget.InteractiveDiagnostic
import Lean.Server.ImportCompletion

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

structure WorkerContext where
  /-- Synchronized output channel for LSP messages. Notifications for outdated versions are
    discarded on read. -/
  chanOut          : IO.Channel JsonRpc.Message
  /--
  Latest document version received by the client, used for filtering out notifications from
  previous versions.
  -/
  maxDocVersionRef : IO.Ref Nat
  hLog             : FS.Stream
  initParams       : InitializeParams
  processor        : Parser.InputContext → BaseIO Lean.Language.Lean.InitialSnapshot
  clientHasWidgets : Bool
  opts             : Options

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

  /-- State of `reportSnapshots`. -/
  private structure ReportSnapshotsState where
    /-- Whether we have waited for a snapshot to finish at least once (see debouncing below). -/
    hasBlocked := false
    /-- All info trees encountered so far. -/
    allInfoTrees : Array Elab.InfoTree := #[]
    /-- New info trees encountered since we last sent a .ilean update notification. -/
    newInfoTrees : Array Elab.InfoTree := #[]
    /-- Whether we should finish with a fatal progress notification. -/
    isFatal := false

  register_builtin_option server.reportDelayMs : Nat := {
    defValue := 200
    group := "server"
    descr := "(server) time in milliseconds to wait before reporting progress and diagnostics on \
      document edit in order to reduce flickering"
  }

  /--
    Reports status of a snapshot tree incrementally to the user: progress,
    diagnostics, .ilean reference information.

    Debouncing: we only report information
    * after first waiting for `reportDelayMs`, to give trivial tasks a chance to finish
    * when first blocking, i.e. not before skipping over any unchanged snapshots and such trival
      tasks
    * afterwards, each time new information is found in a snapshot
    * at the very end, if we never blocked (e.g. emptying a file should make
      sure to empty diagnostics as well eventually) -/
  private partial def reportSnapshots (ctx : WorkerContext) (doc : EditableDocumentCore)
      (prevDiagnosticsCache : DiagnosticsCache) : BaseIO (Task Unit) := do
    let t ← BaseIO.asTask do
      IO.sleep (server.reportDelayMs.get ctx.opts).toUInt32
    BaseIO.bindTask t fun _ =>
      start
  where
    start := go (Language.toSnapshotTree doc.initSnap) { : ReportSnapshotsState } fun st => do
      -- callback at the end of reporting
      if st.isFatal then
        ctx.chanOut.send <| mkFileProgressAtPosNotification doc.meta 0 .fatalError
      else
        ctx.chanOut.send <| mkFileProgressDoneNotification doc.meta
      unless st.hasBlocked do
        publishDiagnostics
      -- This will overwrite existing ilean info for the file, in case something
      -- went wrong during the incremental updates.
      ctx.chanOut.send (← mkIleanInfoFinalNotification doc.meta st.allInfoTrees)
      return .pure ()
    publishDiagnostics := do
      ctx.chanOut.send <| mkPublishDiagnosticsNotification doc.meta <|
        (← doc.diagnosticsRef.get).map (·.toDiagnostic)
    go node st cont := do
      if (← IO.checkCanceled) then
        return .pure ()
      let idiags ←
        if let some cached := node.element.diagnostics.id?.bind prevDiagnosticsCache.find? then
          pure cached
        else
          let idiags ← node.element.diagnostics.msgLog.toList.toArray.mapM
            (Widget.msgToInteractiveDiagnostic doc.meta.text · ctx.clientHasWidgets)
          if let some id := node.element.diagnostics.id? then
            doc.diagnosticsCacheRef.modify (·.insert id idiags)
          pure idiags
      if !node.element.diagnostics.msgLog.isEmpty then
        doc.diagnosticsRef.modify (· ++ idiags)
        if st.hasBlocked then
          publishDiagnostics
      -- we assume that only the last node in the tree sets `isFatal`
      let mut st := { st with isFatal := node.element.isFatal }

      if let some itree := node.element.infoTree? then
        let mut newInfoTrees := st.newInfoTrees.push itree
        if st.hasBlocked then
          ctx.chanOut.send (← mkIleanInfoUpdateNotification doc.meta newInfoTrees)
          newInfoTrees := #[]
        st := { st with newInfoTrees, allInfoTrees := st.allInfoTrees.push itree }
      goSeq st cont node.children.toList
    goSeq st cont
      | [] => cont st
      | t::ts => do
        let mut st := st
        unless (← IO.hasFinished t.task) do
          ctx.chanOut.send <| mkFileProgressAtPosNotification doc.meta t.range.start
          if !st.hasBlocked then
            publishDiagnostics
            st := { st with hasBlocked := true }
        BaseIO.bindTask t.task fun node =>
          go node st (goSeq · cont ts)
end Elab

-- Pending requests are tracked so they can be canceled
abbrev PendingRequestMap := RBMap RequestID (Task (Except IO.Error Unit)) compare

structure AvailableImportsCache where
  availableImports       : ImportCompletion.AvailableImports
  lastRequestTimestampMs : Nat

structure WorkerState where
  doc                : EditableDocument
  importCachingTask? : Option (Task (Except Error AvailableImportsCache))
  pendingRequests    : PendingRequestMap
  /-- A map of RPC session IDs. We allow asynchronous elab tasks and request handlers
  to modify sessions. A single `Ref` ensures atomic transactions. -/
  rpcSessions        : RBMap UInt64 (IO.Ref RpcSession) compare

abbrev WorkerM := ReaderT WorkerContext <| StateRefT WorkerState IO

/- Worker initialization sequence. -/
section Initialization
  def initializeWorker (meta : DocumentMeta) (o e : FS.Stream) (initParams : InitializeParams) (opts : Options)
      : IO (WorkerContext × WorkerState) := do
    let clientHasWidgets := initParams.initializationOptions?.bind (·.hasWidgets?) |>.getD false
    let mut mainModuleName := Name.anonymous
    try
      if let some path := System.Uri.fileUriToPath? meta.uri then
        mainModuleName ← moduleNameOfFileName path none
    catch _ => pure ()
    let maxDocVersionRef ← IO.mkRef 0
    let nextDiagsIdRef ← IO.mkRef 0
    let chanOut ← mkLspOutputChannel maxDocVersionRef
    let processor ← Language.Lean.mkIncrementalProcessor {
      opts, mainModuleName, nextDiagsIdRef
      fileSetupHandler? := some fun imports => do
        let result ← setupFile meta imports fun stderrLine => do
          let progressDiagnostic := {
            range      := ⟨⟨0, 0⟩, ⟨0, 0⟩⟩
            fullRange? := some ⟨⟨0, 0⟩, meta.text.utf8PosToLspPos meta.text.source.endPos⟩
            severity?  := DiagnosticSeverity.information
            message    := stderrLine
          }
          chanOut.send <| mkPublishDiagnosticsNotification meta #[progressDiagnostic]
        -- clear progress notifications in the end
        chanOut.send <| mkPublishDiagnosticsNotification meta #[]
        return result
    }
    let initSnap ← processor meta.mkInputContext
    let ctx := {
      chanOut
      hLog := e
      initParams
      processor
      clientHasWidgets
      maxDocVersionRef
      opts
    }
    let doc : EditableDocumentCore := {
      meta, initSnap
      diagnosticsRef := (← IO.mkRef ∅)
      diagnosticsCacheRef := (← IO.mkRef ∅)
    }
    let reporter ← reportSnapshots ctx doc ∅
    return (ctx, {
      doc := { doc with reporter }
      pendingRequests    := RBMap.empty
      rpcSessions        := RBMap.empty
      importCachingTask? := none
    })
  where
    /-- Creates an LSP message output channel along with a reader that sends out read messages on
        the output FS stream after discarding outdated notifications. This is the only component of
        the worker with access to the output stream, so we can synchronize messages from parallel
        elaboration tasks here. -/
    mkLspOutputChannel maxDocVersion : IO (IO.Channel JsonRpc.Message) := do
      let chanOut ← IO.Channel.new
      -- most recent document version seen in notifications
      let _ ← chanOut.forAsync (prio := .dedicated) fun msg => do
        -- discard outdated notifications; note that in contrast to responses, notifications can
        -- always be silently discarded
        let version? : Option Nat := do
          let doc ← match msg with
            | .notification "textDocument/publishDiagnostics" (some <| .obj params) => some params
            | .notification "$/lean/fileProgress" (some <| .obj params) =>
              params.find compare "textDocument" |>.bind (·.getObj?.toOption)
            | _ => none
          doc.find compare "version" |>.bind (·.getNat?.toOption)
        if let some version := version? then
          if version < (← maxDocVersion.get) then
            return
          -- note that because of `server.reportDelayMs`, we cannot simply set `maxDocVersion` here
          -- as that would allow outdated messages to be reported until the delay is over
        o.writeLspMessage msg |>.catchExceptions (fun _ => pure ())
      return chanOut
end Initialization

section Updates
  def updatePendingRequests (map : PendingRequestMap → PendingRequestMap) : WorkerM Unit := do
    modify fun st => { st with pendingRequests := map st.pendingRequests }

  /-- Given the new document, updates editable doc state. -/
  def updateDocument (oldDoc : EditableDocument) (meta : DocumentMeta) : WorkerM Unit := do
    let ctx ← read
    let initSnap ← ctx.processor meta.mkInputContext
    let doc : EditableDocumentCore := {
      meta, initSnap
      diagnosticsRef := (← IO.mkRef ∅)
      diagnosticsCacheRef := (← IO.mkRef ∅)
    }
    let reporter ← reportSnapshots ctx doc (← oldDoc.diagnosticsCacheRef.get)
    modify fun st => { st with doc := { doc with reporter } }
    -- we assume versions are monotonous
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
      updateDocument oldDoc ⟨docId.uri, newVersion, newDocText, oldDoc.meta.dependencyBuildMode⟩

  def handleCancelRequest (p : CancelParams) : WorkerM Unit := do
    updatePendingRequests (fun pendingRequests => pendingRequests.erase p.id)

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
    | "$/lean/rpc/release"     => handle RpcReleaseParams handleRpcRelease
    | "$/lean/rpc/keepAlive"   => handle RpcKeepAliveParams handleRpcKeepAlive
    | _                        => throwServerError s!"Got unsupported notification method: {method}"

  def queueRequest (id : RequestID) (requestTask : Task (Except IO.Error Unit))
      : WorkerM Unit := do
    updatePendingRequests (fun pendingRequests => pendingRequests.insert id requestTask)

  open Widget RequestM Language in
  def handleGetInteractiveDiagnosticsRequest (params : GetInteractiveDiagnosticsParams) :
      WorkerM (Array InteractiveDiagnostic) := do
    let st ← get
    let diags ← st.doc.diagnosticsRef.get
    return diags.filter fun diag =>
      params.lineRange?.all fun ⟨s, e⟩ =>
        -- does [s,e) intersect [diag.fullRange.start.line,diag.fullRange.end.line)?
        s ≤ diag.fullRange.start.line ∧ diag.fullRange.start.line < e ∨
        diag.fullRange.start.line ≤ s ∧ s < diag.fullRange.end.line

  def handleImportCompletionRequest (id : RequestID) (params : CompletionParams)
      : WorkerM (Task (Except Error AvailableImportsCache)) := do
    let ctx ← read
    let st ← get
    let text := st.doc.meta.text

    match st.importCachingTask? with
    | none => IO.asTask do
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
      -- needs access to `rpcSessions`
      | "$/lean/rpc/connect" =>
        let ps ← parseParams RpcConnectParams params
        let resp ← handleRpcConnect ps
        ctx.chanOut.send <| .response id (toJson resp)
        return
      | "$/lean/rpc/call" =>
        let params ← parseParams Lsp.RpcCallParams params
        -- needs access to `diagnosticsRef`
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

    -- we assume that any other request requires at least the the search path
    -- TODO: move into language-specific request handling
    let srcSearchPathTask :=
      st.doc.initSnap.processedSuccessfully.map (·.map (·.srcSearchPath) |>.getD ∅)
    let t ← IO.bindTask srcSearchPathTask.task fun srcSearchPath => do
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
end MessageHandling

section MainLoop
  variable (hIn : FS.Stream) in
  partial def mainLoop : WorkerM Unit := do
    let mut st ← get
    let msg ← hIn.readLspMessage
    let filterFinishedTasks (acc : PendingRequestMap) (id : RequestID) (task : Task (Except IO.Error Unit))
        : IO PendingRequestMap := do
      if (← hasFinished task) then
        /- Handler tasks are constructed so that the only possible errors here
        are failures of writing a response into the stream. -/
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
      return ()
    | Message.notification method (some params) =>
      handleNotification method (toJson params)
      mainLoop
    | _ => throwServerError "Got invalid JSON-RPC message"
end MainLoop

def initAndRunWorker (i o e : FS.Stream) (opts : Options) : IO UInt32 := do
  let i ← maybeTee "fwIn.txt" false i
  let o ← maybeTee "fwOut.txt" true o
  let initParams ← i.readLspRequestAs "initialize" InitializeParams
  let ⟨_, param⟩ ← i.readLspNotificationAs "textDocument/didOpen" LeanDidOpenTextDocumentParams
  let doc := param.textDocument
  /- NOTE(WN): `toFileMap` marks line beginnings as immediately following
    "\n", which should be enough to handle both LF and CRLF correctly.
    This is because LSP always refers to characters by (line, column),
    so if we get the line number correct it shouldn't matter that there
    is a CR there. -/
  let meta : DocumentMeta := ⟨doc.uri, doc.version, doc.text.toFileMap, param.dependencyBuildMode?.getD .always⟩
  let e := e.withPrefix s!"[{param.textDocument.uri}] "
  let _ ← IO.setStderr e
  try
    let (ctx, st) ← initializeWorker meta o e initParams.param opts
    let _ ← StateRefT'.run (s := st) <| ReaderT.run (r := ctx) (mainLoop i)
    return (0 : UInt32)
  catch err =>
    IO.eprintln err
    e.writeLspMessage <| mkPublishDiagnosticsNotification meta #[{
      range := ⟨⟨0, 0⟩, ⟨0, 0⟩⟩
      severity? := DiagnosticSeverity.error
      message := err.toString }]
    return (1 : UInt32)

@[export lean_server_worker_main]
def workerMain (opts : Options) : IO UInt32 := do
  let i ← IO.getStdin
  let o ← IO.getStdout
  let e ← IO.getStderr
  try
    let exitCode ← initAndRunWorker i o e opts
    -- HACK: all `Task`s are currently "foreground", i.e. we join on them on main thread exit, but we definitely don't
    -- want to do that in the case of the worker processes, which can produce non-terminating tasks evaluating user code
    o.flush
    e.flush
    IO.Process.exit exitCode.toUInt8
  catch err =>
    e.putStrLn s!"worker initialization error: {err}"
    return (1 : UInt32)

end Lean.Server.FileWorker
