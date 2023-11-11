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

import Lean.Util.Paths
import Lean.LoadDynlib
import Lean.Language.Basic

import Lean.Server.Utils
import Lean.Server.AsyncList
import Lean.Server.References

import Lean.Server.FileWorker.Utils
import Lean.Server.FileWorker.RequestHandling
import Lean.Server.FileWorker.WidgetRequests
import Lean.Server.Rpc.Basic
import Lean.Widget.InteractiveDiagnostic

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
  hIn              : FS.Stream
  hOut             : FS.Stream
  hLog             : FS.Stream
  initParams       : InitializeParams
  processor        : Parser.InputContext → BaseIO Lean.Language.Lean.InitialSnapshot
  clientHasWidgets : Bool

/-! # Asynchronous snapshot elaboration -/

section Elab
  -- Placed here instead of Lean.Server.Utils because of an import loop
  private def publishIleanInfo (method : String) (m : DocumentMeta) (hOut : FS.Stream)
      (trees : Array Elab.InfoTree) : IO Unit := do
    let references := findModuleRefs m.text trees (localVars := true)
    let param := { version := m.version, references : LeanIleanInfoParams }
    hOut.writeLspNotification { method, param }

  private def publishIleanInfoUpdate : DocumentMeta → FS.Stream → Array Elab.InfoTree → IO Unit :=
    publishIleanInfo "$/lean/ileanInfoUpdate"

  private def publishIleanInfoFinal : DocumentMeta → FS.Stream → Array Elab.InfoTree → IO Unit :=
    publishIleanInfo "$/lean/ileanInfoFinal"

  private structure ReportSnapshotsState where
    hasBlocked := false
    diagnostics : Array Lsp.Diagnostic := #[]
    infoTrees : Array Elab.InfoTree := #[]

  /--
    Reports status of a snapshot tree incrementally to the user: progress,
    diagnostics, .ilean reference information.

    Debouncing: we only report information
    * when first blocking, i.e. not before skipping over any unchanged snapshots
    * afterwards, each time new information is found in a snapshot
    * at the very end, if we never blocked (e.g. emptying a file should make
      sure to empty diagnostics as well eventually) -/
  private partial def reportSnapshots (ctx : WorkerContext) (m : DocumentMeta) (snaps : Language.SnapshotTree)
      (cancelTk : CancelToken) : IO Unit := do
    discard <| go snaps { : ReportSnapshotsState } fun st => do
      publishProgressDone m ctx.hOut
      unless st.hasBlocked do
        publishDiagnostics m st.diagnostics ctx.hOut
      -- This will overwrite existing ilean info for the file, in case something
      -- went wrong during the incremental updates.
      publishIleanInfoFinal m ctx.hOut st.infoTrees
      return .pure <| .ok ()
  where
    go node st cont := do
      if (← cancelTk.ref.get) then
        return .pure <| .ok ()
      let diagnostics := st.diagnostics ++ (← node.element.msgLog.toList.toArray.mapM (Widget.msgToInteractiveDiagnostic m.text · ctx.clientHasWidgets)).map (·.toDiagnostic)
      if st.hasBlocked && !node.element.msgLog.isEmpty then
        publishDiagnostics m diagnostics ctx.hOut
      let infoTrees := match node.element.infoTree? with
        | some itree => st.infoTrees.push itree
        | none       => st.infoTrees
      if st.hasBlocked && node.element.infoTree?.isSome then
        publishIleanInfoUpdate m ctx.hOut infoTrees
      goSeq { st with diagnostics, infoTrees } cont node.children.toList
    goSeq st cont
      | [] => cont st
      | t::ts => do
        let mut st := st
        unless (← IO.hasFinished t.task) do
          publishProgressAtPos m t.range.start ctx.hOut
          if !st.hasBlocked then
            publishDiagnostics m st.diagnostics ctx.hOut
            st := { st with hasBlocked := true }
        IO.bindTask t.task fun node =>
          go node st (goSeq · cont ts)
end Elab

-- Pending requests are tracked so they can be canceled
abbrev PendingRequestMap := RBMap RequestID (Task (Except IO.Error Unit)) compare

structure WorkerState where
  doc             : EditableDocument
  -- The initial header syntax tree. Changing the header requires restarting the worker process.
  initHeaderStx   : Syntax
  pendingRequests : PendingRequestMap
  /-- A map of RPC session IDs. We allow asynchronous elab tasks and request handlers
  to modify sessions. A single `Ref` ensures atomic transactions. -/
  rpcSessions     : RBMap UInt64 (IO.Ref RpcSession) compare
  reportCancelTk  : CancelToken

abbrev WorkerM := ReaderT WorkerContext <| StateRefT WorkerState IO

/- Worker initialization sequence. -/
section Initialization
  /-- Use `lake print-paths` to compile dependencies on the fly and add them to `LEAN_PATH`.
  Compilation progress is reported to `hOut` via LSP notifications. Return the search path for
  source files. -/
  partial def lakeSetupSearchPath (lakePath : System.FilePath) (m : DocumentMeta) (imports : Array Import) (hOut : FS.Stream) : IO SearchPath := do
    let mut args := #["print-paths"] ++ imports.map (toString ·.module)
    if m.dependencyBuildMode matches .never then
      args := args.push "--no-build"
    let cmdStr := " ".intercalate (toString lakePath :: args.toList)
    let lakeProc ← Process.spawn {
      stdin  := Process.Stdio.null
      stdout := Process.Stdio.piped
      stderr := Process.Stdio.piped
      cmd    := lakePath.toString
      args
    }
    -- progress notification: report latest stderr line
    let rec processStderr (acc : String) : IO String := do
      let line ← lakeProc.stderr.getLine
      if line == "" then
        return acc
      else
        publishDiagnostics m #[{ range := ⟨⟨0, 0⟩, ⟨0, 0⟩⟩, severity? := DiagnosticSeverity.information, message := line }] hOut
        processStderr (acc ++ line)
    let stderr ← IO.asTask (processStderr "") Task.Priority.dedicated
    let stdout := String.trim (← lakeProc.stdout.readToEnd)
    let stderr ← IO.ofExcept stderr.get
    match (← lakeProc.wait) with
    | 0 =>
      let Except.ok (paths : LeanPaths) ← pure (Json.parse stdout >>= fromJson?)
        | throwServerError s!"invalid output from `{cmdStr}`:\n{stdout}\nstderr:\n{stderr}"
      initSearchPath (← getBuildDir) paths.oleanPath
      paths.loadDynlibPaths.forM loadDynlib
      paths.srcPath.mapM realPathNormalized
    | 2 => pure []  -- no lakefile.lean
    -- error from `--no-build`
    | 3 => throwServerError s!"Imports are out of date and must be rebuilt; use the \"Restart File\" command in your editor.\n\n{stdout}"
    | _ => throwServerError s!"`{cmdStr}` failed:\n{stdout}\nstderr:\n{stderr}"

  def initializeWorker (meta : DocumentMeta) (i o e : FS.Stream) (initParams : InitializeParams) (opts : Options)
      : IO (WorkerContext × WorkerState) := do
    let clientHasWidgets := initParams.initializationOptions?.bind (·.hasWidgets?) |>.getD false
    let mut mainModuleName := Name.anonymous
    try
      if let some path := System.Uri.fileUriToPath? meta.uri then
        mainModuleName ← moduleNameOfFileName path none
    catch _ => pure ()
    let processor ← Language.Lean.mkIncrementalProcessor { opts, mainModuleName }
    let initSnap ← processor meta.mkInputContext
    let ctx :=
      { hIn  := i
        hOut := o
        hLog := e
        initParams
        processor
        clientHasWidgets
      }
    let doc : EditableDocument := { meta, initSnap }
    let reportCancelTk ← CancelToken.new
    reportSnapshots ctx doc.meta (Language.ToSnapshotTree.toSnapshotTree doc.initSnap) reportCancelTk
    return (ctx,
    { doc, reportCancelTk
      initHeaderStx   := initSnap.stx
      pendingRequests := RBMap.empty
      rpcSessions     := RBMap.empty
    })
end Initialization

section Updates
  def updatePendingRequests (map : PendingRequestMap → PendingRequestMap) : WorkerM Unit := do
    modify fun st => { st with pendingRequests := map st.pendingRequests }

  /-- Given the new document, updates editable doc state. -/
  def updateDocument (newMeta : DocumentMeta) : WorkerM Unit := do
    let ctx ← read
    (← get).reportCancelTk.set
    let initSnap ← ctx.processor newMeta.mkInputContext
    let reportCancelTk ← CancelToken.new
    reportSnapshots ctx newMeta (Language.ToSnapshotTree.toSnapshotTree initSnap) reportCancelTk
    modify fun st => { st with doc := { meta := newMeta, initSnap }, reportCancelTk }
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

  def handleRequest (id : RequestID) (method : String) (params : Json)
      : WorkerM Unit := do
    let ctx ← read
    let st ← get

    if method == "$/lean/rpc/connect" then
      try
        let ps ← parseParams RpcConnectParams params
        let resp ← handleRpcConnect ps
        ctx.hOut.writeLspResponse ⟨id, resp⟩
      catch e =>
        ctx.hOut.writeLspResponseError
          { id
            code := ErrorCode.internalError
            message := toString e }
      return

    -- we assume that every request requires at least the header snapshot or the search path
    let t ← IO.bindTask (.pure "") fun _ => do
     let srcSearchPath := ∅
     let rc : RequestContext :=
       { rpcSessions := st.rpcSessions
         srcSearchPath
         doc := st.doc
         hLog := ctx.hLog
         hOut := ctx.hOut
         initParams := ctx.initParams }
     let t? ← EIO.toIO' <| handleLspRequest method params rc
     let t₁ ← match t? with
       | Except.error e =>
         IO.asTask do
           ctx.hOut.writeLspResponseError <| e.toLspResponseError id
       | Except.ok t => (IO.mapTask · t) fun
         | Except.ok resp =>
           ctx.hOut.writeLspResponse ⟨id, resp⟩
         | Except.error e =>
           ctx.hOut.writeLspResponseError <| e.toLspResponseError id
    queueRequest id t
end MessageHandling

section MainLoop
  partial def mainLoop : WorkerM Unit := do
    let ctx ← read
    let mut st ← get
    let msg ← ctx.hIn.readLspMessage
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
    let (ctx, st) ← initializeWorker meta i o e initParams.param opts
    let _ ← StateRefT'.run (s := st) <| ReaderT.run (r := ctx) mainLoop
    return (0 : UInt32)
  catch e =>
    IO.eprintln e
    publishDiagnostics meta #[{ range := ⟨⟨0, 0⟩, ⟨0, 0⟩⟩, severity? := DiagnosticSeverity.error, message := e.toString }] o
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
