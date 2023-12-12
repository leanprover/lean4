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

import Lean.Server.Utils
import Lean.Server.Snapshots
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
  hIn              : FS.Stream
  hOut             : FS.Stream
  hLog             : FS.Stream
  headerTask       : Task (Except Error (Snapshot × SearchPath))
  initParams       : InitializeParams
  clientHasWidgets : Bool

/-! # Asynchronous snapshot elaboration -/

section Elab
  structure AsyncElabState where
    snaps : Array Snapshot

  abbrev AsyncElabM := StateT AsyncElabState <| EIO ElabTaskError

  -- Placed here instead of Lean.Server.Utils because of an import loop
  private def publishIleanInfo (method : String) (m : DocumentMeta) (hOut : FS.Stream)
      (snaps : Array Snapshot) : IO Unit := do
    let trees := snaps.map fun snap => snap.infoTree
    let references := findModuleRefs m.text trees (localVars := true)
    let param := { version := m.version, references : LeanIleanInfoParams }
    hOut.writeLspNotification { method, param }

  private def publishIleanInfoUpdate : DocumentMeta → FS.Stream → Array Snapshot → IO Unit :=
    publishIleanInfo "$/lean/ileanInfoUpdate"

  private def publishIleanInfoFinal : DocumentMeta → FS.Stream → Array Snapshot → IO Unit :=
    publishIleanInfo "$/lean/ileanInfoFinal"

  /-- Elaborates the next command after `parentSnap` and emits diagnostics into `hOut`. -/
  private def nextCmdSnap (ctx : WorkerContext) (m : DocumentMeta) (cancelTk : CancelToken)
      : AsyncElabM (Option Snapshot) := do
    cancelTk.check
    let s ← get
    let .some lastSnap := s.snaps.back? | panic! "empty snapshots"
    if lastSnap.isAtEnd then
      publishDiagnostics m lastSnap.diagnostics.toArray ctx.hOut
      publishProgressDone m ctx.hOut
      -- This will overwrite existing ilean info for the file, in case something
      -- went wrong during the incremental updates.
      publishIleanInfoFinal m ctx.hOut s.snaps
      return none
    publishProgressAtPos m lastSnap.endPos ctx.hOut
    let snap ← compileNextCmd m.mkInputContext lastSnap ctx.clientHasWidgets
    set { s with snaps := s.snaps.push snap }
    -- TODO(MH): check for interrupt with increased precision
    cancelTk.check
    /- NOTE(MH): This relies on the client discarding old diagnostics upon receiving new ones
      while preferring newer versions over old ones. The former is necessary because we do
      not explicitly clear older diagnostics, while the latter is necessary because we do
      not guarantee that diagnostics are emitted in order. Specifically, it may happen that
      we interrupted this elaboration task right at this point and a newer elaboration task
      emits diagnostics, after which we emit old diagnostics because we did not yet detect
      the interrupt. Explicitly clearing diagnostics is difficult for a similar reason,
      because we cannot guarantee that no further diagnostics are emitted after clearing
      them. -/
    -- NOTE(WN): this is *not* redundant even if there are no new diagnostics in this snapshot
    -- because empty diagnostics clear existing error/information squiggles. Therefore we always
    -- want to publish in case there was previously a message at this position.
    publishDiagnostics m snap.diagnostics.toArray ctx.hOut
    publishIleanInfoUpdate m ctx.hOut #[snap]
    return some snap

  /-- Elaborates all commands after the last snap (at least the header snap is assumed to exist), emitting the diagnostics into `hOut`. -/
  def unfoldCmdSnaps (m : DocumentMeta) (snaps : Array Snapshot) (cancelTk : CancelToken) (startAfterMs : UInt32)
      : ReaderT WorkerContext IO (AsyncList ElabTaskError Snapshot) := do
    let ctx ← read
    let some headerSnap := snaps[0]? | panic! "empty snapshots"
    if headerSnap.msgLog.hasErrors then
      -- Treats header processing errors as fatal so users aren't swamped with
      -- followup errors
      publishProgressAtPos m headerSnap.beginPos ctx.hOut (kind := LeanFileProgressKind.fatalError)
      publishIleanInfoFinal m ctx.hOut #[headerSnap]
      return AsyncList.ofList [headerSnap]
    else
      -- This will overwrite existing ilean info for the file since this has a
      -- higher version number.
      publishIleanInfoUpdate m ctx.hOut snaps
      return AsyncList.ofList snaps.toList ++ AsyncList.delayed (← EIO.asTask (ε := ElabTaskError) (prio := .dedicated) do
        IO.sleep startAfterMs
        AsyncList.unfoldAsync (nextCmdSnap ctx m cancelTk) { snaps })
end Elab

-- Pending requests are tracked so they can be cancelled
abbrev PendingRequestMap := RBMap RequestID (Task (Except IO.Error Unit)) compare

structure AvailableImportsCache where
  availableImports       : ImportCompletion.AvailableImports
  lastRequestTimestampMs : Nat

structure WorkerState where
  doc                : EditableDocument
  -- The initial header syntax tree that the file worker was started with.
  initHeaderStx      : Syntax
  -- The current header syntax tree. Changing the header from `initHeaderStx` initiates a restart
  -- that only completes after a while, so `currHeaderStx` tracks the modified syntax until then.
  currHeaderStx      : Syntax
  importCachingTask? : Option (Task (Except Error AvailableImportsCache))
  pendingRequests    : PendingRequestMap
  /-- A map of RPC session IDs. We allow asynchronous elab tasks and request handlers
  to modify sessions. A single `Ref` ensures atomic transactions. -/
  rpcSessions        : RBMap UInt64 (IO.Ref RpcSession) compare

abbrev WorkerM := ReaderT WorkerContext <| StateRefT WorkerState IO

/- Worker initialization sequence. -/
section Initialization
  def buildHeaderEnv (m : DocumentMeta) (headerStx : Syntax) (fileSetupResult : FileSetupResult) : IO (Environment × MessageLog) := do
    let (headerEnv, msgLog) ←
      match fileSetupResult.kind with
      | .success | .noLakefile =>
        -- allows `headerEnv` to be leaked, which would live until the end of the process anyway
        Elab.processHeader (leakEnv := true) headerStx fileSetupResult.fileOptions MessageLog.empty m.mkInputContext
      | .importsOutOfDate =>
        mkErrorEnvironment "Imports are out of date and must be rebuilt; use the \"Restart File\" command in your editor."
      | .error msg =>
        mkErrorEnvironment msg

    let mut headerEnv := headerEnv
    try
      if let some path := System.Uri.fileUriToPath? m.uri then
        headerEnv := headerEnv.setMainModule (← moduleNameOfFileName path none)
    catch _ =>
      pure ()

    return (headerEnv, msgLog)

  where
    mkErrorEnvironment (errorMsg : String) : IO (Environment × MessageLog) := do
      let msgs := MessageLog.empty.add { fileName := "<ignored>", pos := ⟨0, 0⟩, data := errorMsg }
      return (← mkEmptyEnvironment, msgs)

  def buildCommandState
      (m : DocumentMeta)
      (headerStx : Syntax)
      (headerEnv : Environment)
      (headerMsgLog : MessageLog)
      (opts : Options)
      : Elab.Command.State :=
    let headerContextInfo : Elab.ContextInfo := {
      env     := headerEnv
      fileMap := m.text
      ngen    := { namePrefix := `_worker }
    }
    let headerInfo := Elab.Info.ofCommandInfo { elaborator := `header, stx := headerStx }
    let headerInfoNodes := headerStx[1].getArgs.toList.map fun importStx =>
      Elab.InfoTree.node (Elab.Info.ofCommandInfo {
        elaborator := `import
        stx := importStx
      }) #[].toPArray'
    let headerInfoTree := Elab.InfoTree.node headerInfo headerInfoNodes.toPArray'
    let headerInfoState := {
      enabled := true
      trees := #[Elab.InfoTree.context headerContextInfo headerInfoTree].toPArray'
    }
    { Elab.Command.mkState headerEnv headerMsgLog opts with infoState := headerInfoState }

  def compileHeader (m : DocumentMeta) (hOut : FS.Stream) (globalOptions : Options) (hasWidgets : Bool)
      : IO (Syntax × Task (Except Error (Snapshot × SearchPath))) := do
    -- parsing should not take long, do synchronously
    let (headerStx, headerParserState, parseMsgLog) ← Parser.parseHeader m.mkInputContext
    (headerStx, ·) <$> EIO.asTask do
      let imports := Lean.Elab.headerToImports headerStx
      let fileSetupResult ← setupFile m imports fun stderrLine =>
        let progressDiagnostic := {
          range     := ⟨⟨0, 0⟩, ⟨0, 0⟩⟩
          severity? := DiagnosticSeverity.information
          message   := stderrLine
        }
        publishDiagnostics m #[progressDiagnostic] hOut
      let fileSetupResult := fileSetupResult.addGlobalOptions globalOptions
      let (headerEnv, envMsgLog) ← buildHeaderEnv m headerStx fileSetupResult
      let headerMsgLog := parseMsgLog.append envMsgLog
      let cmdState := buildCommandState m headerStx headerEnv headerMsgLog fileSetupResult.fileOptions
      let headerSnap := {
        beginPos         := 0
        stx              := headerStx
        mpState          := headerParserState
        cmdState         := cmdState
        interactiveDiags := ← cmdState.messages.msgs.mapM (Widget.msgToInteractiveDiagnostic m.text · hasWidgets)
        tacticCache      := (← IO.mkRef {})
      }
      publishDiagnostics m headerSnap.diagnostics.toArray hOut
      return (headerSnap, fileSetupResult.srcSearchPath)

  def initializeWorker (meta : DocumentMeta) (i o e : FS.Stream) (initParams : InitializeParams) (opts : Options)
      : IO (WorkerContext × WorkerState) := do
    let clientHasWidgets := initParams.initializationOptions?.bind (·.hasWidgets?) |>.getD false
    let (headerStx, headerTask) ← compileHeader meta o opts (hasWidgets := clientHasWidgets)
    let cancelTk ← CancelToken.new
    let ctx := {
      hIn  := i
      hOut := o
      hLog := e
      headerTask
      initParams
      clientHasWidgets
    }
    let cmdSnaps ← EIO.mapTask (t := headerTask) (match · with
      | Except.ok (s, _) => unfoldCmdSnaps meta #[s] cancelTk ctx (startAfterMs := 0)
      | Except.error e   => throw (e : ElabTaskError))
    let doc : EditableDocument := { meta, cmdSnaps := AsyncList.delayed cmdSnaps, cancelTk }
    return (ctx, {
      doc                := doc
      initHeaderStx      := headerStx
      currHeaderStx      := headerStx
      importCachingTask? := none
      pendingRequests    := RBMap.empty
      rpcSessions        := RBMap.empty
    })
end Initialization

section Updates
  def updatePendingRequests (map : PendingRequestMap → PendingRequestMap) : WorkerM Unit := do
    modify fun st => { st with pendingRequests := map st.pendingRequests }

  def determineValidSnapshots (oldDoc : EditableDocument) (newMeta : DocumentMeta) (newHeaderSnap : Snapshot) : IO (List Snapshot) := do
    let changePos := oldDoc.meta.text.source.firstDiffPos newMeta.text.source
    -- Ignores exceptions, we are only interested in the successful snapshots
    let (cmdSnaps, _) ← oldDoc.cmdSnaps.getFinishedPrefix
    oldDoc.cmdSnaps.cancel
    -- NOTE(WN): we invalidate eagerly as `endPos` consumes input greedily. To re-elaborate only
    -- when really necessary, we could do a whitespace-aware `Syntax` comparison instead.
    let mut validSnaps ← pure (cmdSnaps.takeWhile (fun s => s.endPos < changePos))
    if h : validSnaps.length ≤ 1 then
      validSnaps := [newHeaderSnap]
    else
      /- When at least one valid non-header snap exists, it may happen that a change does not fall
          within the syntactic range of that last snap but still modifies it by appending tokens.
          We check for this here. We do not currently handle crazy grammars in which an appended
          token can merge two or more previous commands into one. To do so would require reparsing
          the entire file. -/
      have : validSnaps.length ≥ 2 := Nat.gt_of_not_le h
      let mut lastSnap := validSnaps.getLast (by subst ·; simp at h)
      let preLastSnap :=
        have : 0 < validSnaps.length := Nat.lt_of_lt_of_le (by decide) this
        have : validSnaps.length - 2 < validSnaps.length := Nat.sub_lt this (by decide)
        validSnaps[validSnaps.length - 2]
      let newLastStx ← parseNextCmd newMeta.mkInputContext preLastSnap
      if newLastStx != lastSnap.stx then
        validSnaps := validSnaps.dropLast
    return validSnaps

  def startNewSnapshotTasks (newMeta : DocumentMeta) : WorkerM (AsyncList ElabTaskError Snapshot × CancelToken) := do
    let ctx ← read
    let oldDoc := (← get).doc
    oldDoc.cancelTk.set
    let initHeaderStx := (← get).initHeaderStx
    let (newHeaderStx, newMpState, _) ← Parser.parseHeader newMeta.mkInputContext
    let cancelTk ← CancelToken.new

    if initHeaderStx != newHeaderStx then
      set { ← get with currHeaderStx := newHeaderStx }
      let terminationTask ← EIO.asTask (ε := ElabTaskError) (prio := .dedicated) do
        IO.sleep ctx.initParams.editDelay.toUInt32
        cancelTk.check
        IO.Process.exit 2
      return (AsyncList.delayed terminationTask, cancelTk)

    let headSnapTask := oldDoc.cmdSnaps.waitHead?
    let newSnapTasks ← EIO.mapTask (ε := ElabTaskError) (t := headSnapTask) (prio := .dedicated) fun headSnap?? => do
      -- There is always at least one snapshot absent exceptions
      let some headSnap ← MonadExcept.ofExcept headSnap?? | panic! "empty snapshots"
      let newHeaderSnap := { headSnap with stx := newHeaderStx, mpState := newMpState }
      let validSnaps ← determineValidSnapshots oldDoc newMeta newHeaderSnap
      -- wait for a bit, giving the initial `cancelTk.check` in `nextCmdSnap` time to trigger
      -- before kicking off any expensive elaboration (TODO: make expensive elaboration cancelable)
      unfoldCmdSnaps newMeta validSnaps.toArray cancelTk ctx
        (startAfterMs := ctx.initParams.editDelay.toUInt32)

    return (AsyncList.delayed newSnapTasks, cancelTk)

  /-- Given the new document, updates editable doc state. -/
  def updateDocument (newMeta : DocumentMeta) : WorkerM Unit := do
    let (newSnaps, cancelTk) ← startNewSnapshotTasks newMeta
    modify fun st => { st with doc := { meta := newMeta, cmdSnaps := newSnaps, cancelTk } }

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

  def handleImportCompletionRequest (id : RequestID) (params : CompletionParams)
      : WorkerM (Task (Except Error AvailableImportsCache)) := do
    let ctx ← read
    let st ← get
    let text := st.doc.meta.text

    match st.importCachingTask? with
    | none => IO.asTask do
      let availableImports ← ImportCompletion.collectAvailableImports
      let lastRequestTimestampMs ← IO.monoMsNow
      let completions := ImportCompletion.find text st.currHeaderStx params availableImports
      ctx.hOut.writeLspResponse ⟨id, completions⟩
      pure { availableImports, lastRequestTimestampMs : AvailableImportsCache }

    | some task => IO.mapTask (t := task) fun result => do
      let mut ⟨availableImports, lastRequestTimestampMs⟩ ← IO.ofExcept result
      let timestampNowMs ← IO.monoMsNow
      if timestampNowMs - lastRequestTimestampMs >= 10000 then
        availableImports ← ImportCompletion.collectAvailableImports
      lastRequestTimestampMs := timestampNowMs
      let completions := ImportCompletion.find text st.currHeaderStx params availableImports
      ctx.hOut.writeLspResponse ⟨id, completions⟩
      pure { availableImports, lastRequestTimestampMs : AvailableImportsCache }

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

    if method == "textDocument/completion" then
      let params ← parseParams CompletionParams params
      if ImportCompletion.isImportCompletionRequest st.doc.meta.text st.currHeaderStx params then
        let importCachingTask ← handleImportCompletionRequest id params
        set <| { st with importCachingTask? := some importCachingTask }
        return

    -- we assume that every request requires at least the header snapshot or the search path
    let t ← IO.bindTask ctx.headerTask fun x => do
      let (_, srcSearchPath) ← IO.ofExcept x
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
      let doc := st.doc
      doc.cancelTk.set
      doc.cmdSnaps.cancel
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
