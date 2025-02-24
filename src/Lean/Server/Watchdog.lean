/-
Copyright (c) 2020 Marc Huisinga. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Marc Huisinga, Wojciech Nawrocki
-/
prelude
import Init.System.IO
import Std.Sync.Mutex
import Init.Data.ByteArray
import Lean.Data.RBMap

import Lean.Util.Paths

import Lean.Data.FuzzyMatching
import Lean.Data.Json
import Lean.Data.Lsp
import Lean.Server.Utils
import Lean.Server.Requests
import Lean.Server.References
import Lean.Server.ServerTask

/-!
For general server architecture, see `README.md`. This module implements the watchdog process.

## Watchdog state

Most LSP clients only send us file diffs, so to facilitate sending entire file contents to freshly
restarted workers, the watchdog needs to maintain the current state of each file. It can also use
this state to detect changes to the header and thus restart the corresponding worker, freeing its
imports.

TODO(WN):
We may eventually want to keep track of approximately (since this isn't knowable exactly) where in
the file a worker crashed. Then on restart, we tell said worker to only parse up to that point and
query the user about how to proceed (continue OR allow the user to fix the bug and then continue OR
..). Without this, if the crash is deterministic, users may be confused about why the server
seemingly stopped working for a single file.

## Watchdog <-> worker communication

The watchdog process and its file worker processes communicate via LSP. If the necessity arises, we
might add non-standard commands similarly based on JSON-RPC. Most requests and notifications are
forwarded to the corresponding file worker process, with the exception of these notifications:

- textDocument/didOpen: Launch the file worker, create the associated watchdog state and launch a
                        task to asynchronously receive LSP packets from the worker (e.g. request
                        responses).
- textDocument/didChange: Update the local file state so that it can be resent to restarted workers.
                          Then forward the `didChange` notification.
- textDocument/didClose: Signal a shutdown to the file worker and remove the associated watchdog
  state.

Moreover, we don't implement the full protocol at this level:

- Upon starting, the `initialize` request is forwarded to the worker, but it must not respond with
  its server capabilities. Consequently, the watchdog will not send an `initialized` notification to
  the worker.
- After `initialize`, the watchdog sends the corresponding `didOpen` notification with the full
  current state of the file. No additional `didOpen` notifications will be forwarded to the worker
  process.
- `$/cancelRequest` notifications are forwarded to all file workers.
- File workers are always terminated with an `exit` notification, without previously receiving a
  `shutdown` request. Similarly, they never receive a `didClose` notification.

## Watchdog <-> client communication

The watchdog itself should implement the LSP standard as closely as possible. However we reserve the
right to add non-standard extensions in case they're needed, for example to communicate tactic
state.
-/

namespace Lean.Server.Watchdog

open IO
open Lsp
open JsonRpc
open System.Uri

section Utils
  def workerCfg : Process.StdioConfig := {
    stdin  := Process.Stdio.piped
    stdout := Process.Stdio.piped
    -- We pass workers' stderr through to the editor.
    stderr := Process.Stdio.inherit
  }

  /-- Events that worker-specific tasks signal to the main thread. -/
  inductive WorkerEvent where
    | terminated
    | importsChanged
    | crashed (e : IO.Error)
    | ioError (e : IO.Error)

  inductive CrashOrigin
    | fileWorkerToClientForwarding
    | clientToFileWorkerForwarding

  inductive WorkerState where
    /-- The watchdog can detect a crashed file worker in two places: When trying to send a message
      to the file worker and when reading a request reply.
      In the latter case, the forwarding task terminates and delegates a `crashed` event to the
      main task. Then, in both cases, the file worker has its state set to `crashed` and requests
      that are in-flight are errored. Upon receiving the next packet for that file worker, the file
      worker is restarted and the packet is forwarded to it. If the crash was detected while writing
      a packet, we queue that packet until the next packet for the file worker arrives. -/
    | crashed (queuedMsgs : Array JsonRpc.Message) (origin : CrashOrigin)
    | running

  abbrev PendingRequestMap := RBMap RequestID JsonRpc.Message compare
end Utils

section FileWorker
  structure FileWorker where
    doc                : DocumentMeta
    proc               : Process.Child workerCfg
    exitCode           : Std.Mutex (Option UInt32)
    commTask           : ServerTask WorkerEvent
    state              : WorkerState
    -- This should not be mutated outside of namespace FileWorker,
    -- as it is used as shared mutable state
    /-- The pending requests map contains all requests that have been received from the LSP client,
    but were not answered yet.
    We need them for forwarding cancellation requests to the correct worker as well as cleanly
    aborting requests on worker crashes. -/
    pendingRequestsRef : IO.Ref PendingRequestMap

  namespace FileWorker

  def stdin (fw : FileWorker) : FS.Stream :=
    FS.Stream.ofHandle fw.proc.stdin

  def stdout (fw : FileWorker) : FS.Stream :=
    FS.Stream.ofHandle fw.proc.stdout

  def erasePendingRequest (fw : FileWorker) (id : RequestID) : IO Unit :=
    fw.pendingRequestsRef.modify fun pendingRequests => pendingRequests.erase id

  def errorPendingRequests (fw : FileWorker) (hError : FS.Stream) (code : ErrorCode) (msg : String)
      : IO Unit := do
    let pendingRequests ← fw.pendingRequestsRef.modifyGet
      fun pendingRequests => (pendingRequests, RBMap.empty)
    for ⟨id, _⟩ in pendingRequests do
      hError.writeLspResponseError { id := id, code := code, message := msg }

  def queuedMsgs (fw : FileWorker) : Array JsonRpc.Message :=
    match fw.state with
    | .running => #[]
    | .crashed queuedMsgs _ => queuedMsgs

  def waitForProc (fw : FileWorker) : IO UInt32 :=
    fw.exitCode.atomically do
      match ← get with
      | none =>
        let exitCode ← fw.proc.wait
        set <| some exitCode
        return exitCode
      | some exitCode =>
        return exitCode

  def killProcAndWait (fw : FileWorker) : IO UInt32 :=
    fw.exitCode.atomically do
      match ← get with
      | none =>
        fw.proc.kill
        let exitCode ← fw.proc.wait
        set <| some exitCode
        return exitCode
      | some exitCode =>
        -- Process is already dead
        return exitCode


  end FileWorker
end FileWorker

section ServerM
  abbrev FileWorkerMap := RBMap DocumentUri FileWorker compare
  abbrev ImportMap := RBMap DocumentUri (RBTree DocumentUri compare) compare

  /-- Global import data for all open files managed by this watchdog. -/
  structure ImportData where
    /-- For every open file, the files that it imports. -/
    imports    : ImportMap
    /-- For every open file, the files that it is imported by. -/
    importedBy : ImportMap

  /-- Updates `d` with the new set of `imports` for the file `uri`. -/
  def ImportData.update (d : ImportData) (uri : DocumentUri) (imports : RBTree DocumentUri compare)
      : ImportData := Id.run do
    let oldImports     := d.imports.findD uri ∅
    let removedImports := oldImports.diff imports
    let addedImports   := imports.diff oldImports
    let mut importedBy := d.importedBy

    for removedImport in removedImports do
      let importedByRemovedImport' := importedBy.find! removedImport |>.erase uri
      if importedByRemovedImport'.isEmpty then
        importedBy := importedBy.erase removedImport
      else
        importedBy := importedBy.insert removedImport importedByRemovedImport'

    for addedImport in addedImports do
      importedBy :=
        importedBy.findD addedImport ∅
          |>.insert uri
          |> importedBy.insert addedImport

    let imports :=
      if imports.isEmpty then
        d.imports.erase uri
      else
        d.imports.insert uri imports

    return { imports, importedBy }

  /--
  Sets the imports of `uri` in `d` to the empty set.
  -/
  def ImportData.eraseImportsOf (d : ImportData) (uri : DocumentUri) : ImportData :=
    d.update uri ∅

  structure RequestIDTranslation where
    sourceUri : DocumentUri
    localID   : RequestID

  abbrev PendingServerRequestMap := RBMap RequestID RequestIDTranslation compare

  structure ServerRequestData where
    pendingServerRequests : PendingServerRequestMap
    freshServerRequestID  : Nat

  def ServerRequestData.trackOutboundRequest
      (data      : ServerRequestData)
      (sourceUri : DocumentUri)
      (localID   : RequestID)
      : RequestID × ServerRequestData :=
    let globalID := data.freshServerRequestID
    let data := {
      pendingServerRequests := data.pendingServerRequests.insert globalID ⟨sourceUri, localID⟩
      freshServerRequestID  := globalID + 1
    }
    (globalID, data)

  def ServerRequestData.translateInboundResponse
      (data     : ServerRequestData)
      (globalID : RequestID)
      : Option RequestIDTranslation × ServerRequestData :=
    let translation? := data.pendingServerRequests.find? globalID
    let data := { data with pendingServerRequests := data.pendingServerRequests.erase globalID }
    (translation?, data)

  structure ServerContext where
    hIn                 : FS.Stream
    hOut                : FS.Stream
    hLog                : FS.Stream
    /-- Command line arguments. -/
    args                : List String
    fileWorkersRef      : IO.Ref FileWorkerMap
    /-- We store these to pass them to workers. -/
    initParams          : InitializeParams
    workerPath          : System.FilePath
    srcSearchPath       : System.SearchPath
    references          : IO.Ref References
    serverRequestData   : IO.Ref ServerRequestData
    importData          : IO.Ref ImportData

  abbrev ServerM := ReaderT ServerContext IO

  def updateFileWorkers (val : FileWorker) : ServerM Unit := do
    (←read).fileWorkersRef.modify (fun fileWorkers => fileWorkers.insert val.doc.uri val)

  def findFileWorker? (uri : DocumentUri) : ServerM (Option FileWorker) :=
    return (← (←read).fileWorkersRef.get).find? uri

  def eraseFileWorker (uri : DocumentUri) : ServerM Unit := do
    let s ← read
    s.importData.modify (·.eraseImportsOf uri)
    s.fileWorkersRef.modify (fun fileWorkers => fileWorkers.erase uri)
    let some module ← s.srcSearchPath.searchModuleNameOfUri uri
      | return
    s.references.modify fun refs => refs.removeWorkerRefs module

  def log (msg : String) : ServerM Unit := do
    let st ← read
    st.hLog.putStrLn msg
    st.hLog.flush

  def handleIleanInfoUpdate (fw : FileWorker) (params : LeanIleanInfoParams) : ServerM Unit := do
    let s ← read
    let some module ← s.srcSearchPath.searchModuleNameOfUri fw.doc.uri
      | return
    s.references.modify fun refs =>
      refs.updateWorkerRefs module params.version params.references

  def handleIleanInfoFinal (fw : FileWorker) (params : LeanIleanInfoParams) : ServerM Unit := do
    let s ← read
    let some module ← s.srcSearchPath.searchModuleNameOfUri fw.doc.uri
      | return
    s.references.modify fun refs =>
      refs.finalizeWorkerRefs module params.version params.references

  /--
  Updates the global import data with the import closure provided by the file worker after it
  successfully processed its header.
  -/
  def handleImportClosure (fw : FileWorker) (params : LeanImportClosureParams) : ServerM Unit := do
    let s ← read
    s.importData.modify fun importData =>
      importData.update fw.doc.uri (.ofList params.importClosure.toList)

  /-- Creates a Task which forwards a worker's messages into the output stream until an event
  which must be handled in the main watchdog thread (e.g. an I/O error) happens. -/
  private partial def forwardMessages (fw : FileWorker) : ServerM (ServerTask WorkerEvent) := do
    let task ← ServerTask.IO.asTask (loop $ ←read)
    return task.mapCheap fun
      | Except.ok ev   => ev
      | Except.error e => WorkerEvent.ioError e
  where
    loop : ServerM WorkerEvent := do
      let o := (←read).hOut
      let msg ←
        try
          fw.stdout.readLspMessage
        catch err =>
          let exitCode ← fw.waitForProc
          -- Remove surviving descendant processes, if any, such as from nested builds.
          -- On Windows, we instead rely on elan doing this.
          try fw.proc.kill catch _ => pure ()
          -- TODO: Wait for process group to finish
          match exitCode with
          | 0 =>
            -- Worker was terminated
            fw.errorPendingRequests o ErrorCode.contentModified
              (s!"The file worker for {fw.doc.uri} has been terminated. "
              ++ "Either the header has changed, or the file was closed, "
              ++ " or the server is shutting down.")
            -- one last message to clear the diagnostics for this file so that stale errors
            -- do not remain in the editor forever.
            o.writeLspMessage <| mkPublishDiagnosticsNotification fw.doc #[]
            return WorkerEvent.terminated
          | 2 =>
            return .importsChanged
          | _ =>
            -- Worker crashed
            let (errorCode, errorCausePointer) :=
              if exitCode = 1 then
                (ErrorCode.workerExited, "see stderr for exception")
              else
                (ErrorCode.workerCrashed, "likely due to a stack overflow or a bug")
            fw.errorPendingRequests o errorCode
              s!"Server process for {fw.doc.uri} crashed, {errorCausePointer}."
            o.writeLspMessage <| mkFileProgressAtPosNotification fw.doc 0 (kind := LeanFileProgressKind.fatalError)
            return WorkerEvent.crashed err

      -- Re. `o.writeLspMessage msg`:
      -- Writes to Lean I/O channels are atomic, so these won't trample on each other.
      match msg with
      | Message.response id _ => do
        fw.erasePendingRequest id
        o.writeLspMessage msg
      | Message.responseError id _ _ _ => do
        fw.erasePendingRequest id
        o.writeLspMessage msg
      | Message.request id method params? =>
        let globalID ← (←read).serverRequestData.modifyGet
          (·.trackOutboundRequest fw.doc.uri id)
        o.writeLspMessage (Message.request globalID method params?)
      | Message.notification "$/lean/ileanInfoUpdate" params =>
        if let some params := params then
          if let Except.ok params := FromJson.fromJson? <| ToJson.toJson params then
            handleIleanInfoUpdate fw params
      | Message.notification "$/lean/ileanInfoFinal" params =>
        if let some params := params then
          if let Except.ok params := FromJson.fromJson? <| ToJson.toJson params then
            handleIleanInfoFinal fw params
      | Message.notification "$/lean/importClosure" params =>
        if let some params := params then
          if let Except.ok params := FromJson.fromJson? <| ToJson.toJson params then
            handleImportClosure fw params
      | _ =>
        o.writeLspMessage msg

      loop

  def startFileWorker (m : DocumentMeta) : ServerM Unit := do
    (← read).hOut.writeLspMessage <| mkFileProgressAtPosNotification m 0
    let st ← read
    let workerProc ← Process.spawn {
      toStdioConfig := workerCfg
      cmd           := st.workerPath.toString
      args          := #["--worker"] ++ st.args.toArray ++ #[m.uri]
      -- open session for `kill` above
      setsid        := true
    }
    let exitCode ← Std.Mutex.new none
    let pendingRequestsRef ← IO.mkRef (RBMap.empty : PendingRequestMap)
    let initialDependencyBuildMode := m.dependencyBuildMode
    let updatedDependencyBuildMode :=
      if initialDependencyBuildMode matches .once then
        -- By sending the first `didOpen` notification, we build the dependencies once
        -- => no future builds
        .never
      else
        initialDependencyBuildMode
    -- The task will never access itself, so this is fine
    let fw : FileWorker := {
      doc                := { m with dependencyBuildMode := updatedDependencyBuildMode}
      proc               := workerProc
      exitCode
      commTask           := Task.pure WorkerEvent.terminated
      state              := WorkerState.running
      pendingRequestsRef := pendingRequestsRef
    }
    let commTask ← forwardMessages fw
    let fw : FileWorker := { fw with commTask := commTask }
    fw.stdin.writeLspRequest ⟨0, "initialize", st.initParams⟩
    fw.stdin.writeLspNotification {
      method := "textDocument/didOpen"
      param  := {
        textDocument := {
          uri        := m.uri
          languageId := "lean"
          version    := m.version
          text       := m.text.source
        }
        dependencyBuildMode? := initialDependencyBuildMode
        : LeanDidOpenTextDocumentParams
      }
    }
    updateFileWorkers fw

  def terminateFileWorker (uri : DocumentUri) : ServerM Unit := do
    let some fw ← findFileWorker? uri
      | return
    try
      fw.stdin.writeLspMessage (Message.notification "exit" none)
    catch _ =>
      /- The file worker must have crashed just when we were about to terminate it!
        That's fine - just forget about it then.
        (on didClose we won't need the crashed file worker anymore,
        when the header changed we'll start a new one right after
        anyways and when we're shutting down the server
        it's over either way.) -/
      return
    eraseFileWorker uri

  def handleCrash (uri : DocumentUri) (queuedMsgs : Array JsonRpc.Message) (origin: CrashOrigin) : ServerM Unit := do
    let some fw ← findFileWorker? uri
      | return
    updateFileWorkers { fw with state := WorkerState.crashed queuedMsgs origin }

  def tryDischargeQueuedMessages (uri : DocumentUri) (queuedMsgs : Array JsonRpc.Message) : ServerM Unit := do
      let some fw ← findFileWorker? uri
        | throwServerError "Cannot find file worker for '{uri}'."
      let mut crashedMsgs := #[]
      -- Try to discharge all queued msgs, tracking the ones that we can't discharge
      for msg in queuedMsgs do
        try
          fw.stdin.writeLspMessage msg
        catch _ =>
          crashedMsgs := crashedMsgs.push msg
      if ¬ crashedMsgs.isEmpty then
        handleCrash uri crashedMsgs .clientToFileWorkerForwarding

  /-- Tries to write a message, sets the state of the FileWorker to `crashed` if it does not succeed
      and restarts the file worker if the `crashed` flag was already set. Just logs an error if
      there is no FileWorker at this `uri`.
      Messages that couldn't be sent can be queued up via the queueFailedMessage flag and
      will be discharged after the FileWorker is restarted. -/
  def tryWriteMessage
      (uri : DocumentUri)
      (msg : JsonRpc.Message)
      (queueFailedMessage := true)
      (restartCrashedWorker := false)
      : ServerM Unit := do
    let some fw ← findFileWorker? uri
      | return
    match fw.state with
    | WorkerState.crashed queuedMsgs _ =>
      let mut queuedMsgs := queuedMsgs
      if queueFailedMessage then
        queuedMsgs := queuedMsgs.push msg
      if !restartCrashedWorker then
        return
      -- restart the crashed FileWorker
      eraseFileWorker uri
      startFileWorker fw.doc
      tryDischargeQueuedMessages uri queuedMsgs
    | WorkerState.running =>
      let initialQueuedMsgs :=
        if queueFailedMessage then
          #[msg]
        else
          #[]
      try
        fw.stdin.writeLspMessage msg
      catch _ =>
        handleCrash uri initialQueuedMsgs .clientToFileWorkerForwarding

  /--
  Sends a notification to the file worker identified by `uri` that its dependency `staleDependency`
  is out-of-date.
  -/
  def notifyAboutStaleDependency (uri : DocumentUri) (staleDependency : DocumentUri)
      : ServerM Unit :=
    let notification := Notification.mk "$/lean/staleDependency" {
      staleDependency := staleDependency
      : LeanStaleDependencyParams
    }
    tryWriteMessage uri notification (queueFailedMessage := false)
end ServerM

section RequestHandling

open FuzzyMatching

def findDefinitions (p : TextDocumentPositionParams) : ServerM <| Array Location := do
  let srcSearchPath := (← read).srcSearchPath
  let some module ← srcSearchPath.searchModuleNameOfUri p.textDocument.uri
    | return #[]
  let references ← (← read).references.get
  let mut definitions := #[]
  for ident in references.findAt module p.position (includeStop := true) do
    if let some ⟨definitionLocation, _⟩ ← references.definitionOf? ident srcSearchPath then
      definitions := definitions.push definitionLocation
  return definitions

def handleReference (p : ReferenceParams) : ServerM (Array Location) := do
  let srcSearchPath := (← read).srcSearchPath
  let some module ← srcSearchPath.searchModuleNameOfUri p.textDocument.uri
    | return #[]
  let references ← (← read).references.get
  let mut result := #[]
  for ident in references.findAt module p.position (includeStop := true) do
    let identRefs ← references.referringTo srcSearchPath ident
      p.context.includeDeclaration
    result := result.append <| identRefs.map (·.location)
  return result

/--
Used in `CallHierarchyItem.data?` to retain all the data needed to quickly re-identify the
call hierarchy item.
-/
structure CallHierarchyItemData where
  module : Name
  name   : Name
  deriving FromJson, ToJson

/--
Extracts the CallHierarchyItemData from `item.data?` and returns `none` if this is not possible.
-/
def CallHierarchyItemData.fromItem? (item : CallHierarchyItem) : Option CallHierarchyItemData := do
  fromJson? (← item.data?) |>.toOption

private def callHierarchyItemOf?
    (refs          : References)
    (ident         : RefIdent)
    (srcSearchPath : SearchPath)
    : IO (Option CallHierarchyItem) := do
  let some ⟨definitionLocation, parentDecl?⟩ ← refs.definitionOf? ident srcSearchPath
    | return none

  match ident with
  | .const definitionModule definitionNameString =>
    let definitionName := definitionNameString.toName
    -- If we have a constant with a proper name, use it.
    -- If `callHierarchyItemOf?` is used either on the name of a definition itself or e.g. an
    -- `inductive` constructor, this is the right thing to do and using the parent decl is
    -- the wrong thing to do.

    -- Remove private header from name
    let label := Lean.privateToUserName? definitionName |>.getD definitionName
    return some {
      name           := label.toString
      kind           := SymbolKind.constant
      uri            := definitionLocation.uri
      range          := definitionLocation.range,
      selectionRange := definitionLocation.range
      data?          := toJson {
        module := definitionModule.toName
        name   := definitionName
        : CallHierarchyItemData
      }
    }
  | _ =>
    let some ⟨parentDeclNameString, parentDeclRange, parentDeclSelectionRange⟩ := parentDecl?
      | return none
    let parentDeclName := parentDeclNameString.toName

    let some definitionModule ← srcSearchPath.searchModuleNameOfUri definitionLocation.uri
      | return none

    -- Remove private header from name
    let label := Lean.privateToUserName? parentDeclName |>.getD parentDeclName

    return some {
      name           := label.toString
      kind           := SymbolKind.constant
      uri            := definitionLocation.uri
      range          := parentDeclRange,
      selectionRange := parentDeclSelectionRange
      data?          := toJson {
        -- Assumption: The parent declaration of a reference lives in the same module
        -- as the reference.
        module := definitionModule
        name   := parentDeclName
        : CallHierarchyItemData
      }
    }

def handlePrepareCallHierarchy (p : CallHierarchyPrepareParams)
    : ServerM (Array CallHierarchyItem) := do
  let srcSearchPath := (← read).srcSearchPath
  let some module ← srcSearchPath.searchModuleNameOfUri p.textDocument.uri
    | return #[]

  let references ← (← read).references.get
  let idents := references.findAt module p.position (includeStop := true)

  let items ← idents.filterMapM fun ident =>
    callHierarchyItemOf? references ident srcSearchPath
  return items.qsort (·.name < ·.name)

def handleCallHierarchyIncomingCalls (p : CallHierarchyIncomingCallsParams)
    : ServerM (Array CallHierarchyIncomingCall) := do
  let some itemData := CallHierarchyItemData.fromItem? p.item
    | return #[]

  let srcSearchPath := (← read).srcSearchPath

  let references ← (← read).references.get
  let identRefs ← references.referringTo srcSearchPath (.const itemData.module.toString itemData.name.toString) false

  let incomingCalls ← identRefs.filterMapM fun ⟨location, parentDecl?⟩ => do

    let some ⟨parentDeclNameString, parentDeclRange, parentDeclSelectionRange⟩ := parentDecl?
      | return none

    let parentDeclName := parentDeclNameString.toName

    let some refModule ← srcSearchPath.searchModuleNameOfUri location.uri
      | return none

    -- Remove private header from name
    let label := Lean.privateToUserName? parentDeclName |>.getD parentDeclName

    return some {
      «from» := {
        name           := label.toString
        kind           := SymbolKind.constant
        uri            := location.uri
        range          := parentDeclRange
        selectionRange := parentDeclSelectionRange
        data?          := toJson {
          module := refModule
          name   := parentDeclName
          : CallHierarchyItemData
        }
      }
      fromRanges := #[location.range]
    }

  return collapseSameIncomingCalls incomingCalls |>.qsort (·.«from».name < ·.«from».name)

where

  collapseSameIncomingCalls (incomingCalls : Array CallHierarchyIncomingCall)
      : Array CallHierarchyIncomingCall :=
    let grouped := incomingCalls.groupByKey (·.«from»)
    let collapsed := grouped.toArray.map fun ⟨_, group⟩ => {
      «from» := group[0]!.«from»
      fromRanges := group.flatMap (·.fromRanges)
    }
    collapsed

def handleCallHierarchyOutgoingCalls (p : CallHierarchyOutgoingCallsParams)
    : ServerM (Array CallHierarchyOutgoingCall) := do
  let some itemData := CallHierarchyItemData.fromItem? p.item
    | return #[]

  let srcSearchPath := (← read).srcSearchPath

  let some module ← srcSearchPath.searchModuleNameOfUri p.item.uri
    | return #[]

  let references ← (← read).references.get

  let some refs := references.allRefs[module]?
    | return #[]

  let items ← refs.toArray.filterMapM fun ⟨ident, info⟩ => do
    let outgoingUsages := info.usages.filter fun usage => Id.run do
      let some parentDecl := usage.parentDecl?
        | return false
      return itemData.name == parentDecl.name.toName

    let outgoingUsages := outgoingUsages.map (·.range)
    if outgoingUsages.isEmpty then
      return none

    let some item ← callHierarchyItemOf? references ident srcSearchPath
      | return none

    -- filter local defs from outgoing calls
    if item.name == p.item.name then
      return none

    return some ⟨item, outgoingUsages⟩

  return collapseSameOutgoingCalls items |>.qsort (·.to.name < ·.to.name)

where

  collapseSameOutgoingCalls (outgoingCalls : Array CallHierarchyOutgoingCall)
      : Array CallHierarchyOutgoingCall :=
    let grouped := outgoingCalls.groupByKey (·.to)
    let collapsed := grouped.toArray.map fun ⟨_, group⟩ => {
      to := group[0]!.to
      fromRanges := group.flatMap (·.fromRanges)
    }
    collapsed

def handleWorkspaceSymbol (p : WorkspaceSymbolParams) : ServerM (Array SymbolInformation) := do
  if p.query.isEmpty then
    return #[]
  let references ← (← read).references.get
  let srcSearchPath := (← read).srcSearchPath
  let symbols ← references.definitionsMatching srcSearchPath (maxAmount? := none)
    fun name =>
      let name := privateToUserName? name |>.getD name
      if let some score := fuzzyMatchScoreWithThreshold? p.query name.toString then
        some (name.toString, score)
      else
        none
  return symbols
    |>.qsort (fun ((_, s1), _) ((_, s2), _) => s1 > s2)
    |>.extract 0 100 -- max amount
    |>.map fun ((name, _), location) =>
      { name, kind := SymbolKind.constant, location }

def handlePrepareRename (p : PrepareRenameParams) : ServerM (Option Range) := do
  -- This just checks that the cursor is over a renameable identifier
  let srcSearchPath := (← read).srcSearchPath
  let some module ← srcSearchPath.searchModuleNameOfUri p.textDocument.uri
    | return none
  let references ← (← read).references.get
  return references.findRange? module p.position (includeStop := true)

def handleRename (p : RenameParams) : ServerM Lsp.WorkspaceEdit := do
  if (String.toName p.newName).isAnonymous then
    throwServerError s!"Can't rename: `{p.newName}` is not an identifier"
  let mut refs : Std.HashMap DocumentUri (RBMap Lsp.Position Lsp.Position compare) := ∅
  for { uri, range } in (← handleReference { p with context.includeDeclaration := true }) do
    refs := refs.insert uri <| (refs.getD uri ∅).insert range.start range.end
  -- We have to filter the list of changes to put the ranges in order and
  -- remove any duplicates or overlapping ranges, or else the rename will not apply
  let changes := refs.fold (init := ∅) fun changes uri map => Id.run do
    let mut last := ⟨0, 0⟩
    let mut arr := #[]
    for (start, stop) in map do
      if last ≤ start then
        arr := arr.push { range := ⟨start, stop⟩, newText := p.newName }
        last := stop
    return changes.insert uri arr
  return { changes? := some changes }

end RequestHandling

section NotificationHandling
  def handleDidOpen (p : LeanDidOpenTextDocumentParams) : ServerM Unit :=
    let doc := p.textDocument
    /- Note (kmill): LSP always refers to characters by (line, column),
      so converting CRLF to LF preserves line and column numbers. -/
    startFileWorker ⟨doc.uri, doc.version, doc.text.crlfToLf.toFileMap, p.dependencyBuildMode?.getD .always⟩

  def handleDidChange (p : DidChangeTextDocumentParams) : ServerM Unit := do
    let doc := p.textDocument
    let changes := p.contentChanges
    let some fw ← findFileWorker? p.textDocument.uri
      -- Global search and replace in VS Code will send `didChange` to files that were never opened.
      | return
    let oldDoc := fw.doc
    let newVersion := doc.version?.getD 0
    if changes.isEmpty then
      return
    let newDocText := foldDocumentChanges changes oldDoc.text
    let newDoc : DocumentMeta := ⟨doc.uri, newVersion, newDocText, oldDoc.dependencyBuildMode⟩
    updateFileWorkers { fw with doc := newDoc }
    let notification := Notification.mk "textDocument/didChange" p
    -- Don't queue failed `didChange` notifications because we already accumulate them in the
    -- document and hand the updated document to the file worker when restarting it.
    tryWriteMessage doc.uri notification (restartCrashedWorker := true) (queueFailedMessage := false)

  /--
  When a file is saved, notifies all file workers for files that depend on this file that this
  specific import is now stale so that the file worker can issue a diagnostic asking users to
  restart the file.
  -/
  def handleDidSave (p : DidSaveTextDocumentParams) : ServerM Unit := do
    let s ← read
    let fileWorkers ← s.fileWorkersRef.get
    let importData  ← s.importData.get
    let dependents := importData.importedBy.findD p.textDocument.uri ∅

    for ⟨uri, _⟩ in fileWorkers do
      if ! dependents.contains uri then
        continue
      notifyAboutStaleDependency uri p.textDocument.uri

  def handleDidClose (p : DidCloseTextDocumentParams) : ServerM Unit :=
    terminateFileWorker p.textDocument.uri

  def handleDidChangeWatchedFiles (p : DidChangeWatchedFilesParams) : ServerM Unit := do
    let changes := p.changes.filterMap fun c => do return (c, ← fileUriToPath? c.uri)
    let leanChanges := changes.filter fun (_, path) => path.extension == "lean"
    let ileanChanges := changes.filter fun (_, path) => path.extension == "ilean"
    if ! leanChanges.isEmpty then
      let importData ← (← read).importData.get
      for (c, _) in leanChanges do
        let dependents := importData.importedBy.findD c.uri ∅
        for dependent in dependents do
          notifyAboutStaleDependency dependent c.uri
    if ! ileanChanges.isEmpty then
      let references := (← read).references
      let oleanSearchPath ← Lean.searchPathRef.get
      for (c, path) in ileanChanges do
        if let FileChangeType.Deleted := c.type then
          references.modify (fun r => r.removeIlean path)
          continue
        let isIleanInSearchPath := (← searchModuleNameOfFileName path oleanSearchPath).isSome
        if ! isIleanInSearchPath then
          continue
        try
          let ilean ← Ilean.load path
          if let FileChangeType.Changed := c.type then
            references.modify (fun r => r.removeIlean path |>.addIlean path ilean)
          else
            references.modify (fun r => r.addIlean path ilean)
        catch
          -- ilean vanished, ignore error
          | .noFileOrDirectory .. => references.modify (·.removeIlean path)
          | e => throw e

  def handleCancelRequest (p : CancelParams) : ServerM Unit := do
    let fileWorkers ← (←read).fileWorkersRef.get
    for ⟨uri, fw⟩ in fileWorkers do
      -- Cancelled requests still require a response, so they can't be removed
      -- from the pending requests map.
      if (← fw.pendingRequestsRef.get).contains p.id then
        tryWriteMessage uri (Notification.mk "$/cancelRequest" p) (queueFailedMessage := false)

  def forwardNotification {α : Type} [ToJson α] [FileSource α] (method : String) (params : α)
      : ServerM Unit :=
    tryWriteMessage (fileSource params) (Notification.mk method params) (queueFailedMessage := true)
end NotificationHandling

section MessageHandling
  def parseParams (paramType : Type) [FromJson paramType] (params : Json) : ServerM paramType :=
    match fromJson? params with
    | Except.ok parsed =>
      pure parsed
    | Except.error inner =>
      throwServerError s!"Got param with wrong structure: {params.compress}\n{inner}"

  def forwardRequestToWorker (id : RequestID) (method : String) (params : Json) : ServerM Unit := do
    let uri: DocumentUri ←
      -- This request is handled specially.
      if method == "$/lean/rpc/connect" then
        let ps ← parseParams Lsp.RpcConnectParams params
        pure <| fileSource ps
      else match (← routeLspRequest method params) with
      | Except.error e =>
        (←read).hOut.writeLspResponseError <| e.toLspResponseError id
        return
      | Except.ok uri => pure uri
    let some fw ← findFileWorker? uri
      /- Clients may send requests to closed files, which we respond to with an error.
      For example, VSCode sometimes sends requests just after closing a file,
      and RPC clients may also do so, e.g. due to remaining timers. -/
      | do
        (←read).hOut.writeLspResponseError
          { id      := id
            /- Some clients (VSCode) also send requests *before* opening a file. We reply
            with `contentModified` as that does not display a "request failed" popup. -/
            code    := ErrorCode.contentModified
            message := s!"Cannot process request to closed file '{uri}'" }
        return
    let r := Request.mk id method params
    fw.pendingRequestsRef.modify (·.insert id r)
    tryWriteMessage uri r

  def handleRequest (id : RequestID) (method : String) (params : Json) : ServerM Unit := do
    let handle α β [FromJson α] [ToJson β] (handler : α → ServerM β) : ServerM Unit := do
      let hOut := (← read).hOut
      try
        let params ← parseParams α params
        let result ← handler params
        hOut.writeLspResponse ⟨id, result⟩
      catch
        -- TODO Do fancier error handling, like in file worker?
        | e => hOut.writeLspResponseError {
          id := id
          code := ErrorCode.internalError
          message := s!"Failed to process request {id}: {e}"
        }
    -- If a definition is in a different, modified file, the ilean data should
    -- have the correct location while the olean still has outdated info from
    -- the last compilation. This is easier than catching the client's reply and
    -- fixing the definition's location afterwards, but it doesn't work for
    -- go-to-type-definition.
    if method == "textDocument/definition" || method == "textDocument/declaration" then
      let params ← parseParams TextDocumentPositionParams params
      let definitions ← findDefinitions params
      if !definitions.isEmpty then
        (← read).hOut.writeLspResponse ⟨id, definitions⟩
        return
    match method with
      | "textDocument/references" =>
        handle ReferenceParams (Array Location) handleReference
      | "workspace/symbol" =>
        handle WorkspaceSymbolParams (Array SymbolInformation) handleWorkspaceSymbol
      | "textDocument/prepareCallHierarchy" =>
        handle CallHierarchyPrepareParams (Array CallHierarchyItem) handlePrepareCallHierarchy
      | "callHierarchy/incomingCalls" =>
        handle CallHierarchyIncomingCallsParams (Array CallHierarchyIncomingCall)
          handleCallHierarchyIncomingCalls
      | "callHierarchy/outgoingCalls" =>
        handle Lsp.CallHierarchyOutgoingCallsParams (Array CallHierarchyOutgoingCall)
          handleCallHierarchyOutgoingCalls
      | "textDocument/prepareRename" =>
        handle PrepareRenameParams (Option Range) handlePrepareRename
      | "textDocument/rename" =>
        handle RenameParams WorkspaceEdit handleRename
      | _ =>
        forwardRequestToWorker id method params

  def handleNotification (method : String) (params : Json) : ServerM Unit := do
    let handle := fun α [FromJson α] (handler : α → ServerM Unit) =>
      parseParams α params >>= handler
    match method with
    | "textDocument/didOpen" =>
      handle _ handleDidOpen
    | "textDocument/didChange" =>
      handle DidChangeTextDocumentParams handleDidChange
    | "textDocument/didClose" =>
      handle DidCloseTextDocumentParams handleDidClose
    | "textDocument/didSave" =>
      handle DidSaveTextDocumentParams handleDidSave
    | "workspace/didChangeWatchedFiles" =>
      handle DidChangeWatchedFilesParams handleDidChangeWatchedFiles
    | "$/cancelRequest" =>
      handle CancelParams handleCancelRequest
    | "$/lean/rpc/connect" =>
      handle RpcConnectParams (forwardNotification method)
    | "$/lean/rpc/release" =>
      handle RpcReleaseParams (forwardNotification method)
    | "$/lean/rpc/keepAlive"  =>
      handle RpcKeepAliveParams (forwardNotification method)
    | _ =>
      -- implementation-dependent notifications can be safely ignored
      if !"$/".isPrefixOf method then
        (←read).hLog.putStrLn s!"Got unsupported notification: {method}"

  def handleResponse (id : RequestID) (result : Json) : ServerM Unit := do
    let some translation ← (← read).serverRequestData.modifyGet (·.translateInboundResponse id)
      | return
    tryWriteMessage translation.sourceUri (Response.mk translation.localID result)

  def handleResponseError
      (id      : RequestID)
      (code    : ErrorCode)
      (message : String)
      (data?   : Option Json)
      : ServerM Unit := do
    let some translation ← (← read).serverRequestData.modifyGet (·.translateInboundResponse id)
      | return
    tryWriteMessage translation.sourceUri (ResponseError.mk translation.localID code message data?)
end MessageHandling

section MainLoop
  def shutdown : ServerM Unit := do
    let fileWorkers ← (←read).fileWorkersRef.get
    for ⟨uri, _⟩ in fileWorkers do
      terminateFileWorker uri
    for ⟨_, fw⟩ in fileWorkers do
      -- TODO: Wait for process group to finish instead
      try let _ ← fw.killProcAndWait catch _ => pure ()

  inductive ServerEvent where
    | workerEvent (fw : FileWorker) (ev : WorkerEvent)
    | clientMsg (msg : JsonRpc.Message)
    | clientError (e : IO.Error)

  def runClientTask : ServerM (ServerTask ServerEvent) := do
    let st ← read
    let readMsgAction : IO ServerEvent := do
      /- Runs asynchronously. -/
      let msg ← st.hIn.readLspMessage
      pure <| ServerEvent.clientMsg msg
    let clientTask := (← ServerTask.IO.asTask readMsgAction).mapCheap fun
      | Except.ok ev   => ev
      | Except.error e => ServerEvent.clientError e
    return clientTask

  partial def mainLoop (clientTask : ServerTask ServerEvent) : ServerM Unit := do
    let st ← read
    let workers ← st.fileWorkersRef.get
    let mut workerTasks := #[]
    for (_, fw) in workers do
      -- When the forwarding task crashes, its return value will be stuck at
      -- `WorkerEvent.crashed _`.
      -- We want to handle this event only once, not over and over again,
      -- so once the state becomes `WorkerState.crashed _ .fileWorkerToClientForwarding`
      -- as a result of `WorkerEvent.crashed _`, we stop handling this event until
      -- eventually the file worker is restarted by a notification from the client.
      -- We do not want to filter the forwarding task in case of
      -- `WorkerState.crashed _ .clientToFileWorkerForwarding`, since the forwarding task
      -- exit code may still contain valuable information in this case (e.g. that the imports changed).
      if !(fw.state matches WorkerState.crashed _ .fileWorkerToClientForwarding) then
        workerTasks := workerTasks.push <| fw.commTask.mapCheap (ServerEvent.workerEvent fw)

    let ev ← ServerTask.waitAny (clientTask :: workerTasks.toList)
    match ev with
    | ServerEvent.clientMsg msg =>
      match msg with
      | Message.request id "shutdown" _ =>
        shutdown
        st.hOut.writeLspResponse ⟨id, Json.null⟩
      | Message.request id method (some params) =>
        handleRequest id method (toJson params)
        mainLoop (←runClientTask)
      | Message.response id result =>
        handleResponse id result
        mainLoop (←runClientTask)
      | Message.responseError id code message data? =>
        handleResponseError id code message data?
        mainLoop (←runClientTask)
      | Message.notification method (some params) =>
        handleNotification method (toJson params)
        mainLoop (←runClientTask)
      | _ => throwServerError "Got invalid JSON-RPC message"
    | ServerEvent.clientError e => throw e
    | ServerEvent.workerEvent fw ev =>
      match ev with
      | WorkerEvent.ioError e =>
        throwServerError s!"IO error while processing events for {fw.doc.uri}: {e}"
      | WorkerEvent.crashed _ =>
        handleCrash fw.doc.uri fw.queuedMsgs .fileWorkerToClientForwarding
        mainLoop clientTask
      | WorkerEvent.terminated =>
        throwServerError <| "Internal server error: got termination event for worker that "
          ++ "should have been removed"
      | .importsChanged =>
        let uri := fw.doc.uri
        let queuedMsgs := fw.queuedMsgs
        startFileWorker fw.doc
        tryDischargeQueuedMessages uri queuedMsgs
        mainLoop clientTask
end MainLoop

def mkLeanServerCapabilities : ServerCapabilities := {
  textDocumentSync? := some {
    openClose         := true
    change            := TextDocumentSyncKind.incremental
    willSave          := false
    willSaveWaitUntil := false
    save?             := some { includeText := true }
  }
  -- refine
  completionProvider? := some {
    triggerCharacters? := some #["."]
    resolveProvider := true
  }
  hoverProvider := true
  declarationProvider := true
  definitionProvider := true
  typeDefinitionProvider := true
  referencesProvider := true
  callHierarchyProvider := true
  renameProvider? := some {
    prepareProvider := true
  }
  workspaceSymbolProvider := true
  documentHighlightProvider := true
  documentSymbolProvider := true
  foldingRangeProvider := true
  semanticTokensProvider? := some {
    legend := {
      tokenTypes     := SemanticTokenType.names
      tokenModifiers := SemanticTokenModifier.names
    }
    full  := true
    range := true
  }
  codeActionProvider? := some {
    resolveProvider? := true,
    codeActionKinds? := some #["quickfix", "refactor"]
  }
  inlayHintProvider? := some {
    resolveProvider? := false
  }
}

def initAndRunWatchdogAux : ServerM Unit := do
  let st ← read
  try
    discard $ st.hIn.readLspNotificationAs "initialized" InitializedParams
    st.hOut.writeLspRequest {
      id := RequestID.str "register_lean_watcher"
      method := "client/registerCapability"
      param := some {
        registrations := #[ {
          id := "lean_watcher"
          method := "workspace/didChangeWatchedFiles"
          registerOptions := some <| toJson {
            watchers := #[ { globPattern := "**/*.lean" }, { globPattern := "**/*.ilean" } ]
          : DidChangeWatchedFilesRegistrationOptions }
        } ]
      : RegistrationParams }
    }
    let clientTask ← runClientTask
    mainLoop clientTask
  catch err =>
    shutdown
    throw err

  while true do
    let msg: JsonRpc.Message ←
      try
        st.hIn.readLspMessage
      catch _ =>
        /-
        NOTE(WN): It looks like instead of sending the `exit` notification,
        VSCode sometimes just closes the stream. In that case, pretend we got an `exit`.
        -/
        pure (Message.notification "exit" none)
    match msg with
    | .notification "exit" none =>
      break
    | .request id _ _ =>
      -- The LSP spec suggests that requests after 'shutdown' should be errored in this manner.
      st.hOut.writeLspResponseError {
        id,
        code := .invalidRequest,
        message := "Request received after 'shutdown' request."
      }
    | _ =>
      -- Ignore all other message types.
      continue

def findWorkerPath : IO System.FilePath := do
  let mut workerPath ← IO.appPath
  if let some path := (←IO.getEnv "LEAN_SYSROOT") then
    workerPath := System.FilePath.mk path / "bin" / "lean"
      |>.addExtension System.FilePath.exeExtension
  if let some path := (←IO.getEnv "LEAN_WORKER_PATH") then
    workerPath := System.FilePath.mk path
  return workerPath

/--
Starts loading .ileans present in the search path asynchronously in an IO task.
This ensures that server startup is not blocked by loading the .ileans.
In return, while the .ileans are being loaded, users will only get incomplete
results in requests that need references.
-/
def startLoadingReferences (references : IO.Ref References) : IO Unit := do
  -- Discard the task; there isn't much we can do about this failing,
  -- but we should try to continue server operations regardless
  let _ ← ServerTask.IO.asTask do
    let oleanSearchPath ← Lean.searchPathRef.get
    for path in ← oleanSearchPath.findAllWithExt "ilean" do
      try
        let ilean ← Ilean.load path
        references.modify fun refs =>
          refs.addIlean path ilean
      catch _ =>
        -- could be a race with the build system, for example
        -- ilean load errors should not be fatal, but we *should* log them
        -- when we add logging to the server
        pure ()

def initAndRunWatchdog (args : List String) (i o e : FS.Stream) : IO Unit := do
  let workerPath ← findWorkerPath
  let srcSearchPath ← initSrcSearchPath
  let references ← IO.mkRef .empty
  startLoadingReferences references
  let fileWorkersRef ← IO.mkRef (RBMap.empty : FileWorkerMap)
  let serverRequestData ← IO.mkRef {
    pendingServerRequests := RBMap.empty
    freshServerRequestID  := 0
  }
  let importData ← IO.mkRef ⟨RBMap.empty, RBMap.empty⟩
  let i ← maybeTee "wdIn.txt" false i
  let o ← maybeTee "wdOut.txt" true o
  let e ← maybeTee "wdErr.txt" true e
  let initRequest ← i.readLspRequestAs "initialize" InitializeParams
  o.writeLspResponse {
    id     := initRequest.id
    result := {
      capabilities := mkLeanServerCapabilities
      serverInfo?  := some {
        name     := "Lean 4 Server"
        version? := "0.2.0"
      }
      : InitializeResult
    }
  }
  ReaderT.run initAndRunWatchdogAux {
    hIn              := i
    hOut             := o
    hLog             := e
    args             := args
    fileWorkersRef   := fileWorkersRef
    initParams       := initRequest.param
    workerPath
    srcSearchPath
    references
    serverRequestData
    importData
    : ServerContext
  }

@[export lean_server_watchdog_main]
def watchdogMain (args : List String) : IO UInt32 := do
  let i ← IO.getStdin
  let o ← IO.getStdout
  let e ← IO.getStderr
  try
    initAndRunWatchdog args i o e
    IO.Process.exit 0 -- Terminate all tasks of this process
  catch err =>
    e.putStrLn s!"Watchdog error: {err}"
    IO.Process.exit 1 -- Terminate all tasks of this process

end Lean.Server.Watchdog
