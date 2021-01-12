/-
Copyright (c) 2020 Marc Huisinga. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Marc Huisinga, Wojciech Nawrocki
-/
import Init.System.IO
import Std.Data.RBMap

import Lean.Environment
import Lean.PrettyPrinter

import Lean.Data.Lsp
import Lean.Data.Json.FromToJson

import Lean.Server.Snapshots
import Lean.Server.Utils
import Lean.Server.AsyncList
import Lean.Server.InfoUtils

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
On didChange notifications, we search for the task in which the change occured. If we stumble across
a task that has not yet finished before finding the task we're looking for, we terminate it
and start the elaboration there, otherwise we start the elaboration at the task where the change occured.

Requests iterate over tasks until they find the command that they need to answer the request.
In order to not block the main thread, this is done in a request task.
If a task that the request task waits for is terminated, a change occured somewhere before the
command that the request is looking for and the request sends a "content changed" error.
-/

namespace Lean.Server.FileWorker

open Lsp
open IO
open Snapshots
open Lean.Parser.Command

section Utils
  private def logSnapContent (s : Snapshot) (text : FileMap) : IO Unit :=
    IO.eprintln s!"[{s.beginPos}, {s.endPos}]: `{text.source.extract s.beginPos (s.endPos-1)}`"

  inductive ElabTaskError where
    | aborted
    | eof
    | ioError (e : IO.Error)

  instance : Coe IO.Error ElabTaskError := ⟨ElabTaskError.ioError⟩

  structure CancelToken where
    ref : IO.Ref Bool
    deriving Inhabited

  namespace CancelToken
    def new : IO CancelToken :=
      CancelToken.mk <$> IO.mkRef false

    def check [MonadExceptOf ElabTaskError m] [MonadLiftT (ST RealWorld) m] [Monad m] (tk : CancelToken) : m Unit := do
      let c ← tk.ref.get
      if c = true then
        throw ElabTaskError.aborted

    def set (tk : CancelToken) : IO Unit :=
      tk.ref.set true
  end CancelToken

  /-- A document editable in the sense that we track the environment
  and parser state after each command so that edits can be applied
  without recompiling code appearing earlier in the file. -/
  structure EditableDocument where
    meta       : DocumentMeta
    /- The first snapshot is that after the header. -/
    headerSnap : Snapshot
    /- Subsequent snapshots occur after each command. -/
    cmdSnaps   : AsyncList ElabTaskError Snapshot
    cancelTk   : CancelToken
    deriving Inhabited
end Utils

open IO
open Std (RBMap RBMap.empty)
open JsonRpc

section ServerM
  -- Pending requests are tracked so they can be cancelled
  abbrev PendingRequestMap := RBMap RequestID (Task (Except IO.Error Unit)) (fun a b => Decidable.decide (a < b))

  structure ServerContext where
    hIn                : FS.Stream
    hOut               : FS.Stream
    hLog               : FS.Stream
    docRef             : IO.Ref EditableDocument
    pendingRequestsRef : IO.Ref PendingRequestMap

  abbrev ServerM := ReaderT ServerContext IO

  def updatePendingRequests (map : PendingRequestMap → PendingRequestMap) : ServerM Unit := do
    (←read).pendingRequestsRef.modify map

  /-- Elaborates the next command after `parentSnap` and emits diagnostics. -/
  private def nextCmdSnap (m : DocumentMeta) (parentSnap : Snapshot) (cancelTk : CancelToken) : ExceptT ElabTaskError ServerM Snapshot := do
    cancelTk.check
    let st ← read
    let maybeSnap ← compileNextCmd m.text.source parentSnap
    -- TODO(MH): check for interrupt with increased precision
    cancelTk.check
    let sendDiagnostics (msgLog : MessageLog) : IO Unit := do
      let diagnostics ← msgLog.msgs.mapM (msgToDiagnostic m.text)
      st.hOut.writeLspNotification {
        method := "textDocument/publishDiagnostics"
        param  := {
          uri         := m.uri
          version?    := m.version
          diagnostics := diagnostics.toArray
          : PublishDiagnosticsParams
        }
      }
    match maybeSnap with
    | Sum.inl snap =>
      /- NOTE(MH): This relies on the client discarding old diagnostics upon receiving new ones
        while prefering newer versions over old ones. The former is necessary because we do
        not explicitly clear older diagnostics, while the latter is necessary because we do
        not guarantee that diagnostics are emitted in order. Specifically, it may happen that
        we interrupted this elaboration task right at this point and a newer elaboration task
        emits diagnostics, after which we emit old diagnostics because we did not yet detect
        the interrupt. Explicitly clearing diagnostics is difficult for a similar reason,
        because we cannot guarantee that no further diagnostics are emitted after clearing
        them. -/
      sendDiagnostics <| snap.msgLog.add {
        fileName := "<ignored>"
        pos      := m.text.toPosition snap.endPos
        severity := MessageSeverity.information
        data     := "processing..."
      }
      snap
    | Sum.inr msgLog =>
      sendDiagnostics msgLog
      throw ElabTaskError.eof

  /-- Elaborates all commands after `initSnap`, emitting the diagnostics. -/
  def unfoldCmdSnaps (m : DocumentMeta) (initSnap : Snapshot) (cancelTk : CancelToken) : ServerM (AsyncList ElabTaskError Snapshot) := do
    AsyncList.unfoldAsync (nextCmdSnap m . cancelTk (←read)) initSnap

  /-- Compiles the contents of a Lean file. -/
  def compileDocument (m : DocumentMeta) : ServerM Unit := do
    let headerSnap@{ data := SnapshotData.headerData cmdState, .. } ← Snapshots.compileHeader m.text.source
      | throwServerError "Internal server error: invalid header snapshot"
    let opts : Options := {}
    let opts := opts.setBool `interpreter.prefer_native false
    let cmdState := { cmdState with infoState.enabled := true, scopes := [{ header := "", opts := opts }] }
    let headerSnap := { headerSnap with data := SnapshotData.headerData cmdState }
    let cancelTk ← CancelToken.new
    let cmdSnaps ← unfoldCmdSnaps m headerSnap cancelTk
    (←read).docRef.set ⟨m, headerSnap, cmdSnaps, cancelTk⟩

  /-- Given the new document and `changePos`, the UTF-8 offset of a change into the pre-change source,
      updates editable doc state. -/
  def updateDocument (newMeta : DocumentMeta) (changePos : String.Pos) : ServerM Unit := do
    -- The watchdog only restarts the file worker when the syntax tree of the header changes.
    -- If e.g. a newline is deleted, it will not restart this file worker, but we still
    -- need to reparse the header so that the offsets are correct.
    let st ← read
    let oldDoc ← st.docRef.get
    let newHeaderSnap ← reparseHeader newMeta.text.source oldDoc.headerSnap
    if newHeaderSnap.stx != oldDoc.headerSnap.stx then
      throwServerError "Internal server error: header changed but worker wasn't restarted."
    let ⟨cmdSnaps, e?⟩ ← oldDoc.cmdSnaps.updateFinishedPrefix
    match e? with
    -- This case should not be possible. only the main task aborts tasks and ensures that aborted tasks
    -- do not show up in `snapshots` of an EditableDocument.
    | some ElabTaskError.aborted =>
      throwServerError "Internal server error: elab task was aborted while still in use."
    | some (ElabTaskError.ioError ioError) => throw ioError
    | _ => -- No error or EOF
      oldDoc.cancelTk.set
      -- NOTE(WN): we invalidate eagerly as `endPos` consumes input greedily. To re-elaborate only
      -- when really necessary, we could do a whitespace-aware `Syntax` comparison instead.
      let mut validSnaps := cmdSnaps.finishedPrefix.takeWhile (fun s => s.endPos < changePos)
      if validSnaps.length = 0 then
        let cancelTk ← CancelToken.new
        let newCmdSnaps ← unfoldCmdSnaps newMeta newHeaderSnap cancelTk
        st.docRef.set ⟨newMeta, newHeaderSnap, newCmdSnaps, cancelTk⟩
      else
        /- When at least one valid non-header snap exists, it may happen that a change does not fall
           within the syntactic range of that last snap but still modifies it by appending tokens.
           We check for this here. We do not currently handle crazy grammars in which an appended
           token can merge two or more previous commands into one. To do so would require reparsing
           the entire file. -/
        let mut lastSnap := validSnaps.getLast!
        let preLastSnap :=
          if validSnaps.length ≥ 2
          then validSnaps.get! (validSnaps.length - 2)
          else newHeaderSnap
        let newLastStx ← parseNextCmd newMeta.text.source preLastSnap
        if newLastStx != lastSnap.stx then
          validSnaps ← validSnaps.dropLast
          lastSnap ← preLastSnap
        let cancelTk ← CancelToken.new
        let newSnaps ← unfoldCmdSnaps newMeta lastSnap cancelTk
        let newCmdSnaps := AsyncList.ofList validSnaps ++ newSnaps
        st.docRef.set ⟨newMeta, newHeaderSnap, newCmdSnaps, cancelTk⟩
end ServerM

/- Notifications are handled in the main thread. They may change global worker state
such as the current file contents. -/
section NotificationHandling
  def handleDidOpen (p : DidOpenTextDocumentParams) : ServerM Unit :=
    let doc := p.textDocument
    /- NOTE(WN): `toFileMap` marks line beginnings as immediately following
      "\n", which should be enough to handle both LF and CRLF correctly.
      This is because LSP always refers to characters by (line, column),
      so if we get the line number correct it shouldn't matter that there
      is a CR there. -/
    compileDocument ⟨doc.uri, doc.version, doc.text.toFileMap⟩

  def handleDidChange (p : DidChangeTextDocumentParams) : ServerM Unit := do
    let docId := p.textDocument
    let changes := p.contentChanges
    let oldDoc ← (←read).docRef.get
    let some newVersion ← pure docId.version?
      | throwServerError "Expected version number"
    if newVersion ≤ oldDoc.meta.version then
      -- TODO(WN): This happens on restart sometimes.
      IO.eprintln s!"Got outdated version number: {newVersion} ≤ {oldDoc.meta.version}"
    else if ¬ changes.isEmpty then
      let (newDocText, minStartOff) := foldDocumentChanges changes oldDoc.meta.text
      updateDocument ⟨docId.uri, newVersion, newDocText⟩ minStartOff

  def handleCancelRequest (p : CancelParams) : ServerM Unit := do
    updatePendingRequests (fun pendingRequests => pendingRequests.erase p.id)
end NotificationHandling

/- Request handlers are given by `Task`s executed asynchronously. They may be cancelled at any time,
so they should check the cancellation token when possible to handle this cooperatively. Any exceptions
thrown in a handler will be reported to the client as LSP error responses. -/
section RequestHandling
  structure RequestError where
    code    : ErrorCode
    message : String

  namespace RequestError

  def fileChanged : RequestError :=
    { code := ErrorCode.contentModified
      message := "File changed." }

  end RequestError

  -- TODO(WN): the type is too complicated
  abbrev RequestM α := ServerM $ Task $ Except IO.Error $ Except RequestError α

  def mapTask (t : Task α) (f : α → ExceptT RequestError ServerM β) : RequestM β := fun st =>
    (IO.mapTask · t) fun a => f a st

  /- Requests that need data from a certain command should traverse the snapshots
     by successively getting the next task, meaning that we might need to wait for elaboration.
     When that happens, the request should send a "content changed" error to the user
     (this way, the server doesn't get bogged down in requests for an old state of the document).
     Requests need to manually check for whether their task has been cancelled, so that they
     can reply with a RequestCancelled error. -/
  open Elab in
  partial def handleHover (id : RequestID) (p : HoverParams)
    : ServerM (Task (Except IO.Error (Except RequestError (Option Hover)))) := do
    let st ← read
    let doc ← st.docRef.get
    let text := doc.meta.text
    let hoverPos := text.lspPosToUtf8Pos p.position
    let findTask ← doc.cmdSnaps.waitFind? (fun s => s.endPos > hoverPos)
    let mkHover (s : String) (f : String.Pos) (t : String.Pos) : Hover :=
      { contents := { kind := MarkupKind.markdown
                      value := s }
        range? := some { start := text.utf8PosToLspPos f
                         «end» := text.utf8PosToLspPos t } }
    mapTask findTask fun
      | Except.error ElabTaskError.aborted =>
        throwThe RequestError RequestError.fileChanged
      | Except.error (ElabTaskError.ioError e) =>
        throwThe IO.Error e
      | Except.error ElabTaskError.eof =>
        return none
      | Except.ok (some snap) => do
        for t in snap.toCmdState.infoState.trees do
          let ts := t.smallestNodes fun
            | Info.ofTermInfo i =>
              match i.pos?, i.tailPos? with
              | some pos, some tailPos =>
                /- TODO(WN): when we have a way to do so,
                check for synthetic syntax and allow arbitrary syntax kinds. -/
                if pos ≤ hoverPos ∧ hoverPos < tailPos then
                  #[identKind,
                    strLitKind,
                    charLitKind,
                    numLitKind,
                    scientificLitKind,
                    nameLitKind,
                    fieldIdxKind,
                    interpolatedStrLitKind,
                    interpolatedStrKind
                  ].contains i.stx.getKind
                else false
              | _, _ => false
            | _ => false
          let mut nds : Array (Nat × ContextInfo × TermInfo) := #[]
          for t in ts do
            if let InfoTree.context ci (InfoTree.node (Info.ofTermInfo i) _) := t then
              let diff := i.tailPos?.get! - i.pos?.get!
              nds := nds.push (diff, ci, i)

          if let some (_, ci, i) := nds.getMax? (fun a b => a.1 > b.1) then
            let tFmt ← ci.runMetaM i.lctx do
              return f!"{← Meta.ppExpr i.expr} : {← Meta.ppExpr (← Meta.inferType i.expr)}"
            let mut hoverFmt := f!"```lean
{tFmt}
```"
            if let Expr.const n .. := i.expr then
              if let some doc ← ci.runMetaM i.lctx <| findDocString? n then
                hoverFmt := f!"{hoverFmt}\n***\n{doc}"

            return some <| mkHover (toString hoverFmt) i.pos?.get! i.tailPos?.get!
          pure ()

        return none
      | Except.ok none => return none

  def handleWaitForDiagnostics (id : RequestID) (p : WaitForDiagnosticsParam)
    : ServerM (Task (Except IO.Error (Except RequestError WaitForDiagnostics))) := do
    let st ← read
    let doc ← st.docRef.get
    let t ← doc.cmdSnaps.waitAll
    t.map fun _ => Except.ok $ Except.ok WaitForDiagnostics.mk

  def rangeOfSyntax (text : FileMap) (stx : Syntax) : Range :=
    ⟨text.utf8PosToLspPos <| stx.getHeadInfo.get!.pos.get!,
     text.utf8PosToLspPos <| stx.getTailPos.get!⟩

  partial def handleDocumentSymbol (id : RequestID) (p : DocumentSymbolParams) :
    ServerM (Task (Except IO.Error (Except RequestError DocumentSymbolResult))) := do
    let st ← read
    asTask do
      let doc ← st.docRef.get
      let ⟨cmdSnaps, e?⟩ ← doc.cmdSnaps.updateFinishedPrefix
      let mut stxs := cmdSnaps.finishedPrefix.map Snapshot.stx
      match e? with
      | some ElabTaskError.aborted =>
        return Except.error RequestError.fileChanged
      | some _ => pure () -- TODO(WN): what to do on ioError?
      | none =>
        let lastSnap := cmdSnaps.finishedPrefix.getLastD doc.headerSnap
        stxs := stxs ++ (← parseAhead doc.meta.text.source lastSnap).toList
      let (syms, _) := toDocumentSymbols doc.meta.text stxs
      return Except.ok { syms := syms.toArray }
    where
      toDocumentSymbols (text : FileMap)
      | [] => ([], [])
      | stx::stxs => match stx with
        | `(namespace $id) => sectionLikeToDocumentSymbols text stx stxs (id.getId.toString) SymbolKind.namespace id
        | `(section $(id)?) => sectionLikeToDocumentSymbols text stx stxs ((·.getId.toString) <$> id |>.getD "<section>") SymbolKind.namespace (id.getD stx)
        | `(end $(id)?) => ([], stx::stxs)
        | _ =>
          let (syms, stxs') := toDocumentSymbols text stxs
          if stx.isOfKind ``Lean.Parser.Command.declaration then
            let (name, selection) := match stx with
              | `($dm:declModifiers $ak:attrKind instance $[$np:namedPrio]? $[$id:ident$[.{$ls,*}]?]? $sig:declSig $val) =>
                ((·.getId.toString) <$> id |>.getD s!"instance {sig.reprint.getD ""}", id.getD sig)
              | _ => match stx[1][1] with
                | `(declId|$id:ident$[.{$ls,*}]?) => (id.getId.toString, id)
                | _                               => (stx[1][0].isIdOrAtom?.getD "<unknown>", stx[1][0])
            (DocumentSymbol.mk {
              name := name
              kind := SymbolKind.method
              range := rangeOfSyntax text stx
              selectionRange := rangeOfSyntax text selection
            } :: syms, stxs')
          else
            (syms, stxs')
      sectionLikeToDocumentSymbols (text : FileMap) (stx : Syntax) (stxs : List Syntax) (name : String) (kind : SymbolKind) (selection : Syntax) :=
          let (syms, stxs') := toDocumentSymbols text stxs
          -- discard `end`
          let (syms', stxs'') := toDocumentSymbols text (stxs'.drop 1)
          let endStx := match stxs' with
            | endStx::_ => endStx
            | []        => (stx::stxs').getLast!
          (DocumentSymbol.mk {
            name := name
            kind := kind
            range := ⟨(rangeOfSyntax text stx).start, (rangeOfSyntax text endStx).«end»⟩
            selectionRange := rangeOfSyntax text selection
            children? := syms.toArray
          } :: syms', stxs'')

end RequestHandling

section MessageHandling
  def parseParams (paramType : Type) [FromJson paramType] (params : Json) : ServerM paramType :=
    match fromJson? params with
    | some parsed => pure parsed
    | none        => throwServerError s!"Got param with wrong structure: {params.compress}"

  def handleNotification (method : String) (params : Json) : ServerM Unit := do
    let handle := fun paramType [FromJson paramType] (handler : paramType → ServerM Unit) =>
      parseParams paramType params >>= handler
    match method with
    | "textDocument/didChange" => handle DidChangeTextDocumentParams handleDidChange
    | "$/cancelRequest"        => handle CancelParams handleCancelRequest
    | _                        => throwServerError s!"Got unsupported notification method: {method}"

  def queueRequest (id : RequestID) (requestTask : Task (Except IO.Error Unit))
  : ServerM Unit := do
    updatePendingRequests (fun pendingRequests => pendingRequests.insert id requestTask)

  def handleRequest (id : RequestID) (method : String) (params : Json)
  : ServerM Unit := do
    let handle := fun paramType [FromJson paramType] respType [ToJson respType]
                      (handler : RequestID → paramType → RequestM respType) => do
      let st ← read
      let p ← parseParams paramType params
      let t ← handler id p
      let t₁ ← (IO.mapTask · t) fun
        | Except.ok (Except.ok resp) =>
          st.hOut.writeLspResponse ⟨id, resp⟩
        | Except.ok (Except.error e) =>
          st.hOut.writeLspResponseError { id := id, code := e.code, message := e.message }
        | Except.error e =>
          st.hOut.writeLspResponseError { id := id, code := ErrorCode.internalError, message := toString e }
      queueRequest id t₁
    match method with
    | "textDocument/waitForDiagnostics" => handle WaitForDiagnosticsParam WaitForDiagnostics handleWaitForDiagnostics
    | "textDocument/hover"              => handle HoverParams (Option Hover) handleHover
    | "textDocument/documentSymbol"     => handle DocumentSymbolParams DocumentSymbolResult handleDocumentSymbol
    | _ => throwServerError s!"Got unsupported request: {method}"
end MessageHandling

section MainLoop
  partial def mainLoop : ServerM Unit := do
    let st ← read
    let msg ← st.hIn.readLspMessage
    let pendingRequests ← st.pendingRequestsRef.get
    let filterFinishedTasks (acc : PendingRequestMap) (id : RequestID) (task : Task (Except IO.Error Unit))
      : ServerM PendingRequestMap := do
      if (←hasFinished task) then
        /- Handler tasks are constructed so that the only possible errors here
        are failures of writing a response into the stream. -/
        if let Except.error e := task.get then
          throwServerError s!"Failed responding to request {id}: {e}"
        acc.erase id
      else acc
    let pendingRequests ← pendingRequests.foldM filterFinishedTasks pendingRequests
    st.pendingRequestsRef.set pendingRequests
    match msg with
    | Message.request id method (some params) =>
      handleRequest id method (toJson params)
      mainLoop
    | Message.notification "exit" none =>
      let doc ← st.docRef.get
      doc.cancelTk.set
      return ()
    | Message.notification method (some params) =>
      handleNotification method (toJson params)
      mainLoop
    | _ => throwServerError "Got invalid JSON-RPC message"
end MainLoop

def initAndRunWorker (i o e : FS.Stream) : IO UInt32 := do
  let i ← maybeTee "fwIn.txt" false i
  let o ← maybeTee "fwOut.txt" true o
  -- TODO(WN): act in accordance with InitializeParams
  let _ ← i.readLspRequestAs "initialize" InitializeParams
  let ⟨_, param⟩ ← i.readLspNotificationAs "textDocument/didOpen" DidOpenTextDocumentParams
  let e ← e.withPrefix s!"[{param.textDocument.uri}] "
  let _ ← IO.setStderr e
  let ctx : ServerContext := {
    hIn                := i
    hOut               := o
    hLog               := e
    -- `openDocument` will not access `docRef`, but set it
    docRef             := ←IO.mkRef arbitrary
    pendingRequestsRef := ←IO.mkRef (RBMap.empty : PendingRequestMap)
  }
  ReaderT.run (r := ctx) try
    handleDidOpen param
    mainLoop
    return 0
  catch e =>
    o.writeLspNotification {
      method := "textDocument/publishDiagnostics"
      param  := {
        uri         := param.textDocument.uri
        version?    := param.textDocument.version
        diagnostics := #[{ range := ⟨⟨0, 0⟩, ⟨0, 0⟩⟩, severity? := DiagnosticSeverity.error, message := e.toString }]
        : PublishDiagnosticsParams
      }
    }
    return 1

@[export lean_server_worker_main]
def workerMain : IO UInt32 := do
  let i ← IO.getStdin
  let o ← IO.getStdout
  let e ← IO.getStderr
  try
    initAndRunWorker i o e
  catch err =>
    e.putStrLn s!"worker initialization error: {err}"
    return 1

end Lean.Server.FileWorker

