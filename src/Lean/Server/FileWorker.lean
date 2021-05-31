/-
Copyright (c) 2020 Marc Huisinga. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Marc Huisinga, Wojciech Nawrocki
-/
import Init.System.IO
import Std.Data.RBMap

import Lean.Environment
import Lean.PrettyPrinter
import Lean.DeclarationRange

import Lean.Data.Lsp
import Lean.Data.Json.FromToJson

import Lean.Server.Snapshots
import Lean.Server.Utils
import Lean.Server.AsyncList
import Lean.Server.InfoUtils
import Lean.Server.Completion

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
open Std (RBMap RBMap.empty)
open JsonRpc

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
      if c then
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

/- Asynchronous snapshot elaboration. -/
section Elab
  /-- Elaborates the next command after `parentSnap` and emits diagnostics into `hOut`. -/
  private def nextCmdSnap (m : DocumentMeta) (parentSnap : Snapshot) (cancelTk : CancelToken) (hOut : FS.Stream)
  : ExceptT ElabTaskError IO Snapshot := do
    cancelTk.check
    let maybeSnap ← compileNextCmd m.text.source parentSnap
    -- TODO(MH): check for interrupt with increased precision
    cancelTk.check
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
      publishMessages m (snap.msgLog.add {
        fileName := "<ignored>"
        pos      := m.text.toPosition snap.endPos
        severity := MessageSeverity.information
        data     := "processing..."
      }) hOut
      snap
    | Sum.inr msgLog =>
      publishMessages m msgLog hOut
      throw ElabTaskError.eof

  /-- Elaborates all commands after `initSnap`, emitting the diagnostics into `hOut`. -/
  def unfoldCmdSnaps (m : DocumentMeta) (initSnap : Snapshot) (cancelTk : CancelToken) (hOut : FS.Stream)
    (initial : Bool) :
      IO (AsyncList ElabTaskError Snapshot) := do
    if initial && initSnap.msgLog.hasErrors then
      -- treat header processing errors as fatal so users aren't swamped with followup errors
      AsyncList.nil
    else
      AsyncList.unfoldAsync (nextCmdSnap m . cancelTk hOut) initSnap
end Elab

-- Pending requests are tracked so they can be cancelled
abbrev PendingRequestMap := RBMap RequestID (Task (Except IO.Error Unit)) compare

structure ServerContext where
  hIn                : FS.Stream
  hOut               : FS.Stream
  hLog               : FS.Stream
  srcSearchPath      : SearchPath
  docRef             : IO.Ref EditableDocument
  pendingRequestsRef : IO.Ref PendingRequestMap

abbrev ServerM := ReaderT ServerContext IO

/- Worker initialization sequence. -/
section Initialization
  /-- Use `leanpkg print-paths` to compile dependencies on the fly and add them to `LEAN_PATH`.
  Compilation progress is reported to `hOut` via LSP notifications. Return the search path for
  source files. -/
  partial def leanpkgSetupSearchPath (leanpkgPath : System.FilePath) (m : DocumentMeta) (imports : Array Import) (hOut : FS.Stream) : IO SearchPath := do
    let leanpkgProc ← Process.spawn {
      stdin  := Process.Stdio.null
      stdout := Process.Stdio.piped
      stderr := Process.Stdio.piped
      cmd    := leanpkgPath.toString
      args   := #["print-paths"] ++ imports.map (toString ·.module)
    }
    -- progress notification: report latest stderr line
    let rec processStderr (acc : String) : IO String := do
      let line ← leanpkgProc.stderr.getLine
      if line == "" then
        return acc
      else
        publishDiagnostics m #[{ range := ⟨⟨0, 0⟩, ⟨0, 0⟩⟩, severity? := DiagnosticSeverity.information, message := line }] hOut
        processStderr (acc ++ line)
    let stderr ← IO.asTask (processStderr "") Task.Priority.dedicated
    let stdout := String.trim (← leanpkgProc.stdout.readToEnd)
    let stderr ← IO.ofExcept stderr.get
    if (← leanpkgProc.wait) == 0 then
      let leanpkgLines := stdout.split (· == '\n')
      -- ignore any output up to the last two lines
      -- TODO: leanpkg should instead redirect nested stdout output to stderr
      let leanpkgLines := leanpkgLines.drop (leanpkgLines.length - 2)
      match leanpkgLines with
      | [""]                    => pure []  -- e.g. no leanpkg.toml
      | [leanPath, leanSrcPath] => let sp ← getBuiltinSearchPath
                                   let sp ← addSearchPathFromEnv sp
                                   let sp := System.SearchPath.parse leanPath ++ sp
                                   searchPathRef.set sp
                                   let srcPath := System.SearchPath.parse leanSrcPath
                                   srcPath.mapM realPathNormalized
      | _                       => throw <| IO.userError s!"unexpected output from `leanpkg print-paths`:\n{stdout}\nstderr:\n{stderr}"
    else
      throw <| IO.userError s!"`leanpkg print-paths` failed:\n{stdout}\nstderr:\n{stderr}"

  def compileHeader (m : DocumentMeta) (hOut : FS.Stream) : IO (Snapshot × SearchPath) := do
    let opts := {}  -- TODO
    let inputCtx := Parser.mkInputContext m.text.source "<input>"
    let (headerStx, headerParserState, msgLog) ← Parser.parseHeader inputCtx
    let leanpkgPath ← match ← IO.getEnv "LEAN_SYSROOT" with
      | some path => pure <| System.FilePath.mk path / "bin" / "leanpkg"
      | _         => pure <| (← appDir) / "leanpkg"
    let leanpkgPath := leanpkgPath.withExtension System.FilePath.exeExtension
    let mut srcSearchPath := [(← appDir) / ".." / "lib" / "lean" / "src"]
    if let some p := (← IO.getEnv "LEAN_SRC_PATH") then
      srcSearchPath := srcSearchPath ++ System.SearchPath.parse p
    let (headerEnv, msgLog) ← try
      -- NOTE: leanpkg does not exist in stage 0 (yet?)
      if (← System.FilePath.pathExists leanpkgPath) then
        let pkgSearchPath ← leanpkgSetupSearchPath leanpkgPath m (Lean.Elab.headerToImports headerStx).toArray hOut
        srcSearchPath := srcSearchPath ++ pkgSearchPath
      Elab.processHeader headerStx opts msgLog inputCtx
    catch e =>  -- should be from `leanpkg print-paths`
      let msgs := MessageLog.empty.add { fileName := "<ignored>", pos := ⟨0, 0⟩, data := e.toString }
      pure (← mkEmptyEnvironment, msgs)
    publishMessages m msgLog hOut
    let cmdState := Elab.Command.mkState headerEnv msgLog opts
    let cmdState := { cmdState with infoState.enabled := true, scopes := [{ header := "", opts := opts }] }
    let headerSnap := {
      beginPos := 0
      stx := headerStx
      mpState := headerParserState
      cmdState := cmdState
    }
    return (headerSnap, srcSearchPath)

  def initializeWorker (meta : DocumentMeta) (i o e : FS.Stream)
  : IO ServerContext := do
    /- NOTE(WN): `toFileMap` marks line beginnings as immediately following
      "\n", which should be enough to handle both LF and CRLF correctly.
      This is because LSP always refers to characters by (line, column),
      so if we get the line number correct it shouldn't matter that there
      is a CR there. -/
    let (headerSnap, srcSearchPath) ← compileHeader meta o
    let cancelTk ← CancelToken.new
    let cmdSnaps ← unfoldCmdSnaps meta headerSnap cancelTk o (initial := true)
    let doc : EditableDocument := ⟨meta, headerSnap, cmdSnaps, cancelTk⟩
    return {
      hIn                := i
      hOut               := o
      hLog               := e
      srcSearchPath      := srcSearchPath
      docRef             := ←IO.mkRef doc
      pendingRequestsRef := ←IO.mkRef RBMap.empty
    }
end Initialization

section Updates
  def updatePendingRequests (map : PendingRequestMap → PendingRequestMap) : ServerM Unit := do
    (←read).pendingRequestsRef.modify map

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
        let newCmdSnaps ← unfoldCmdSnaps newMeta newHeaderSnap cancelTk st.hOut (initial := true)
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
        let newSnaps ← unfoldCmdSnaps newMeta lastSnap cancelTk st.hOut (initial := false)
        let newCmdSnaps := AsyncList.ofList validSnaps ++ newSnaps
        st.docRef.set ⟨newMeta, newHeaderSnap, newCmdSnaps, cancelTk⟩
end Updates

/- Notifications are handled in the main thread. They may change global worker state
such as the current file contents. -/
section NotificationHandling
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

  /-- Create a task which waits for a snapshot matching `p`, handles various errors,
  and if a matching snapshot was found executes `x` with it. If not found, the task
  executes `notFoundX`. -/
  def withWaitFindSnap (doc : EditableDocument) (p : Snapshot → Bool)
    (notFoundX : ExceptT RequestError ServerM β)
    (x : Snapshot → ExceptT RequestError ServerM β)
    : ServerM (Task (Except IO.Error (Except RequestError β))) := do
    let findTask ← doc.cmdSnaps.waitFind? p
    mapTask findTask fun
      | Except.error ElabTaskError.aborted =>
        throwThe RequestError RequestError.fileChanged
      | Except.error (ElabTaskError.ioError e) =>
        throwThe IO.Error e
      | Except.error ElabTaskError.eof => notFoundX
      | Except.ok none => notFoundX
      | Except.ok (some snap) => x snap

  /- Requests that need data from a certain command should traverse the snapshots
     by successively getting the next task, meaning that we might need to wait for elaboration.
     When that happens, the request should send a "content changed" error to the user
     (this way, the server doesn't get bogged down in requests for an old state of the document).
     Requests need to manually check for whether their task has been cancelled, so that they
     can reply with a RequestCancelled error. -/

  partial def handleCompletion (p : CompletionParams) :
      ServerM (Task (Except IO.Error (Except RequestError CompletionList))) := do
    let st ← read
    let doc ← st.docRef.get
    let text := doc.meta.text
    let pos := text.lspPosToUtf8Pos p.position
    -- dbg_trace ">> handleCompletion invoked {pos}"
    -- NOTE: use `>=` since the cursor can be *after* the input
    withWaitFindSnap doc (fun s => s.endPos >= pos)
      (notFoundX := pure { items := #[], isIncomplete := true }) fun snap => do
        for infoTree in snap.cmdState.infoState.trees do
          -- for (ctx, info) in infoTree.getCompletionInfos do
          --   dbg_trace "{← info.format ctx}"
          if let some r ← Completion.find? doc.meta.text pos infoTree then
            return r
        return { items := #[ ], isIncomplete := true }

  open Elab in
  partial def handleHover (p : HoverParams)
    : ServerM (Task (Except IO.Error (Except RequestError (Option Hover)))) := do
    let st ← read
    let doc ← st.docRef.get
    let text := doc.meta.text
    let mkHover (s : String) (f : String.Pos) (t : String.Pos) : Hover :=
      { contents := { kind := MarkupKind.markdown
                      value := s }
        range? := some { start := text.utf8PosToLspPos f
                         «end» := text.utf8PosToLspPos t } }

    let hoverPos := text.lspPosToUtf8Pos p.position
    withWaitFindSnap doc (fun s => s.endPos > hoverPos)
      (notFoundX := pure none) fun snap => do
        for t in snap.cmdState.infoState.trees do
          if let some (ci, i) := t.hoverableInfoAt? hoverPos then
            if let some hoverFmt ← i.fmtHover? ci then
              return some <| mkHover (toString hoverFmt) i.pos?.get! i.tailPos?.get!

        return none

  open Elab in
  partial def handleDefinition (goToType? : Bool) (p : TextDocumentPositionParams)
    : ServerM (Task (Except IO.Error (Except RequestError (Array LocationLink)))) := do
    let st ← read
    let doc ← st.docRef.get
    let text := doc.meta.text
    let hoverPos := text.lspPosToUtf8Pos p.position
    withWaitFindSnap doc (fun s => s.endPos > hoverPos)
      (notFoundX := pure #[]) fun snap => do
        for t in snap.cmdState.infoState.trees do
          if let some (ci, Info.ofTermInfo i) := t.hoverableInfoAt? hoverPos then
            let mut expr := i.expr
            if goToType? then
              expr ← ci.runMetaM i.lctx do
                Meta.instantiateMVars (← Meta.inferType expr)
            if let some n := expr.constName? then
              let mod? ← ci.runMetaM i.lctx <| findModuleOf? n
              let modUri? ← match mod? with
                | some modName =>
                  let modFname? ← st.srcSearchPath.findWithExt "lean" modName
                  pure <| modFname?.map toFileUri
                | none         => pure <| some doc.meta.uri

              let ranges? ← ci.runMetaM i.lctx <| findDeclarationRanges? n
              if let (some ranges, some modUri) := (ranges?, modUri?) then
                let declRangeToLspRange (r : DeclarationRange) : Lsp.Range :=
                  { start := ⟨r.pos.line - 1, r.charUtf16⟩
                    «end» := ⟨r.endPos.line - 1, r.endCharUtf16⟩ }
                let ll : LocationLink := {
                  originSelectionRange? := some ⟨text.utf8PosToLspPos i.stx.getPos?.get!,
                                                 text.utf8PosToLspPos i.stx.getTailPos?.get!⟩
                  targetUri := modUri
                  targetRange := declRangeToLspRange ranges.range
                  targetSelectionRange := declRangeToLspRange ranges.selectionRange
                }
                return #[ll]
        return #[]

  open Elab in
  partial def handlePlainGoal (p : PlainGoalParams)
    : ServerM (Task (Except IO.Error (Except RequestError (Option PlainGoal)))) := do
    let st ← read
    let doc ← st.docRef.get
    let text := doc.meta.text
    let hoverPos := text.lspPosToUtf8Pos p.position
    -- NOTE: use `>=` since the cursor can be *after* the input
    withWaitFindSnap doc (fun s => s.endPos >= hoverPos)
      (notFoundX := return none) fun snap => do
        for t in snap.cmdState.infoState.trees do
          if let rs@(_ :: _) := t.goalsAt? doc.meta.text hoverPos then
            let goals ← List.join <$> rs.mapM fun { ctxInfo := ci, tacticInfo := ti, useAfter := useAfter } =>
              let ci := if useAfter then { ci with mctx := ti.mctxAfter } else { ci with mctx := ti.mctxBefore }
              let goals := if useAfter then ti.goalsAfter else ti.goalsBefore
              ci.runMetaM {} <| goals.mapM (fun g => Meta.withPPInaccessibleNames (Meta.ppGoal g))
            let md :=
              if goals.isEmpty then
                "no goals"
              else
                let goals := goals.map fun goal => s!"```lean
{goal}
```"
                String.intercalate "\n---\n" goals
            return some { goals := goals.map toString |>.toArray, rendered := md }

        return none

  def hasRange (stx : Syntax) : Bool :=
    stx.getPos?.isSome && stx.getTailPos?.isSome

  def rangeOfSyntax! (text : FileMap) (stx : Syntax) : Range :=
    ⟨text.utf8PosToLspPos <| stx.getPos?.get!,
     text.utf8PosToLspPos <| stx.getTailPos?.get!⟩

  open Elab in
  partial def handlePlainTermGoal (p : PlainTermGoalParams)
    : ServerM (Task (Except IO.Error (Except RequestError (Option PlainTermGoal)))) := do
    let st ← read
    let doc ← st.docRef.get
    let text := doc.meta.text
    let hoverPos := text.lspPosToUtf8Pos p.position
    withWaitFindSnap doc (fun s => s.endPos > hoverPos)
      (notFoundX := pure none) fun snap => do
        for t in snap.cmdState.infoState.trees do
          if let some (ci, Info.ofTermInfo i) := t.termGoalAt? hoverPos then
            let goal ← ci.runMetaM i.lctx <| open Meta in do
              let ty ← instantiateMVars <|<- inferType i.expr
              withPPInaccessibleNames <| Meta.ppGoal (← mkFreshExprMVar ty).mvarId!
            let range := if hasRange i.stx then rangeOfSyntax! text i.stx else ⟨p.position, p.position⟩
            return some { goal := toString goal, range }
        return none

  partial def handleDocumentHighlight (p : DocumentHighlightParams) :
    ServerM (Task (Except IO.Error (Except RequestError (Array DocumentHighlight)))) := do
    let doc ← (← read).docRef.get
    let text := doc.meta.text
    let pos := text.lspPosToUtf8Pos p.position
    let rec highlightReturn? (doRange? : Option Range) : Syntax → Option DocumentHighlight
      | stx@`(doElem|return%$i $e) =>
        if stx.getPos?.get! <= pos && pos < stx.getTailPos?.get! then
          some { range := doRange?.getD (rangeOfSyntax! text i), kind? := DocumentHighlightKind.text }
        else
          highlightReturn? doRange? e
      | `(do%$i $elems) => highlightReturn? (rangeOfSyntax! text i) elems
      | stx => stx.getArgs.findSome? (highlightReturn? doRange?)

    withWaitFindSnap doc (fun s => s.endPos > pos)
      (notFoundX := pure #[]) fun snap => do
        if let some hi := highlightReturn? none snap.stx then
          return #[hi]
        return #[]

  partial def handleDocumentSymbol (p : DocumentSymbolParams) :
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
        | `(namespace $id)  => sectionLikeToDocumentSymbols text stx stxs (id.getId.toString) SymbolKind.namespace id
        | `(section $(id)?) => sectionLikeToDocumentSymbols text stx stxs ((·.getId.toString) <$> id |>.getD "<section>") SymbolKind.namespace (id.getD stx)
        | `(end $(id)?) => ([], stx::stxs)
        | _ =>
          let (syms, stxs') := toDocumentSymbols text stxs
          if stx.isOfKind ``Lean.Parser.Command.declaration && hasRange stx then
            let (name, selection) := match stx with
              | `($dm:declModifiers $ak:attrKind instance $[$np:namedPrio]? $[$id:ident$[.{$ls,*}]?]? $sig:declSig $val) =>
                ((·.getId.toString) <$> id |>.getD s!"instance {sig.reprint.getD ""}", id.getD sig)
              | _ => match stx[1][1] with
                | `(declId|$id:ident$[.{$ls,*}]?) => (id.getId.toString, id)
                | _                               => (stx[1][0].isIdOrAtom?.getD "<unknown>", stx[1][0])
            if hasRange selection then
              (DocumentSymbol.mk {
                name := name
                kind := SymbolKind.method
                range := rangeOfSyntax! text stx
                selectionRange := rangeOfSyntax! text selection
               } :: syms, stxs')
            else
             (syms, stxs')
          else
            (syms, stxs')
      sectionLikeToDocumentSymbols (text : FileMap) (stx : Syntax) (stxs : List Syntax) (name : String) (kind : SymbolKind) (selection : Syntax) :=
          let (syms, stxs') := toDocumentSymbols text stxs
          -- discard `end`
          let (syms', stxs'') := toDocumentSymbols text (stxs'.drop 1)
          let endStx := match stxs' with
            | endStx::_ => endStx
            | []        => (stx::stxs').getLast!
          -- we can assume that commands always have at least one position (see `parseCommand`)
          let range := rangeOfSyntax! text (mkNullNode #[stx, endStx])
          (DocumentSymbol.mk {
            name
            kind
            range
            selectionRange := if hasRange selection then rangeOfSyntax! text selection else range
            children? := syms.toArray
          } :: syms', stxs'')

  def noHighlightKinds : Array SyntaxNodeKind := #[
    -- usually have special highlighting by the client
    ``Lean.Parser.Term.sorry,
    ``Lean.Parser.Term.type,
    ``Lean.Parser.Term.prop,
    -- not really keywords
    `antiquotName,
    ``Lean.Parser.Command.docComment]

  structure SemanticTokensContext where
    beginPos  : String.Pos
    endPos    : String.Pos
    text      : FileMap
    infoState : Elab.InfoState

  structure SemanticTokensState where
    data       : Array Nat
    lastLspPos : Lsp.Position

  partial def handleSemanticTokens (beginPos endPos : String.Pos) :
      ServerM (Task (Except IO.Error (Except RequestError SemanticTokens))) := do
    let st ← read
    let doc ← st.docRef.get
    let text := doc.meta.text
    let t ← doc.cmdSnaps.waitAll (·.beginPos < endPos)
    IO.mapTask (t := t) fun (snaps, _) =>
      StateT.run' (s := { data := #[], lastLspPos := ⟨0, 0⟩ : SemanticTokensState }) do
      for s in snaps do
        if s.endPos <= beginPos then
          continue
        ReaderT.run (r := SemanticTokensContext.mk beginPos endPos text s.cmdState.infoState) <|
          go s.stx
      return Except.ok { data := (← get).data }
  where
    go (stx : Syntax) := do
      match stx with
      | `($e.$id:ident)    => go e; addToken id SemanticTokenType.property
      -- indistinguishable from next pattern
      --| `(level|$id:ident) => addToken id SemanticTokenType.variable
      | `($id:ident)       => highlightId id
      | _ =>
        if !noHighlightKinds.contains stx.getKind then
          highlightKeyword stx
          if stx.isOfKind choiceKind then
            go stx[0]
          else
            stx.getArgs.forM go
    highlightId (stx : Syntax) : ReaderT SemanticTokensContext (StateT SemanticTokensState IO) _ := do
      if let (some pos, some tailPos) := (stx.getPos?, stx.getTailPos?) then
        for t in (← read).infoState.trees do
          for ti in t.deepestNodes (fun
            | _, i@(Elab.Info.ofTermInfo ti), _ => match i.pos? with
              | some ipos => if pos <= ipos && ipos < tailPos then some ti else none
              | _         => none
            | _, _, _ => none) do
            match ti.expr with
            | Expr.fvar .. => addToken ti.stx SemanticTokenType.variable
            | _            => if ti.stx.getPos?.get! > pos then addToken ti.stx SemanticTokenType.property
    highlightKeyword stx := do
      if let Syntax.atom info val := stx then
        if val.bsize > 0 && val[0].isAlpha then
          addToken stx SemanticTokenType.keyword
    addToken stx type := do
      let ⟨beginPos, endPos, text, _⟩ ← read
      if let (some pos, some tailPos) := (stx.getPos?, stx.getTailPos?) then
        if beginPos <= pos && pos < endPos then
          let lspPos := (← get).lastLspPos
          let lspPos' := text.utf8PosToLspPos pos
          let deltaLine := lspPos'.line - lspPos.line
          let deltaStart := lspPos'.character - (if lspPos'.line == lspPos.line then lspPos.character else 0)
          let length := (text.utf8PosToLspPos tailPos).character - lspPos'.character
          let tokenType := type.toNat
          let tokenModifiers := 0
          modify fun st => {
            data := st.data ++ #[deltaLine, deltaStart, length, tokenType, tokenModifiers]
            lastLspPos := lspPos'
          }

  def handleSemanticTokensFull (p : SemanticTokensParams) :
      ServerM (Task (Except IO.Error (Except RequestError SemanticTokens))) := do
    handleSemanticTokens 0 (1 <<< 16)

  def handleSemanticTokensRange (p : SemanticTokensRangeParams) :
      ServerM (Task (Except IO.Error (Except RequestError SemanticTokens))) := do
    let st ← read
    let doc ← st.docRef.get
    let text := doc.meta.text
    let beginPos := text.lspPosToUtf8Pos p.range.start
    let endPos := text.lspPosToUtf8Pos p.range.end
    handleSemanticTokens beginPos endPos

  partial def handleWaitForDiagnostics (p : WaitForDiagnosticsParams)
    : ServerM (Task (Except IO.Error (Except RequestError WaitForDiagnostics))) := do
    let st ← read
    let rec waitLoop : IO EditableDocument := do
      let doc ← st.docRef.get
      if p.version ≤ doc.meta.version then
        return doc
      else
        IO.sleep 50
        waitLoop
    let t ← IO.asTask waitLoop
    let t ← IO.bindTask t fun
      | Except.error e => unreachable!
      | Except.ok doc => do
        let t₁ ← doc.cmdSnaps.waitAll
        return t₁.map fun _ => Except.ok WaitForDiagnostics.mk
    return t.map fun _ => Except.ok <| Except.ok WaitForDiagnostics.mk

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
                      (handler : paramType → RequestM respType) => do
      let st ← read
      let p ← parseParams paramType params
      let t ← handler p
      let t₁ ← (IO.mapTask · t) fun
        | Except.ok (Except.ok resp) =>
          st.hOut.writeLspResponse ⟨id, resp⟩
        | Except.ok (Except.error e) =>
          st.hOut.writeLspResponseError { id := id, code := e.code, message := e.message }
        | Except.error e =>
          st.hOut.writeLspResponseError { id := id, code := ErrorCode.internalError, message := toString e }
      queueRequest id t₁
    match method with
    | "textDocument/waitForDiagnostics"   => handle WaitForDiagnosticsParams WaitForDiagnostics handleWaitForDiagnostics
    | "textDocument/completion"           => handle CompletionParams CompletionList handleCompletion
    | "textDocument/hover"                => handle HoverParams (Option Hover) handleHover
    | "textDocument/declaration"          => handle TextDocumentPositionParams (Array LocationLink) <| handleDefinition (goToType? := false)
    | "textDocument/definition"           => handle TextDocumentPositionParams (Array LocationLink) <| handleDefinition (goToType? := false)
    | "textDocument/typeDefinition"       => handle TextDocumentPositionParams (Array LocationLink) <| handleDefinition (goToType? := true)
    | "textDocument/documentHighlight"    => handle DocumentHighlightParams DocumentHighlightResult handleDocumentHighlight
    | "textDocument/documentSymbol"       => handle DocumentSymbolParams DocumentSymbolResult handleDocumentSymbol
    | "textDocument/semanticTokens/full"  => handle SemanticTokensParams SemanticTokens handleSemanticTokensFull
    | "textDocument/semanticTokens/range" => handle SemanticTokensRangeParams SemanticTokens handleSemanticTokensRange
    | "$/lean/plainGoal"                  => handle PlainGoalParams (Option PlainGoal) handlePlainGoal
    | "$/lean/plainTermGoal"              => handle PlainTermGoalParams (Option PlainTermGoal) handlePlainTermGoal
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
  let doc := param.textDocument
  let meta : DocumentMeta := ⟨doc.uri, doc.version, doc.text.toFileMap⟩
  let e ← e.withPrefix s!"[{param.textDocument.uri}] "
  let _ ← IO.setStderr e
  try
    let ctx ← initializeWorker meta i o e
    ReaderT.run (r := ctx) mainLoop
    return 0
  catch e =>
    IO.eprintln e
    publishDiagnostics meta #[{ range := ⟨⟨0, 0⟩, ⟨0, 0⟩⟩, severity? := DiagnosticSeverity.error, message := e.toString }] o
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
    return (1 : UInt32)

end Lean.Server.FileWorker
