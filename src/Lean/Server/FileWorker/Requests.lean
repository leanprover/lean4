/-
Copyright (c) 2021 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Wojciech Nawrocki, Marc Huisinga
-/
import Lean.DeclarationRange

import Lean.Data.Json
import Lean.Data.Lsp

import Lean.Server.Completion
import Lean.Server.FileWorker.Utils

/-!  Request handlers are implemented as asynchronously executing `Task`s. They may be cancelled at any time,
so they should check the cancellation token when possible to handle this cooperatively. Any exceptions
thrown in a request handler will be reported to the client as LSP error responses.

We maintain a global map of request handlers. This allows user code such as plugins to register its own
handlers, for example to support ITP functionality such as goal state visualization. -/

namespace Lean.Server.FileWorker.Requests

structure RequestError where
  code    : JsonRpc.ErrorCode
  message : String

namespace RequestError
open JsonRpc

def fileChanged : RequestError :=
  { code := ErrorCode.contentModified
    message := "File changed." }

def methodNotFound (method : String) : RequestError :=
  { code := ErrorCode.methodNotFound
    message := s!"No request handler found for '${method}'" }

instance : Coe IO.Error RequestError where
  coe e := { code := ErrorCode.internalError
             message := toString e }

def toLspResponseError (id : RequestID) (e : RequestError) : ResponseError Unit :=
  { id := id
    code := e.code
    message := e.message }

end RequestError

structure RequestContext where
  srcSearchPath : SearchPath
  docRef        : IO.Ref EditableDocument

abbrev RequestTask α := Task (Except RequestError α)
/-- Request handlers execute in this monad. -/
abbrev RequestM := ReaderT RequestContext <| ExceptT RequestError IO

/- The global request handlers table. -/
section HandlerTable
/- NOTE(WN): maybe it would be neater to store
```lean
  paramType : Type
  paramFromJson : FromJson paramType
  respType : Type
  respToJson : ToJson respType
```
here but this is a `Type 1`, requiring `EStateM/ST/IO` to be universe-polymorphic. -/
private structure RequestHandler where
  handle : Json → RequestM (RequestTask Json)

builtin_initialize requestHandlers : IO.Ref (Std.PersistentHashMap String RequestHandler) ←
  IO.mkRef {}

private def parseParams (paramType : Type) [FromJson paramType] (params : Json) : RequestM paramType :=
  match fromJson? params with
  | Except.ok parsed => return parsed
  | Except.error inner => throwThe RequestError {
    code := JsonRpc.ErrorCode.parseError
    message := s!"Cannot parse request params: {params.compress}\n{inner}"
  }

def registerLspRequestHandler (method : String)
    paramType [FromJson paramType]
    respType [ToJson respType]
    (handler : paramType → RequestM (RequestTask respType)) : IO Unit := do
  unless (← IO.initializing) do
    throw <| IO.userError s!"Failed to register LSP request handler for '{method}': only possible during initialization"
  if (←requestHandlers.get).contains method then
    throw <| IO.userError s!"Failed to register LSP request handler for '{method}': already registered"
  let handle := fun j => do
    let params ← parseParams paramType j
    let t ← handler params
    t.map <| Except.map ToJson.toJson
  requestHandlers.modify fun rhs => rhs.insert method { handle }

private def lookupLspRequestHandler (method : String) : IO (Option RequestHandler) := do
  (← requestHandlers.get).find? method

def handleLspRequest (method : String) (params : Json) : RequestM (RequestTask Json) := do
  match (← lookupLspRequestHandler method) with
  | none => throw <| RequestError.methodNotFound method
  | some rh => rh.handle params
end HandlerTable

open Snapshots

namespace RequestM
  def readDoc : RequestM EditableDocument := fun rc => rc.docRef.get

  def asTask (t : RequestM α) : RequestM (RequestTask α) := fun rc => do
    let t ← IO.asTask <| t rc
    return t.map fun
      | Except.error e => throwThe RequestError e
      | Except.ok v    => v

  def mapTask (t : Task α) (f : α → RequestM β) : RequestM (RequestTask β) := fun rc => do
    let t ← (IO.mapTask · t) fun a => f a rc
    return t.map fun
      | Except.error e => throwThe RequestError e
      | Except.ok v    => v

  def bindTask (t : Task α) (f : α → RequestM (RequestTask β)) : RequestM (RequestTask β) := fun rc => do
    let t ← IO.bindTask t fun a => do
      match ← f a rc with
      | Except.error e => return Task.pure <| Except.ok <| Except.error e
      | Except.ok t    => return t.map Except.ok
    return t.map fun
      | Except.error e => throwThe RequestError e
      | Except.ok v    => v

  /-- Create a task which waits for a snapshot matching `p`, handles various errors,
  and if a matching snapshot was found executes `x` with it. If not found, the task
  executes `notFoundX`. -/
  def withWaitFindSnap (doc : EditableDocument) (p : Snapshot → Bool)
    (notFoundX : RequestM β)
    (x : Snapshot → RequestM β)
    : RequestM (RequestTask β) := do
    let findTask ← doc.cmdSnaps.waitFind? p
    mapTask findTask fun
      /- The elaboration task that we're waiting for may be aborted if the file contents change.
      In that case, we reply with the `fileChanged` error. Thanks to this, the server doesn't
      get bogged down in requests for an old state of the document. -/
      | Except.error ElabTaskError.aborted =>
        throwThe RequestError RequestError.fileChanged
      | Except.error (ElabTaskError.ioError e) =>
        throwThe IO.Error e
      | Except.error ElabTaskError.eof => notFoundX
      | Except.ok none => notFoundX
      | Except.ok (some snap) => x snap
end RequestM

open RequestM
open Lsp

partial def handleCompletion (p : CompletionParams)
    : RequestM (RequestTask CompletionList) := do
  let doc ← readDoc
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
    : RequestM (RequestTask (Option Hover)) := do
  let doc ← readDoc
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
    : RequestM (RequestTask (Array LocationLink)) := do
  let rc ← read
  let doc ← readDoc
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
                let modFname? ← rc.srcSearchPath.findWithExt "lean" modName
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
    : RequestM (RequestTask (Option PlainGoal)) := do
  let doc ← readDoc
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
    : RequestM (RequestTask (Option PlainTermGoal)) := do
  let doc ← readDoc
  let text := doc.meta.text
  let hoverPos := text.lspPosToUtf8Pos p.position
  withWaitFindSnap doc (fun s => s.endPos > hoverPos)
    (notFoundX := pure none) fun snap => do
      for t in snap.cmdState.infoState.trees do
        if let some (ci, Info.ofTermInfo i) := t.termGoalAt? hoverPos then
          let goal ← ci.runMetaM i.lctx <| open Meta in do
            let ty ← instantiateMVars <| i.expectedType?.getD (← inferType i.expr)
            withPPInaccessibleNames <| Meta.ppGoal (← mkFreshExprMVar ty).mvarId!
          let range := if hasRange i.stx then rangeOfSyntax! text i.stx else ⟨p.position, p.position⟩
          return some { goal := toString goal, range }
      return none

partial def handleDocumentHighlight (p : DocumentHighlightParams)
    : RequestM (RequestTask (Array DocumentHighlight)) := do
  let doc ← readDoc
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

section -- TODO https://github.com/leanprover/lean4/issues/529
open Parser.Command
partial def handleDocumentSymbol (p : DocumentSymbolParams)
    : RequestM (RequestTask DocumentSymbolResult) := do
  let doc ← readDoc
  asTask do
    let ⟨cmdSnaps, e?⟩ ← doc.cmdSnaps.updateFinishedPrefix
    let mut stxs := cmdSnaps.finishedPrefix.map Snapshot.stx
    match e? with
    | some ElabTaskError.aborted =>
      throw RequestError.fileChanged
    | some (ElabTaskError.ioError e) =>
      throwThe IO.Error e
    | _ => ()

    let lastSnap := cmdSnaps.finishedPrefix.getLastD doc.headerSnap
    stxs := stxs ++ (← parseAhead doc.meta.text.source lastSnap).toList
    let (syms, _) := toDocumentSymbols doc.meta.text stxs
    return { syms := syms.toArray }
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
end

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

partial def handleSemanticTokens (beginPos endPos : String.Pos)
    : RequestM (RequestTask SemanticTokens) := do
  let doc ← readDoc
  let text := doc.meta.text
  let t ← doc.cmdSnaps.waitAll (·.beginPos < endPos)
  mapTask t fun (snaps, _) =>
    StateT.run' (s := { data := #[], lastLspPos := ⟨0, 0⟩ : SemanticTokensState }) do
      for s in snaps do
        if s.endPos <= beginPos then
          continue
        ReaderT.run (r := SemanticTokensContext.mk beginPos endPos text s.cmdState.infoState) <|
          go s.stx
      return { data := (← get).data }
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
  highlightId (stx : Syntax) : ReaderT SemanticTokensContext (StateT SemanticTokensState RequestM) _ := do
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

def handleSemanticTokensFull (p : SemanticTokensParams)
    : RequestM (RequestTask SemanticTokens) := do
  handleSemanticTokens 0 (1 <<< 16)

def handleSemanticTokensRange (p : SemanticTokensRangeParams)
    : RequestM (RequestTask SemanticTokens) := do
  let doc ← readDoc
  let text := doc.meta.text
  let beginPos := text.lspPosToUtf8Pos p.range.start
  let endPos := text.lspPosToUtf8Pos p.range.end
  handleSemanticTokens beginPos endPos

partial def handleWaitForDiagnostics (p : WaitForDiagnosticsParams)
    : RequestM (RequestTask WaitForDiagnostics) := do
  let rec waitLoop : RequestM EditableDocument := do
    let doc ← readDoc
    if p.version ≤ doc.meta.version then
      return doc
    else
      IO.sleep 50
      waitLoop
  let t ← RequestM.asTask waitLoop
  RequestM.bindTask t fun doc? => do
    let doc ← doc?
    let t₁ ← doc.cmdSnaps.waitAll
    return t₁.map fun _ => pure WaitForDiagnostics.mk

builtin_initialize
  registerLspRequestHandler "textDocument/waitForDiagnostics"   WaitForDiagnosticsParams   WaitForDiagnostics      handleWaitForDiagnostics
  registerLspRequestHandler "textDocument/completion"           CompletionParams           CompletionList          handleCompletion
  registerLspRequestHandler "textDocument/hover"                HoverParams                (Option Hover)          handleHover
  registerLspRequestHandler "textDocument/declaration"          TextDocumentPositionParams (Array LocationLink)    (handleDefinition (goToType? := false))
  registerLspRequestHandler "textDocument/definition"           TextDocumentPositionParams (Array LocationLink)    (handleDefinition (goToType? := false))
  registerLspRequestHandler "textDocument/typeDefinition"       TextDocumentPositionParams (Array LocationLink)    (handleDefinition (goToType? := true))
  registerLspRequestHandler "textDocument/documentHighlight"    DocumentHighlightParams    DocumentHighlightResult handleDocumentHighlight
  registerLspRequestHandler "textDocument/documentSymbol"       DocumentSymbolParams       DocumentSymbolResult    handleDocumentSymbol
  registerLspRequestHandler "textDocument/semanticTokens/full"  SemanticTokensParams       SemanticTokens          handleSemanticTokensFull
  registerLspRequestHandler "textDocument/semanticTokens/range" SemanticTokensRangeParams  SemanticTokens          handleSemanticTokensRange
  registerLspRequestHandler "$/lean/plainGoal"                  PlainGoalParams            (Option PlainGoal)      handlePlainGoal
  registerLspRequestHandler "$/lean/plainTermGoal"              PlainTermGoalParams        (Option PlainTermGoal)  handlePlainTermGoal
end Lean.Server.FileWorker.Requests