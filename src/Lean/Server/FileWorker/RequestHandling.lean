/-
Copyright (c) 2021 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Wojciech Nawrocki, Marc Huisinga
-/
import Lean.DeclarationRange

import Lean.Data.Json
import Lean.Data.Lsp

import Lean.Server.FileWorker.Utils
import Lean.Server.Requests
import Lean.Server.Completion
import Lean.Server.References
import Lean.Server.GoTo

import Lean.Widget.InteractiveGoal

namespace Lean.Server.FileWorker
open Lsp
open RequestM
open Snapshots

def handleCompletion (p : CompletionParams)
    : RequestM (RequestTask CompletionList) := do
  let doc ← readDoc
  let text := doc.meta.text
  let pos := text.lspPosToUtf8Pos p.position
  let caps := (← read).initParams.capabilities
  -- dbg_trace ">> handleCompletion invoked {pos}"
  -- NOTE: use `+ 1` since we sometimes want to consider invalid input technically after the command,
  -- such as a trailing dot after an option name. This shouldn't be a problem since any subsequent
  -- command starts with a keyword that (currently?) does not participate in completion.
  withWaitFindSnap doc (·.endPos + ' ' >= pos)
    (notFoundX := pure { items := #[], isIncomplete := true }) fun snap => do
      if let some r ← Completion.find? doc.meta.text pos snap.infoTree caps then
        return r
      return { items := #[ ], isIncomplete := true }

open Elab in
def handleHover (p : HoverParams)
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
      if let some (ci, i) := snap.infoTree.hoverableInfoAt? hoverPos then
        if let some hoverFmt ← i.fmtHover? ci then
          return some <| mkHover (toString hoverFmt) i.pos?.get! i.tailPos?.get!

      return none

open Elab GoToKind in
def locationLinksOfInfo (kind : GoToKind) (ci : Elab.ContextInfo) (i : Elab.Info)
    (infoTree? : Option InfoTree := none) : RequestM (Array LocationLink) := do
  let rc ← read
  let doc ← readDoc
  let text := doc.meta.text

  let locationLinksFromDecl (i : Elab.Info) (n : Name) :=
    locationLinksFromDecl rc.srcSearchPath.get doc.meta.uri n <| (·.toLspRange text) <$> i.range?

  let locationLinksFromBinder (i : Elab.Info) (id : FVarId) := do
    if let some i' := infoTree? >>= InfoTree.findInfo? fun
        | Info.ofTermInfo { isBinder := true, expr := Expr.fvar id' .., .. } => id' == id
        | _ => false then
      if let some r := i'.range? then
        let r := r.toLspRange text
        let ll : LocationLink := {
          originSelectionRange? := (·.toLspRange text) <$> i.range?
          targetUri := doc.meta.uri
          targetRange := r
          targetSelectionRange := r
        }
        return #[ll]
    return #[]

  let locationLinksFromImport (i : Elab.Info) := do
    let name := i.stx[2].getId
    if let some modUri ← documentUriFromModule rc.srcSearchPath.get name then
      let range := { start := ⟨0, 0⟩, «end» := ⟨0, 0⟩ : Range }
      let ll : LocationLink := {
        originSelectionRange? := (·.toLspRange text) <$> i.stx[2].getRange? (originalOnly := true)
        targetUri := modUri
        targetRange := range
        targetSelectionRange := range
      }
      return #[ll]
    return #[]

  if let Info.ofTermInfo ti := i then
    let mut expr := ti.expr
    if kind == type then
      expr ← ci.runMetaM i.lctx do
        return Expr.getAppFn (← Meta.instantiateMVars (← Meta.inferType expr))
    match expr with
    | Expr.const n .. => return ← ci.runMetaM i.lctx <| locationLinksFromDecl i n
    | Expr.fvar id .. => return ← ci.runMetaM i.lctx <| locationLinksFromBinder i id
    | _ => pure ()
  if let Info.ofFieldInfo fi := i then
    if kind == type then
      let expr ← ci.runMetaM i.lctx do
        Meta.instantiateMVars (← Meta.inferType fi.val)
      if let some n := expr.getAppFn.constName? then
        return ← ci.runMetaM i.lctx <| locationLinksFromDecl i n
    else
      return ← ci.runMetaM i.lctx <| locationLinksFromDecl i fi.projName
  if let Info.ofCommandInfo ⟨`import, _⟩ := i then
    if kind == definition || kind == declaration then
      return ← ci.runMetaM i.lctx <| locationLinksFromImport i
  -- If other go-tos fail, we try to show the elaborator or parser
  if let some ei := i.toElabInfo? then
    if kind == declaration && ci.env.contains ei.stx.getKind then
      return ← ci.runMetaM i.lctx <| locationLinksFromDecl i ei.stx.getKind
    if kind == definition && ci.env.contains ei.elaborator then
      return ← ci.runMetaM i.lctx <| locationLinksFromDecl i ei.elaborator
  return #[]

open Elab GoToKind in
def handleDefinition (kind : GoToKind) (p : TextDocumentPositionParams)
    : RequestM (RequestTask (Array LocationLink)) := do
  let doc ← readDoc
  let text := doc.meta.text
  let hoverPos := text.lspPosToUtf8Pos p.position

  withWaitFindSnap doc (fun s => s.endPos > hoverPos)
    (notFoundX := pure #[]) fun snap => do
      if let some (ci, i) := snap.infoTree.hoverableInfoAt? (includeStop := true /- #767 -/) hoverPos then
        locationLinksOfInfo kind ci i snap.infoTree
      else return #[]

open RequestM in
def getInteractiveGoals (p : Lsp.PlainGoalParams) : RequestM (RequestTask (Option Widget.InteractiveGoals)) := do
  let doc ← readDoc
  let text := doc.meta.text
  let hoverPos := text.lspPosToUtf8Pos p.position
  -- NOTE: use `>=` since the cursor can be *after* the input
  withWaitFindSnap doc (fun s => s.endPos >= hoverPos)
    (notFoundX := return none) fun snap => do
      if let rs@(_ :: _) := snap.infoTree.goalsAt? doc.meta.text hoverPos then
        let goals ← List.join <$> rs.mapM fun { ctxInfo := ci, tacticInfo := ti, useAfter := useAfter, .. } =>
          let ci := if useAfter then { ci with mctx := ti.mctxAfter } else { ci with mctx := ti.mctxBefore }
          let goals := if useAfter then ti.goalsAfter else ti.goalsBefore
          ci.runMetaM {} <| goals.mapM (fun g => Meta.withPPInaccessibleNames (Widget.goalToInteractive g))
        return some { goals := goals.toArray }
      else
        return none

open Elab in
def handlePlainGoal (p : PlainGoalParams)
    : RequestM (RequestTask (Option PlainGoal)) := do
  let t ← getInteractiveGoals p
  return t.map <| Except.map <| Option.map <| fun ⟨goals⟩ =>
    if goals.isEmpty then
      { goals := #[], rendered := "no goals" }
    else
      let goalStrs := goals.map (toString ·.pretty)
      let goalBlocks := goalStrs.map fun goal => s!"```lean
{goal}
```"
      let md := String.intercalate "\n---\n" goalBlocks.toList
      { goals := goalStrs, rendered := md }

def getInteractiveTermGoal (p : Lsp.PlainTermGoalParams)
    : RequestM (RequestTask (Option Widget.InteractiveTermGoal)) := do
  let doc ← readDoc
  let text := doc.meta.text
  let hoverPos := text.lspPosToUtf8Pos p.position
  withWaitFindSnap doc (fun s => s.endPos > hoverPos)
    (notFoundX := pure none) fun snap => do
      if let some (ci, i@(Elab.Info.ofTermInfo ti)) := snap.infoTree.termGoalAt? hoverPos then
        let ty ← ci.runMetaM i.lctx do
          Meta.instantiateMVars <| ti.expectedType?.getD (← Meta.inferType ti.expr)
        -- for binders, hide the last hypothesis (the binder itself)
        let lctx' := if ti.isBinder then i.lctx.pop else i.lctx
        let goal ← ci.runMetaM lctx' do
          Widget.goalToInteractive (← Meta.mkFreshExprMVar ty).mvarId!
        let range := if let some r := i.range? then r.toLspRange text else ⟨p.position, p.position⟩
        return some { goal with range }
      else
        return none

def handlePlainTermGoal (p : PlainTermGoalParams)
    : RequestM (RequestTask (Option PlainTermGoal)) := do
  let t ← getInteractiveTermGoal p
  return t.map <| Except.map <| Option.map fun goal =>
    { goal := toString goal.toInteractiveGoal.pretty
      range := goal.range
    }

partial def handleDocumentHighlight (p : DocumentHighlightParams)
    : RequestM (RequestTask (Array DocumentHighlight)) := do
  let doc ← readDoc
  let text := doc.meta.text
  let pos := text.lspPosToUtf8Pos p.position

  let rec highlightReturn? (doRange? : Option Range) : Syntax → Option DocumentHighlight
    | `(doElem|return%$i $e) => Id.run do
      if let some range := i.getRange? then
        if range.contains pos then
          return some { range := doRange?.getD (range.toLspRange text), kind? := DocumentHighlightKind.text }
      highlightReturn? doRange? e
    | `(do%$i $elems) => highlightReturn? (i.getRange?.get!.toLspRange text) elems
    | stx => stx.getArgs.findSome? (highlightReturn? doRange?)

  let highlightRefs? (snaps : Array Snapshot) : Option (Array DocumentHighlight) := Id.run do
    let trees := snaps.map (·.infoTree)
    let refs : Lsp.ModuleRefs := findModuleRefs text trees
    let mut ranges := #[]
    for ident in ← refs.findAt p.position do
      if let some info ← refs.find? ident then
        if let some definition := info.definition then
          ranges := ranges.push definition
        ranges := ranges.append info.usages
    if ranges.isEmpty then
      return none
    some <| ranges.map ({ range := ·, kind? := DocumentHighlightKind.text })

  withWaitFindSnap doc (fun s => s.endPos > pos)
    (notFoundX := pure #[]) fun snap => do
      let (snaps, _) ← doc.cmdSnaps.updateFinishedPrefix
      if let some his := highlightRefs? snaps.finishedPrefix.toArray then
        return his
      if let some hi := highlightReturn? none snap.stx then
        return #[hi]
      return #[]

open Parser.Command in
partial def handleDocumentSymbol (_ : DocumentSymbolParams)
    : RequestM (RequestTask DocumentSymbolResult) := do
  let doc ← readDoc
  asTask do
    let ⟨cmdSnaps, e?⟩ ← doc.cmdSnaps.updateFinishedPrefix
    let mut stxs := cmdSnaps.finishedPrefix.map (·.stx)
    match e? with
    | some ElabTaskError.aborted =>
      throw RequestError.fileChanged
    | some (ElabTaskError.ioError e) =>
      throw (e : RequestError)
    | _ => pure ()

    let lastSnap := cmdSnaps.finishedPrefix.getLast!
    stxs := stxs ++ (← parseAhead doc.meta.mkInputContext lastSnap).toList
    let (syms, _) := toDocumentSymbols doc.meta.text stxs
    return { syms := syms.toArray }
  where
    toDocumentSymbols (text : FileMap)
    | [] => ([], [])
    | stx::stxs => match stx with
      | `(namespace $id)  => sectionLikeToDocumentSymbols text stx stxs (id.getId.toString) SymbolKind.namespace id
      | `(section $(id)?) => sectionLikeToDocumentSymbols text stx stxs ((·.getId.toString) <$> id |>.getD "<section>") SymbolKind.namespace (id.getD stx)
      | `(end $(_id)?) => ([], stx::stxs)
      | _ => Id.run do
        let (syms, stxs') := toDocumentSymbols text stxs
        unless stx.isOfKind ``Lean.Parser.Command.declaration do
          return (syms, stxs')
        if let some stxRange := stx.getRange? then
          let (name, selection) := match stx with
            | `($_:declModifiers $_:attrKind instance $[$np:namedPrio]? $[$id:ident$[.{$ls,*}]?]? $sig:declSig $_) =>
              ((·.getId.toString) <$> id |>.getD s!"instance {sig.reprint.getD ""}", id.getD sig)
            | _ => match stx[1][1] with
              | `(declId|$id:ident$[.{$ls,*}]?) => (id.getId.toString, id)
              | _                               => (stx[1][0].isIdOrAtom?.getD "<unknown>", stx[1][0])
          if let some selRange := selection.getRange? then
            return (DocumentSymbol.mk {
              name := name
              kind := SymbolKind.method
              range := stxRange.toLspRange text
              selectionRange := selRange.toLspRange text
              } :: syms, stxs')
        return (syms, stxs')
    sectionLikeToDocumentSymbols (text : FileMap) (stx : Syntax) (stxs : List Syntax) (name : String) (kind : SymbolKind) (selection : Syntax) :=
        let (syms, stxs') := toDocumentSymbols text stxs
        -- discard `end`
        let (syms', stxs'') := toDocumentSymbols text (stxs'.drop 1)
        let endStx := match stxs' with
          | endStx::_ => endStx
          | []        => (stx::stxs').getLast!
        -- we can assume that commands always have at least one position (see `parseCommand`)
        let range := (mkNullNode #[stx, endStx]).getRange?.get!.toLspRange text
        (DocumentSymbol.mk {
          name
          kind
          range
          selectionRange := selection.getRange? |>.map (·.toLspRange text) |>.getD range
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
  snap      : Snapshot

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
        ReaderT.run (r := SemanticTokensContext.mk beginPos endPos text s) <|
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
    if let some range := stx.getRange? then
      let mut lastPos := range.start
      for ti in (← read).snap.infoTree.deepestNodes (fun
        | _, i@(Elab.Info.ofTermInfo ti), _ => match i.pos? with
          | some ipos => if range.contains ipos then some ti else none
          | _         => none
        | _, _, _ => none) do
        let pos := ti.stx.getPos?.get!
        -- avoid reporting same position twice; the info node can occur multiple times if
        -- e.g. the term is elaborated multiple times
        if pos < lastPos then
          continue
        if let Expr.fvar fvarId .. := ti.expr then
          if let some localDecl := ti.lctx.find? fvarId then
            -- Recall that `isAuxDecl` is an auxiliary declaration used to elaborate a recursive definition.
            if localDecl.isAuxDecl then
              if ti.isBinder then
                addToken ti.stx SemanticTokenType.function
            else
              addToken ti.stx SemanticTokenType.variable
        else if ti.stx.getPos?.get! > lastPos then
          -- any info after the start position: must be projection notation
          addToken ti.stx SemanticTokenType.property
          lastPos := ti.stx.getPos?.get!
  highlightKeyword stx := do
    if let Syntax.atom _ val := stx then
      if (val.length > 0 && val[0].isAlpha) ||
         -- Support for keywords of the form `#<alpha>...`
         (val.length > 1 && val[0] == '#' && val[⟨1⟩].isAlpha) then
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

def handleSemanticTokensFull (_ : SemanticTokensParams)
    : RequestM (RequestTask SemanticTokens) := do
  handleSemanticTokens 0 ⟨1 <<< 16⟩

def handleSemanticTokensRange (p : SemanticTokensRangeParams)
    : RequestM (RequestTask SemanticTokens) := do
  let doc ← readDoc
  let text := doc.meta.text
  let beginPos := text.lspPosToUtf8Pos p.range.start
  let endPos := text.lspPosToUtf8Pos p.range.end
  handleSemanticTokens beginPos endPos

partial def handleFoldingRange (_ : FoldingRangeParams)
  : RequestM (RequestTask (Array FoldingRange)) := do
  let doc ← readDoc
  let t ← doc.cmdSnaps.waitAll
  mapTask t fun (snaps, _) => do
    let stxs := snaps.map (·.stx)
    let (_, ranges) ← StateT.run (addRanges doc.meta.text [] stxs) #[]
    return ranges
  where
    isImport stx := stx.isOfKind ``Lean.Parser.Module.header || stx.isOfKind ``Lean.Parser.Command.open

    addRanges (text : FileMap) sections
    | [] => return
    | stx::stxs => match stx with
      | `(namespace $_id)  => addRanges text (stx.getPos?::sections) stxs
      | `(section $(_id)?) => addRanges text (stx.getPos?::sections) stxs
      | `(end $(_id)?) => do
        if let start::rest := sections then
          addRange text FoldingRangeKind.region start stx.getTailPos?
          addRanges text rest stxs
        else
          addRanges text sections stxs
      | `(mutual $body* end) => do
        addRangeFromSyntax text FoldingRangeKind.region stx
        addRanges text [] body.toList
        addRanges text sections stxs
      | _ => do
        if isImport stx then
          let (imports, stxs) := stxs.span isImport
          let last := imports.getLastD stx
          addRange text FoldingRangeKind.imports stx.getPos? last.getTailPos?
          addRanges text sections stxs
        else
          addCommandRange text stx
          addRanges text sections stxs

    addCommandRange text stx :=
      match stx.getKind with
      | `Lean.Parser.Command.moduleDoc =>
        addRangeFromSyntax text FoldingRangeKind.comment stx
      | ``Lean.Parser.Command.declaration => do
        -- When visiting a declaration, attempt to fold the doc comment
        -- separately to the main definition.
        -- We never fold other modifiers, such as annotations.
        if let `($dm:declModifiers $decl) := stx then
          if let some comment := dm[0].getOptional? then
            addRangeFromSyntax text FoldingRangeKind.comment comment

          addRangeFromSyntax text FoldingRangeKind.region decl
        else
          addRangeFromSyntax text FoldingRangeKind.region stx
      | _ =>
        addRangeFromSyntax text FoldingRangeKind.region stx

    addRangeFromSyntax (text : FileMap) kind stx := addRange text kind stx.getPos? stx.getTailPos?

    addRange (text : FileMap) kind start? stop? := do
      if let (some startP, some endP) := (start?, stop?) then
        let startP := text.utf8PosToLspPos startP
        let endP := text.utf8PosToLspPos endP
        if startP.line != endP.line then
          modify fun st => st.push
            { startLine := startP.line
              endLine := endP.line
              kind? := some kind }

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
    let doc ← liftExcept doc?
    let t₁ ← doc.cmdSnaps.waitAll
    return t₁.map fun _ => pure WaitForDiagnostics.mk

builtin_initialize
  registerLspRequestHandler "textDocument/waitForDiagnostics"   WaitForDiagnosticsParams   WaitForDiagnostics      handleWaitForDiagnostics
  registerLspRequestHandler "textDocument/completion"           CompletionParams           CompletionList          handleCompletion
  registerLspRequestHandler "textDocument/hover"                HoverParams                (Option Hover)          handleHover
  registerLspRequestHandler "textDocument/declaration"          TextDocumentPositionParams (Array LocationLink)    (handleDefinition GoToKind.declaration)
  registerLspRequestHandler "textDocument/definition"           TextDocumentPositionParams (Array LocationLink)    (handleDefinition GoToKind.definition)
  registerLspRequestHandler "textDocument/typeDefinition"       TextDocumentPositionParams (Array LocationLink)    (handleDefinition GoToKind.type)
  registerLspRequestHandler "textDocument/documentHighlight"    DocumentHighlightParams    DocumentHighlightResult handleDocumentHighlight
  registerLspRequestHandler "textDocument/documentSymbol"       DocumentSymbolParams       DocumentSymbolResult    handleDocumentSymbol
  registerLspRequestHandler "textDocument/semanticTokens/full"  SemanticTokensParams       SemanticTokens          handleSemanticTokensFull
  registerLspRequestHandler "textDocument/semanticTokens/range" SemanticTokensRangeParams  SemanticTokens          handleSemanticTokensRange
  registerLspRequestHandler "textDocument/foldingRange"         FoldingRangeParams         (Array FoldingRange)    handleFoldingRange
  registerLspRequestHandler "$/lean/plainGoal"                  PlainGoalParams            (Option PlainGoal)      handlePlainGoal
  registerLspRequestHandler "$/lean/plainTermGoal"              PlainTermGoalParams        (Option PlainTermGoal)  handlePlainTermGoal

end Lean.Server.FileWorker
