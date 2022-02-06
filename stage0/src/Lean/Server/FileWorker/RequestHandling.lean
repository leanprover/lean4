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

import Lean.Widget.InteractiveGoal

namespace Lean.Server.FileWorker
open Lsp
open RequestM
open Snapshots

partial def handleCompletion (p : CompletionParams)
    : RequestM (RequestTask CompletionList) := do
  let doc ← readDoc
  let text := doc.meta.text
  let pos := text.lspPosToUtf8Pos p.position
  let caps := (← read).initParams.capabilities
  -- dbg_trace ">> handleCompletion invoked {pos}"
  -- NOTE: use `+ 1` since we sometimes want to consider invalid input technically after the command,
  -- such as a trailing dot after an option name. This shouldn't be a problem since any subsequent
  -- command starts with a keyword that (currently?) does not participate in completion.
  withWaitFindSnap doc (·.endPos + 1 >= pos)
    (notFoundX := pure { items := #[], isIncomplete := true }) fun snap => do
      if let some r ← Completion.find? doc.meta.text pos snap.infoTree caps then
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
      if let some (ci, i) := snap.infoTree.hoverableInfoAt? hoverPos then
        if let some hoverFmt ← i.fmtHover? ci then
          return some <| mkHover (toString hoverFmt) i.pos?.get! i.tailPos?.get!

      return none

inductive GoToKind
  | declaration | definition | type
  deriving BEq

open Elab GoToKind in
partial def handleDefinition (kind : GoToKind) (p : TextDocumentPositionParams)
    : RequestM (RequestTask (Array LocationLink)) := do
  let rc ← read
  let doc ← readDoc
  let text := doc.meta.text
  let hoverPos := text.lspPosToUtf8Pos p.position

  let documentUriFromModule (modName : Name) : MetaM (Option DocumentUri) := do
    let some modFname ← rc.srcSearchPath.findWithExt "lean" modName
      | pure none
    -- resolve symlinks (such as `src` in the build dir) so that files are opened
    -- in the right folder
    let modFname ← IO.FS.realPath modFname
    pure <| some <| Lsp.DocumentUri.ofPath modFname

  let locationLinksFromDecl (i : Elab.Info) (n : Name) := do
    let mod? ← findModuleOf? n
    let modUri? ← match mod? with
      | some modName => documentUriFromModule modName
      | none         => pure <| some doc.meta.uri

    let ranges? ← findDeclarationRanges? n
    if let (some ranges, some modUri) := (ranges?, modUri?) then
      let declRangeToLspRange (r : DeclarationRange) : Lsp.Range :=
        { start := ⟨r.pos.line - 1, r.charUtf16⟩
          «end» := ⟨r.endPos.line - 1, r.endCharUtf16⟩ }
      let ll : LocationLink := {
        originSelectionRange? := (·.toLspRange text) <$> i.range?
        targetUri := modUri
        targetRange := declRangeToLspRange ranges.range
        targetSelectionRange := declRangeToLspRange ranges.selectionRange
      }
      return #[ll]
    return #[]

  let locationLinksFromBinder (t : InfoTree) (i : Elab.Info) (id : FVarId) := do
    if let some i' := t.findInfo? fun
        | Info.ofTermInfo { isBinder := true, expr := Expr.fvar id' .., .. } => id' == id
        | _ => false then
      if let some r := i'.range? then
        let r := r.toLspRange text
        let ll : LocationLink := {
          originSelectionRange? := (·.toLspRange text) <$> i.range?
          targetUri := p.textDocument.uri
          targetRange := r
          targetSelectionRange := r
        }
        return #[ll]
    return #[]

  let locationLinksFromImport (i : Elab.Info) := do
    let name := i.stx[2].getId
    if let some modUri ← documentUriFromModule name then
      let range := { start := ⟨0, 0⟩, «end» := ⟨0, 0⟩ : Range }
      let ll : LocationLink := {
        originSelectionRange? := none
        targetUri := modUri
        targetRange := range
        targetSelectionRange := range
      }
      return #[ll]
    return #[]

  withWaitFindSnap doc (fun s => s.endPos > hoverPos)
    (notFoundX := pure #[]) fun snap => do
      if let some (ci, i) := snap.infoTree.hoverableInfoAt? hoverPos then
        if let Info.ofTermInfo ti := i then
          let mut expr := ti.expr
          if kind == type then
            expr ← ci.runMetaM i.lctx do
              return Expr.getAppFn (← Meta.instantiateMVars (← Meta.inferType expr))
          match expr with
          | Expr.const n .. => return ← ci.runMetaM i.lctx <| locationLinksFromDecl i n
          | Expr.fvar id .. => return ← ci.runMetaM i.lctx <| locationLinksFromBinder snap.infoTree i id
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

open RequestM in
def getInteractiveGoals (p : Lsp.PlainGoalParams) : RequestM (RequestTask (Option Widget.InteractiveGoals)) := do
  let doc ← readDoc
  let text := doc.meta.text
  let hoverPos := text.lspPosToUtf8Pos p.position
  -- NOTE: use `>=` since the cursor can be *after* the input
  withWaitFindSnap doc (fun s => s.endPos >= hoverPos)
    (notFoundX := return none) fun snap => do
      if let rs@(_ :: _) := snap.infoTree.goalsAt? doc.meta.text hoverPos then
        let goals ← List.join <$> rs.mapM fun { ctxInfo := ci, tacticInfo := ti, useAfter := useAfter } =>
          let ci := if useAfter then { ci with mctx := ti.mctxAfter } else { ci with mctx := ti.mctxBefore }
          let goals := if useAfter then ti.goalsAfter else ti.goalsBefore
          ci.runMetaM {} <| goals.mapM (fun g => Meta.withPPInaccessibleNames (Widget.goalToInteractive g))
        return some { goals := goals.toArray }
      else
        return none

open Elab in
partial def handlePlainGoal (p : PlainGoalParams)
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

partial def getInteractiveTermGoal (p : Lsp.PlainTermGoalParams)
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
          Meta.withPPInaccessibleNames <| Widget.goalToInteractive (← Meta.mkFreshExprMVar ty).mvarId!
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
    | stx@`(doElem|return%$i $e) => Id.run <| do
      if let some range := i.getRange? then
        if range.contains pos then
          return some { range := doRange?.getD (range.toLspRange text), kind? := DocumentHighlightKind.text }
      highlightReturn? doRange? e
    | `(do%$i $elems) => highlightReturn? (i.getRange?.get!.toLspRange text) elems
    | stx => stx.getArgs.findSome? (highlightReturn? doRange?)

  let highlightRefs? (snaps : Array Snapshot) (pos : Lsp.Position) : Option (Array DocumentHighlight) := Id.run do
    let trees := snaps.map (·.infoTree)
    let refs := findModuleRefs text trees
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
      let (snaps, _) ← doc.allSnaps.updateFinishedPrefix
      if let some his := highlightRefs? snaps.finishedPrefix.toArray p.position then
        return his
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
    let mut stxs := cmdSnaps.finishedPrefix.map (·.stx)
    match e? with
    | some ElabTaskError.aborted =>
      throw RequestError.fileChanged
    | some (ElabTaskError.ioError e) =>
      throw (e : RequestError)
    | _ => pure ()

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
      | _ => Id.run <| do
        let (syms, stxs') := toDocumentSymbols text stxs
        unless stx.isOfKind ``Lean.Parser.Command.declaration do
          return (syms, stxs')
        if let some stxRange := stx.getRange? then
          let (name, selection) := match stx with
            | `($dm:declModifiers $ak:attrKind instance $[$np:namedPrio]? $[$id:ident$[.{$ls,*}]?]? $sig:declSig $val) =>
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
        if let Expr.fvar .. := ti.expr then
          addToken ti.stx SemanticTokenType.variable
        else if ti.stx.getPos?.get! > lastPos then
          -- any info after the start position: must be projection notation
          addToken ti.stx SemanticTokenType.property
          lastPos := ti.stx.getPos?.get!
  highlightKeyword stx := do
    if let Syntax.atom info val := stx then
      if (val.length > 0 && val[0].isAlpha) ||
         -- Support for keywords of the form `#<alpha>...`
         (val.length > 1 && val[0] == '#' && val[1].isAlpha) then
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
  registerLspRequestHandler "$/lean/plainGoal"                  PlainGoalParams            (Option PlainGoal)      handlePlainGoal
  registerLspRequestHandler "$/lean/plainTermGoal"              PlainTermGoalParams        (Option PlainTermGoal)  handlePlainTermGoal

end Lean.Server.FileWorker
