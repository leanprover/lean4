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

  let locationLinksFromDecl (i : Elab.Info) (n : Name) := do
    let mod? ← findModuleOf? n
    let modUri? ← match mod? with
      | some modName =>
        let modFname? ← rc.srcSearchPath.findWithExt "lean" modName
        pure <| modFname?.map toFileUri
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

  withWaitFindSnap doc (fun s => s.endPos > hoverPos)
    (notFoundX := pure #[]) fun snap => do
      for t in snap.cmdState.infoState.trees do
        if let some (ci, i) := t.hoverableInfoAt? hoverPos then
          if let Info.ofTermInfo ti := i then
            let mut expr := ti.expr
            if kind == type then
              expr ← ci.runMetaM i.lctx do
                Expr.getAppFn (← Meta.instantiateMVars (← Meta.inferType expr))
            match expr with
            | Expr.const n .. => return ← ci.runMetaM i.lctx <| locationLinksFromDecl i n
            | Expr.fvar id .. => return ← ci.runMetaM i.lctx <| locationLinksFromBinder t i id
            | _ => pure ()
          if let Info.ofFieldInfo fi := i then
            if kind == type then
              let expr ← ci.runMetaM i.lctx do
                Meta.instantiateMVars (← Meta.inferType fi.val)
              if let some n := expr.getAppFn.constName? then
                return ← ci.runMetaM i.lctx <| locationLinksFromDecl i n
            else
              return ← ci.runMetaM i.lctx <| locationLinksFromDecl i fi.projName
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
      for t in snap.cmdState.infoState.trees do
        if let rs@(_ :: _) := t.goalsAt? doc.meta.text hoverPos then
          let goals ← List.join <$> rs.mapM fun { ctxInfo := ci, tacticInfo := ti, useAfter := useAfter } =>
            let ci := if useAfter then { ci with mctx := ti.mctxAfter } else { ci with mctx := ti.mctxBefore }
            let goals := if useAfter then ti.goalsAfter else ti.goalsBefore
            ci.runMetaM {} <| goals.mapM (fun g => Meta.withPPInaccessibleNames (Widget.goalToInteractive g))
          return some { goals := goals.toArray }

      return none

open Elab in
partial def handlePlainGoal (p : PlainGoalParams)
    : RequestM (RequestTask (Option PlainGoal)) := do
  let t ← getInteractiveGoals p
  t.map <| Except.map <| Option.map <| fun ⟨goals⟩ =>
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
      for t in snap.cmdState.infoState.trees do
        if let some (ci, i@(Elab.Info.ofTermInfo ti)) := t.termGoalAt? hoverPos then
         let ty ← ci.runMetaM i.lctx do
           Meta.instantiateMVars <| ti.expectedType?.getD (← Meta.inferType ti.expr)
         -- for binders, hide the last hypothesis (the binder itself)
         let lctx' := if ti.isBinder then i.lctx.pop else i.lctx
         let goal ← ci.runMetaM lctx' do
           Meta.withPPInaccessibleNames <| Widget.goalToInteractive (← Meta.mkFreshExprMVar ty).mvarId!
         let range := if let some r := i.range? then r.toLspRange text else ⟨p.position, p.position⟩
         return some { goal with range }
      return none

def handlePlainTermGoal (p : PlainTermGoalParams)
    : RequestM (RequestTask (Option PlainTermGoal)) := do
  let t ← getInteractiveTermGoal p
  t.map <| Except.map <| Option.map fun goal =>
    { goal := toString goal.toInteractiveGoal.pretty
      range := goal.range
    }

partial def handleDocumentHighlight (p : DocumentHighlightParams)
    : RequestM (RequestTask (Array DocumentHighlight)) := do
  let doc ← readDoc
  let text := doc.meta.text
  let pos := text.lspPosToUtf8Pos p.position
  let rec highlightReturn? (doRange? : Option Range) : Syntax → Option DocumentHighlight
    | stx@`(doElem|return%$i $e) => do
      if let some range := i.getRange? then
        if range.contains pos then
          return some { range := doRange?.getD (range.toLspRange text), kind? := DocumentHighlightKind.text }
      highlightReturn? doRange? e
    | `(do%$i $elems) => highlightReturn? (i.getRange?.get!.toLspRange text) elems
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
    let mut stxs := cmdSnaps.finishedPrefix.map (·.stx)
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
      | _ => do
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
    if let some range := stx.getRange? then
      for t in (← read).infoState.trees do
        for ti in t.deepestNodes (fun
          | _, i@(Elab.Info.ofTermInfo ti), _ => match i.pos? with
            | some ipos => if range.contains ipos then some ti else none
            | _         => none
          | _, _, _ => none) do
          match ti.expr with
          | Expr.fvar .. => addToken ti.stx SemanticTokenType.variable
          | _            => if ti.stx.getPos?.get! > range.start then addToken ti.stx SemanticTokenType.property
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
