/-
Copyright (c) 2021 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Wojciech Nawrocki, Marc Huisinga
-/
module

prelude
public import Lean.Server.FileWorker.ExampleHover
public import Lean.Server.FileWorker.InlayHints
public import Lean.Server.FileWorker.SemanticHighlighting
public import Lean.Server.FileWorker.SignatureHelp
public import Lean.Server.Completion
public import Lean.Server.References
public import Lean.Server.Completion.CompletionItemCompression

public import Lean.Widget.Diff

public section

namespace Lean.Server.FileWorker
open Lsp
open RequestM
open Snapshots

open Lean.Parser.Tactic.Doc (alternativeOfTactic getTacticExtensionString)

def findCompletionCmdDataAtPos
    (doc : EditableDocument)
    (pos : String.Pos.Raw)
    : ServerTask (Option (Syntax × Elab.InfoTree)) :=
  -- `findCmdDataAtPos` may produce an incorrect snapshot when `pos` is in whitespace.
  -- However, most completions don't need trailing whitespace at the term level;
  -- synthetic completions are the only notions of completion that care care about whitespace.
  -- Synthetic tactic completion only needs the `ContextInfo` of the command, so any snapshot
  -- will do.
  -- Synthetic field completion in `{ }` doesn't care about whitespace;
  -- synthetic field completion in `where` only needs to gather the expected type.
  findCmdDataAtPos doc pos (includeStop := true)

def handleCompletion (p : CompletionParams)
    : RequestM (RequestTask ResolvableCompletionList) := do
  let doc ← readDoc
  let text := doc.meta.text
  let pos := text.lspPosToUtf8Pos p.position
  let caps := (← read).initParams.capabilities
  mapTaskCostly (findCompletionCmdDataAtPos doc pos) fun cmdData? => do
    let some (cmdStx, infoTree) := cmdData?
      | return { items := #[], isIncomplete := true }
    Completion.find? doc.meta.uri p.position doc.meta.text pos cmdStx infoTree caps

/--
Handles `completionItem/resolve` requests that are sent by the client after the user selects
a completion item that was provided by `textDocument/completion`. Resolving the item fills the
`detail?` field of the item with the pretty-printed type.
This control flow is necessary because pretty-printing the type for every single completion item
(even those never selected by the user) is inefficient.
-/
def handleCompletionItemResolve (item : CompletionItem)
    : RequestM (RequestTask CompletionItem) := do
  let doc ← readDoc
  let text := doc.meta.text
  let some (data : ResolvableCompletionItemData) := item.data?.bind fun data => (fromJson? data).toOption
    | return .pure item
  let some id := data.id?
    | return .pure item
  let some cPos := data.cPos?
    | return .pure item
  let pos := text.lspPosToUtf8Pos data.pos
  mapTaskCostly (findCompletionCmdDataAtPos doc pos) fun cmdData? => do
    let some (cmdStx, infoTree) := cmdData?
      | return item
    Completion.resolveCompletionItem? text pos cmdStx infoTree item id cPos

open Elab in
def handleHover (p : HoverParams)
    : RequestM (RequestTask (Option Hover)) := do
  let doc ← readDoc
  let text := doc.meta.text
  let mkHover (s : String) (r : Lean.Syntax.Range) : Hover :=
    let s := Hover.rewriteExamples s
    {
      contents := {
        kind := MarkupKind.markdown
        value := s
      }
      range? := r.toLspRange text
    }

  let hoverPos := text.lspPosToUtf8Pos p.position
  withWaitFindSnap doc (fun s => s.endPos > hoverPos)
    (notFoundX := pure none) fun snap => do
      -- try to find parser docstring from syntax tree
      let stack? := snap.stx.findStack? (·.getRange?.any (·.contains hoverPos))
      let stxDoc? ← match stack? with
        | some stack => stack.findSomeM? fun (stx, _) => do
          let .node _ kind _ := stx | pure none
          let docStr ← findDocString? snap.env kind
          return docStr.map (·, stx.getRange?.get!)
        | none => pure none
      -- now try info tree
      if let some result := snap.infoTree.hoverableInfoAtM? (m := Id) hoverPos then
        let ctx := result.ctx
        let info := result.info
        if let some range := info.range? then
          -- prefer info tree if at least as specific as parser docstring
          if stxDoc?.all fun (_, stxRange) => stxRange.includes range then
            if let some hoverFmt ← info.fmtHover? ctx then
              return mkHover (toString hoverFmt.fmt) range

      if let some (doc, range) := stxDoc? then
        return mkHover doc range

      return none

open Elab GoToKind in
-- The `LeanLocationLink`s in this request get converted to `LocationLink` by the Watchdog process.
-- In doing so, it updates the position information in the location link using the .ilean data
-- it has available (which includes .ilean update notifications, i.e. position information
-- for the unsaved & unbuilt state of open files).
def handleDefinition (kind : GoToKind) (p : TextDocumentPositionParams)
    : RequestM (RequestTask (Array LeanLocationLink)) := do
  let doc ← readDoc
  let text := doc.meta.text
  let hoverPos := text.lspPosToUtf8Pos p.position

  withWaitFindSnap doc (fun s => s.endPos >= hoverPos)
    (notFoundX := pure #[]) fun snap => do
      let filter ctx info _ results := do
        let .ofTermInfo ti := info
          | return results
        ctx.runMetaM info.lctx do
          results.filterM fun (_, r) => do
            let .ofTermInfo childTi := r.info
              | return true
            return ! (← isInstanceProjectionInfoFor kind ti childTi)
      let some info ← snap.infoTree.hoverableInfoAtM? (m := IO) hoverPos
          (includeStop := true) (filter := filter)
        | return #[]
      locationLinksOfInfo doc.meta kind info snap.infoTree

open Language in
def findGoalsAt? (doc : EditableDocument) (hoverPos : String.Pos.Raw) : ServerTask (Option (List Elab.GoalsAtResult)) :=
  let text := doc.meta.text
  findCmdParsedSnap doc hoverPos |>.bindCostly fun
    | some cmdParsed =>
      let t := toSnapshotTree cmdParsed.elabSnap |>.foldSnaps [] fun snap oldGoals => Id.run do
        let some stx := snap.stx?
          | return .pure (oldGoals, .proceed (foldChildren := false))
        let some (pos, tailPos, trailingPos) := getPositions stx
          | return .pure (oldGoals, .proceed (foldChildren := true))
        let snapRange : Lean.Syntax.Range := ⟨pos, trailingPos⟩
        -- When there is no trailing whitespace, we also consider snapshots directly before the
        -- cursor.
        let hasNoTrailingWhitespace := tailPos == trailingPos
        if ! text.rangeContainsHoverPos snapRange hoverPos (includeStop := hasNoTrailingWhitespace) then
          return .pure (oldGoals, .proceed (foldChildren := false))

        return snap.task.asServerTask.mapCheap fun tree => Id.run do
          let some infoTree := tree.element.infoTree?
            | return (oldGoals, .proceed (foldChildren := true))

          let goals := infoTree.goalsAt? text hoverPos
          let optimalSnapRange : Lean.Syntax.Range := ⟨pos, tailPos⟩
          let isOptimalGoalSet :=
            text.rangeContainsHoverPos optimalSnapRange hoverPos
                (includeStop := hasNoTrailingWhitespace)
              || goals.any fun goal => ! goal.indented
          if isOptimalGoalSet then
            return (goals, .done)

          return (goals, .proceed (foldChildren := true))
      t.mapCheap fun
        | []    => none
        | goals => goals
    | none =>
      .pure none
where
  getPositions (stx : Syntax) : Option (String.Pos.Raw × String.Pos.Raw × String.Pos.Raw) := do
    let pos ← stx.getPos? (canonicalOnly := true)
    let tailPos ← stx.getTailPos? (canonicalOnly := true)
    let trailingPos? ← stx.getTrailingTailPos? (canonicalOnly := true)
    return (pos, tailPos, trailingPos?)

open RequestM in
def getInteractiveGoals (p : Lsp.PlainGoalParams) : RequestM (RequestTask (Option Widget.InteractiveGoals)) := do
  let doc ← readDoc
  let text := doc.meta.text
  let hoverPos := text.lspPosToUtf8Pos p.position
  mapTaskCostly (findGoalsAt? doc hoverPos) <| Option.mapM fun rs => do
    let goals : List Widget.InteractiveGoals ← rs.mapM fun { ctxInfo := ci, tacticInfo := ti, useAfter := useAfter, .. } => do
      let ciAfter := { ci with mctx := ti.mctxAfter }
      let ci := if useAfter then ciAfter else { ci with mctx := ti.mctxBefore }
      -- compute the interactive goals
      let goals ← ci.runMetaM {} (do
        let goals := List.toArray <| if useAfter then ti.goalsAfter else ti.goalsBefore
        let goals ← goals.mapM Widget.goalToInteractive
        return ⟨goals⟩
      )
      -- compute the goal diff
      ciAfter.runMetaM {} (do
          try
            Widget.diffInteractiveGoals useAfter ti goals
          catch _ =>
            -- fail silently, since this is just a bonus feature
            return goals
      )
    return goals.foldl (· ++ ·) ∅

open Elab in
def handlePlainGoal (p : PlainGoalParams)
    : RequestM (RequestTask (Option PlainGoal)) := do
  let t ← getInteractiveGoals p
  return t.mapCheap <| Except.map <| Option.map <| fun {goals, ..} =>
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
  mapTaskCostly (findInfoTreeAtPos doc hoverPos (includeStop := true)) <| Option.bindM fun infoTree => do
    let some {ctx := ci, info := i@(Elab.Info.ofTermInfo ti), ..} := infoTree.termGoalAt? hoverPos
      | return none
    let ty ← ci.runMetaM i.lctx do
      instantiateMVars <| ti.expectedType?.getD (← Meta.inferType ti.expr)
    -- for binders, hide the last hypothesis (the binder itself)
    let lctx' := if ti.isBinder then i.lctx.pop else i.lctx
    let goal ← ci.runMetaM lctx' do
      Widget.goalToInteractive (← Meta.mkFreshExprMVar ty).mvarId!
    let range := if let some r := i.range? then r.toLspRange text else ⟨p.position, p.position⟩
    return some { goal with range, term := ← WithRpcRef.mk ti }

def handlePlainTermGoal (p : PlainTermGoalParams)
    : RequestM (RequestTask (Option PlainTermGoal)) := do
  let t ← getInteractiveTermGoal p
  return t.mapCheap <| Except.map <| Option.map fun goal =>
    { goal := toString goal.pretty
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

  let highlightRefs? (snaps : Array Snapshot) : IO (Option (Array DocumentHighlight)) := do
    let trees := snaps.map (·.infoTree)
    let (refs, _) ← findModuleRefs text trees |>.toLspModuleRefs
    let mut ranges := #[]
    for ident in refs.findAt p.position (includeStop := true) do
      if let some info := refs.get? ident then
        if let some loc := info.definition? then
          ranges := ranges.push loc.range
        ranges := ranges.append <| info.usages.map (·.range)
    if ranges.isEmpty then
      return none
    return some <| ranges.map ({ range := ·, kind? := DocumentHighlightKind.text })

  withWaitFindSnap doc (fun s => s.endPos >= pos)
    (notFoundX := pure #[]) fun snap => do
      let (snaps, _) ← doc.cmdSnaps.getFinishedPrefix
      if let some his ← highlightRefs? snaps.toArray then
        return his
      if let some hi := highlightReturn? none snap.stx then
        return #[hi]
      return #[]

structure NamespaceEntry where
  /-- The list of the name components introduced by this namespace command,
  in reverse order so that `end` will peel them off from the front. -/
  name : List Name
  stx : Syntax
  selection : Syntax
  prevSiblings : Array DocumentSymbol

def NamespaceEntry.finish (text : FileMap) (syms : Array DocumentSymbol) (endStx : Option Syntax) :
    NamespaceEntry → Array DocumentSymbol
  | { name, stx, selection, prevSiblings, .. } =>
    -- we can assume that commands always have at least one position (see `parseCommand`)
    let range := match endStx with
      | some endStx => (mkNullNode #[stx, endStx]).getRange?.get!
      | none        =>  { stx.getRange?.get! with stop := text.source.rawEndPos }
    let name := name.foldr (fun x y => y ++ x) Name.anonymous
    prevSiblings.push <| DocumentSymbol.mk {
      -- anonymous sections are represented by `«»` name components
      name := if name == `«» then "<section>" else name.toString
      kind := .namespace
      range := range.toLspRange text
      selectionRange := selection.getRange?.getD range |>.toLspRange text
      children? := syms
    }

open Parser.Command in
partial def handleDocumentSymbol (_ : DocumentSymbolParams)
    : RequestM (RequestTask DocumentSymbolResult) := do
  let doc ← readDoc
  -- bad: we have to wait on elaboration of the entire file before we can report document symbols
  let t := doc.cmdSnaps.waitAll
  mapTaskCostly t fun (snaps, _) => do
    let mut stxs := snaps.map (·.stx)
    return { syms := ← toDocumentSymbols doc.meta.text stxs #[] [] }
where
  toDocumentSymbols (text : FileMap) (stxs : List Syntax)
      (syms : Array DocumentSymbol) (stack : List NamespaceEntry) :
      RequestM (Array DocumentSymbol) := do
    RequestM.checkCancelled
    match stxs with
    | [] => return stack.foldl (fun syms entry => entry.finish text syms none) syms
    | stx::stxs => match stx with
      | `(namespace $id)  =>
        let entry := { name := id.getId.componentsRev, stx, selection := id, prevSiblings := syms }
        toDocumentSymbols text stxs #[] (entry :: stack)
      | `($_:sectionHeader section $(id)?) =>
        let name := id.map (·.getId.componentsRev) |>.getD [`«»]
        let entry := { name, stx, selection := id.map (·.raw) |>.getD stx, prevSiblings := syms }
        toDocumentSymbols text stxs #[] (entry :: stack)
      | `(end $[$id $[.$_]?]?) =>
        let rec popStack n syms
          | [] => toDocumentSymbols text stxs syms []
          | entry :: stack =>
            if entry.name.length == n then
              let syms := entry.finish text syms stx
              toDocumentSymbols text stxs syms stack
            else if entry.name.length > n then
              let syms := { entry with name := entry.name.take n, prevSiblings := #[] }.finish text syms stx
              toDocumentSymbols text stxs syms ({ entry with name := entry.name.drop n } :: stack)
            else
              let syms := entry.finish text syms stx
              popStack (n - entry.name.length) syms stack
        popStack (id.map (·.getId.getNumParts) |>.getD 1) syms stack
      | _ => do
        unless stx.isOfKind ``Lean.Parser.Command.declaration do
          return ← toDocumentSymbols text stxs syms stack
        if let some stxRange := stx.getRange? then
          let (name, selection) := match stx with
            | `($_:declModifiers $_:attrKind instance $[$np:namedPrio]? $[$id$[.{$ls,*}]?]? $sig:declSig $_) =>
              ((·.getId.toString) <$> id |>.getD s!"instance {sig.raw.reprint.getD ""}", id.map (·.raw) |>.getD sig)
            | _ =>
              match stx.getArg 1 |>.getArg 1 with
              | `(declId|$id$[.{$ls,*}]?) => (id.raw.getId.toString, id)
              | _ =>
                let stx10 : Syntax := (stx.getArg 1).getArg 0 -- TODO: stx[1][0] times out
                (stx10.isIdOrAtom?.getD "<unknown>", stx10)
          if let some selRange := selection.getRange? then
            let sym := DocumentSymbol.mk {
              name := name
              kind := SymbolKind.method
              range := stxRange.toLspRange text
              selectionRange := selRange.toLspRange text
            }
            return ← toDocumentSymbols text stxs (syms.push sym) stack
        toDocumentSymbols text stxs syms stack

partial def handleFoldingRange (_ : FoldingRangeParams)
  : RequestM (RequestTask (Array FoldingRange)) := do
  let doc ← readDoc
  let t := doc.cmdSnaps.waitAll
  mapTaskCostly t fun (snaps, _) => do
    let stxs := snaps.map (·.stx)
    let (_, ranges) ← StateT.run (addRanges doc.meta.text [] stxs) #[]
    return ranges
  where
    isImport stx := stx.isOfKind ``Lean.Parser.Module.header || stx.isOfKind ``Lean.Parser.Command.open

    addRanges (text : FileMap) sections
    | [] => do
      if let (_, start)::rest := sections then
        addRange text FoldingRangeKind.region start text.source.rawEndPos
        addRanges text rest []
    | stx::stxs => do
      RequestM.checkCancelled
      match stx with
      | `(namespace $id)  =>
        addRanges text ((id.getId.getNumParts, stx.getPos?)::sections) stxs
      | `($_:sectionHeader section $(id)?) =>
        addRanges text ((id.map (·.getId.getNumParts) |>.getD 1, stx.getPos?)::sections) stxs
      | `(end $[$id $[.$_]?]?) => do
        let rec popRanges n sections := do
          if let (size, start)::rest := sections then
            if size == n then
              addRange text FoldingRangeKind.region start stx.getTailPos?
              addRanges text rest stxs
            else if size > n then
              -- we don't add a range here because vscode doesn't like
              -- multiple folding regions with the same start line
              addRanges text ((size - n, start)::rest) stxs
            else
              addRange text FoldingRangeKind.region start stx.getTailPos?
              popRanges (n - size) rest
          else
            addRanges text sections stxs
        popRanges (id.map (·.getId.getNumParts) |>.getD 1) sections
      | `(mutual $body* end) => do
        addRangeFromSyntax text FoldingRangeKind.region stx
        addRanges text [] body.raw.toList
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
          if let some comment := dm.raw[0].getOptional? then
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

def handleSignatureHelp (p : SignatureHelpParams) : RequestM (RequestTask (Option SignatureHelp)) := do
  let doc ← readDoc
  let text := doc.meta.text
  let requestedPos := text.lspPosToUtf8Pos p.position
  mapTaskCostly (findCmdDataAtPos doc requestedPos (includeStop := false)) fun cmdData? => do
    let some (cmdStx, tree) := cmdData?
      | return none
    SignatureHelp.findSignatureHelp? text p.context? cmdStx tree requestedPos

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
  RequestM.bindTaskCheap t fun doc? => do
    let doc ← liftExcept doc?
    -- We wait on both the reporter and `cmdSnaps` so that all request handlers that use
    -- `IO.hasFinished` on `doc.cmdSnaps` are guaranteed to have finished when
    -- `waitForDiagnostics` returns.
    return doc.reporter.bindCheap (fun _ => doc.cmdSnaps.waitAll)
      |>.mapCheap fun _ => pure WaitForDiagnostics.mk

def handleDocumentColor (_ : DocumentColorParams) :
    RequestM (RequestTask (Array ColorInformation)) :=
  -- By default, if no document color provider is registered, VS Code itself provides
  -- a color picker decoration for all parts of the file that look like CSS colors.
  -- Disabling this setting on the client-side is not possible because of
  -- https://github.com/microsoft/vscode/issues/91533,
  -- so we just provide an empty document color provider here that overrides the
  -- VS Code one.
  return .pure #[]

builtin_initialize
  registerLspRequestHandler
    "textDocument/waitForDiagnostics"
    WaitForDiagnosticsParams
    WaitForDiagnostics
    handleWaitForDiagnostics
  registerLspRequestHandler
    "textDocument/completion"
    CompletionParams
    ResolvableCompletionList
    handleCompletion
    (serialize? := some (·.compressFast))
  registerLspRequestHandler
    "completionItem/resolve"
    CompletionItem
    CompletionItem
    handleCompletionItemResolve
  registerLspRequestHandler
    "textDocument/hover"
    HoverParams
    (Option Hover)
    handleHover
  registerLspRequestHandler
    "textDocument/declaration"
    TextDocumentPositionParams
    (Array LeanLocationLink)
    (handleDefinition GoToKind.declaration)
  registerLspRequestHandler
    "textDocument/definition"
    TextDocumentPositionParams
    (Array LeanLocationLink)
    (handleDefinition GoToKind.definition)
  registerLspRequestHandler
    "textDocument/typeDefinition"
    TextDocumentPositionParams
    (Array LeanLocationLink)
    (handleDefinition GoToKind.type)
  registerLspRequestHandler
    "textDocument/documentHighlight"
    DocumentHighlightParams
    DocumentHighlightResult
    handleDocumentHighlight
  registerLspRequestHandler
    "textDocument/documentSymbol"
    DocumentSymbolParams
    DocumentSymbolResult
    handleDocumentSymbol
  registerLspRequestHandler
    "textDocument/foldingRange"
    FoldingRangeParams
    (Array FoldingRange)
    handleFoldingRange
  registerLspRequestHandler
    "textDocument/signatureHelp"
    SignatureHelpParams
    (Option SignatureHelp)
    handleSignatureHelp
  registerLspRequestHandler
    "textDocument/documentColor"
    DocumentColorParams
    (Array ColorInformation)
    handleDocumentColor
  registerLspRequestHandler
    "$/lean/plainGoal"
    PlainGoalParams
    (Option PlainGoal)
    handlePlainGoal
  registerLspRequestHandler
    "$/lean/plainTermGoal"
    PlainTermGoalParams
    (Option PlainTermGoal)
    handlePlainTermGoal

end Lean.Server.FileWorker
