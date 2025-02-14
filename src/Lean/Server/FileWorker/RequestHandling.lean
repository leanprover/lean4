/-
Copyright (c) 2021 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Wojciech Nawrocki, Marc Huisinga
-/
prelude
import Lean.Server.FileWorker.InlayHints
import Lean.Server.FileWorker.SemanticHighlighting
import Lean.Server.Completion
import Lean.Server.References

import Lean.Widget.Diff

namespace Lean.Server.FileWorker
open Lsp
open RequestM
open Snapshots

open Lean.Parser.Tactic.Doc (alternativeOfTactic getTacticExtensionString)

def findCompletionCmdDataAtPos
    (doc : EditableDocument)
    (pos : String.Pos)
    : Task (Option (Syntax × Elab.InfoTree)) :=
  -- `findCmdDataAtPos` may produce an incorrect snapshot when `pos` is in whitespace.
  -- However, most completions don't need trailing whitespace at the term level;
  -- synthetic completions are the only notions of completion that care care about whitespace.
  -- Synthetic tactic completion only needs the `ContextInfo` of the command, so any snapshot
  -- will do.
  -- Synthetic field completion in `{ }` doesn't care about whitespace;
  -- synthetic field completion in `where` only needs to gather the expected type.
  findCmdDataAtPos doc pos (includeStop := true)

def handleCompletion (p : CompletionParams)
    : RequestM (RequestTask CompletionList) := do
  let doc ← readDoc
  let text := doc.meta.text
  let pos := text.lspPosToUtf8Pos p.position
  let caps := (← read).initParams.capabilities
  mapTask (findCompletionCmdDataAtPos doc pos) fun cmdData? => do
    let some (cmdStx, infoTree) := cmdData?
      -- work around https://github.com/microsoft/vscode/issues/155738
      | return {
        items := #[{label := "-", data? := toJson { params := p : Lean.Lsp.CompletionItemData }}],
        isIncomplete := true
      }
    Completion.find? p doc.meta.text pos cmdStx infoTree caps

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
  let pos := text.lspPosToUtf8Pos data.params.position
  mapTask (findCompletionCmdDataAtPos doc pos) fun cmdData? => do
    let some (cmdStx, infoTree) := cmdData?
      | return item
    Completion.resolveCompletionItem? text pos cmdStx infoTree item id data.cPos

open Elab in
def handleHover (p : HoverParams)
    : RequestM (RequestTask (Option Hover)) := do
  let doc ← readDoc
  let text := doc.meta.text
  let mkHover (s : String) (r : String.Range) : Hover := {
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
      if let some ictx := snap.infoTree.hoverableInfoAt? hoverPos then
        if let some range := ictx.info.range? then
          -- prefer info tree if at least as specific as parser docstring
          if stxDoc?.all fun (_, stxRange) => stxRange.includes range then
            if let some hoverFmt ← ictx.info.fmtHover? ictx.ctx then
              return mkHover (toString hoverFmt.fmt) range

      if let some (doc, range) := stxDoc? then
        return mkHover doc range

      return none

open Elab GoToKind in
def locationLinksOfInfo (kind : GoToKind) (ictx : InfoWithCtx)
    (infoTree? : Option InfoTree := none) : RequestM (Array LocationLink) := do
  let rc ← read
  let doc ← readDoc
  let text := doc.meta.text

  let locationLinksFromDecl (i : Elab.Info) (n : Name) :=
    locationLinksFromDecl rc.srcSearchPath doc.meta.uri n <| (·.toLspRange text) <$> i.range?

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
    if let some modUri ← documentUriFromModule rc.srcSearchPath name then
      let range := { start := ⟨0, 0⟩, «end» := ⟨0, 0⟩ : Range }
      let ll : LocationLink := {
        originSelectionRange? := (·.toLspRange text) <$> i.stx[2].getRange? (canonicalOnly := true)
        targetUri := modUri
        targetRange := range
        targetSelectionRange := range
      }
      return #[ll]
    return #[]

  let i := ictx.info
  let ci := ictx.ctx
  let children := ictx.children

  let locationLinksDefault : RequestM (Array LocationLink) := do
    -- If other go-tos fail, we try to show the elaborator or parser
    if let some ei := i.toElabInfo? then
      if kind == declaration && ci.env.contains ei.stx.getKind then
        return ← ci.runMetaM i.lctx <| locationLinksFromDecl i ei.stx.getKind
      if kind == definition && ci.env.contains ei.elaborator then
        return ← ci.runMetaM i.lctx <| locationLinksFromDecl i ei.elaborator
    return #[]

  let locationLinksFromTermInfo (ti : TermInfo) : RequestM (Array LocationLink) := do
    let mut expr := ti.expr
    if kind == type then
      expr ← ci.runMetaM i.lctx do
        return Expr.getAppFn (← instantiateMVars (← Meta.inferType expr))
    match expr.consumeMData with
    | Expr.const n .. => return ← ci.runMetaM i.lctx <| locationLinksFromDecl i n
    | Expr.fvar id .. => return ← ci.runMetaM i.lctx <| locationLinksFromBinder i id
    | _ => pure ()

    -- Check whether this `TermInfo` node is directly responsible for its `.expr`.
    -- This is the case iff all of its children represent strictly smaller subexpressions;
    -- it is sufficient to check this of all direct children of this node (and that its elaborator didn't expand it as a macro)
    let isExprGenerator := children.all fun
      | .node (Info.ofTermInfo info) _ => info.expr != expr
      | .node (Info.ofMacroExpansionInfo _) _ => false
      | _ => true

    -- don't go-to-instance if this `TermInfo` didn't directly generate its `.expr`
    if kind != declaration && isExprGenerator then
      -- go-to-definition on a projection application of a typeclass
      -- should return all instances generated by TC
      expr ← ci.runMetaM i.lctx do instantiateMVars expr
      if let .const n _ := expr.getAppFn.consumeMData then
        -- also include constant along with instance results
        let mut results ← ci.runMetaM i.lctx <| locationLinksFromDecl i n
        if let some info := ci.env.getProjectionFnInfo? n then
          let mut elaborators := default
          if let some ei := i.toElabInfo? then do
            -- also include elaborator along with instance results, as this wouldn't be accessible otherwise
            if ei.elaborator != `Delab -- prevent an error if this `TermInfo` came from the infoview
              && ei.elaborator != `Lean.Elab.Term.elabApp && ei.elaborator != `Lean.Elab.Term.elabIdent -- don't include trivial elaborators
              then do
              elaborators ← ci.runMetaM i.lctx <| locationLinksFromDecl i ei.elaborator
          let instIdx := info.numParams
          let appArgs := expr.getAppArgs
          let rec extractInstances : Expr → RequestM (Array Name)
            | .const declName _ => do
              if ← ci.runMetaM i.lctx do Lean.Meta.isInstance declName then pure #[declName] else pure #[]
            | .app fn arg => do pure $ (← extractInstances fn).append (← extractInstances arg)
            | .mdata _ e => extractInstances e
            | _ => pure #[]
          if let some instArg := appArgs.get? instIdx then
            for inst in (← extractInstances instArg) do
              results := results.append (← ci.runMetaM i.lctx <| locationLinksFromDecl i inst)
            results := results.append elaborators -- put elaborators at the end of the results
        return results
    locationLinksDefault

  match i with
  | .ofTermInfo ti =>
    return ← locationLinksFromTermInfo ti
  | .ofDelabTermInfo { toTermInfo := ti, location?, .. } =>
    if let some location := location? then
      if let some targetUri ← documentUriFromModule rc.srcSearchPath location.module then
        let range := location.range.toLspRange
        let result : LocationLink := {
          targetUri, targetRange := range, targetSelectionRange := range,
          originSelectionRange? := (·.toLspRange text) <$> i.range?
        }
        return #[result]
      -- If we fail to find a DocumentUri, fall through and use the default method to at least try to have something to jump to.
    return ← locationLinksFromTermInfo ti
  | .ofFieldInfo fi =>
    if kind == type then
      let expr ← ci.runMetaM i.lctx do
        instantiateMVars (← Meta.inferType fi.val)
      if let some n := expr.getAppFn.constName? then
        return ← ci.runMetaM i.lctx <| locationLinksFromDecl i n
    else
      return ← ci.runMetaM i.lctx <| locationLinksFromDecl i fi.projName
  | .ofOptionInfo oi =>
    return ← ci.runMetaM i.lctx <| locationLinksFromDecl i oi.declName
  | .ofCommandInfo ⟨`import, _⟩ =>
    if kind == definition || kind == declaration then
      return ← ci.runMetaM i.lctx <| locationLinksFromImport i
  | _ => pure ()
  locationLinksDefault

open Elab GoToKind in
def handleDefinition (kind : GoToKind) (p : TextDocumentPositionParams)
    : RequestM (RequestTask (Array LocationLink)) := do
  let doc ← readDoc
  let text := doc.meta.text
  let hoverPos := text.lspPosToUtf8Pos p.position

  withWaitFindSnap doc (fun s => s.endPos >= hoverPos)
    (notFoundX := pure #[]) fun snap => do
      if let some infoWithCtx := snap.infoTree.hoverableInfoAt? (omitIdentApps := true) (includeStop := true /- #767 -/) hoverPos then
        locationLinksOfInfo kind infoWithCtx snap.infoTree
      else return #[]

open Language in
def findGoalsAt? (doc : EditableDocument) (hoverPos : String.Pos) : Task (Option (List Elab.GoalsAtResult)) :=
  let text := doc.meta.text
  findCmdParsedSnap doc hoverPos |>.bind (sync := true) fun
    | some cmdParsed =>
      let t := toSnapshotTree cmdParsed |>.foldSnaps [] fun snap oldGoals => Id.run do
        let some (pos, tailPos, trailingPos) := getPositions snap
          | return .pure (oldGoals, .proceed (foldChildren := false))
        let snapRange : String.Range := ⟨pos, trailingPos⟩
        -- When there is no trailing whitespace, we also consider snapshots directly before the
        -- cursor.
        let hasNoTrailingWhitespace := tailPos == trailingPos
        if ! text.rangeContainsHoverPos snapRange hoverPos (includeStop := hasNoTrailingWhitespace) then
          return .pure (oldGoals, .proceed (foldChildren := false))

        return snap.task.map (sync := true) fun tree => Id.run do
          let some infoTree := tree.element.infoTree?
            | return (oldGoals, .proceed (foldChildren := true))

          let goals := infoTree.goalsAt? text hoverPos
          let optimalSnapRange : String.Range := ⟨pos, tailPos⟩
          let isOptimalGoalSet :=
            text.rangeContainsHoverPos optimalSnapRange hoverPos
                (includeStop := hasNoTrailingWhitespace)
              || goals.any fun goal => ! goal.indented
          if isOptimalGoalSet then
            return (goals, .done)

          return (goals, .proceed (foldChildren := true))
      t.map fun
        | []    => none
        | goals => goals
    | none =>
      .pure none
where
  getPositions (snap : SnapshotTask SnapshotTree) : Option (String.Pos × String.Pos × String.Pos) := do
    let stx ← snap.stx?
    let pos ← stx.getPos? (canonicalOnly := true)
    let tailPos ← stx.getTailPos? (canonicalOnly := true)
    let trailingPos? ← stx.getTrailingTailPos? (canonicalOnly := true)
    return (pos, tailPos, trailingPos?)

open RequestM in
def getInteractiveGoals (p : Lsp.PlainGoalParams) : RequestM (RequestTask (Option Widget.InteractiveGoals)) := do
  let doc ← readDoc
  let text := doc.meta.text
  let hoverPos := text.lspPosToUtf8Pos p.position
  mapTask (findGoalsAt? doc hoverPos) <| Option.mapM fun rs => do
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
  return t.map <| Except.map <| Option.map <| fun {goals, ..} =>
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
  mapTask (findInfoTreeAtPos doc hoverPos (includeStop := true)) <| Option.bindM fun infoTree => do
    let some {ctx := ci, info := i@(Elab.Info.ofTermInfo ti), ..} := infoTree.termGoalAt? hoverPos
      | return none
    let ty ← ci.runMetaM i.lctx do
      instantiateMVars <| ti.expectedType?.getD (← Meta.inferType ti.expr)
    -- for binders, hide the last hypothesis (the binder itself)
    let lctx' := if ti.isBinder then i.lctx.pop else i.lctx
    let goal ← ci.runMetaM lctx' do
      Widget.goalToInteractive (← Meta.mkFreshExprMVar ty).mvarId!
    let range := if let some r := i.range? then r.toLspRange text else ⟨p.position, p.position⟩
    return some { goal with range, term := ⟨ti⟩ }

def handlePlainTermGoal (p : PlainTermGoalParams)
    : RequestM (RequestTask (Option PlainTermGoal)) := do
  let t ← getInteractiveTermGoal p
  return t.map <| Except.map <| Option.map fun goal =>
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
    let refs : Lsp.ModuleRefs ← findModuleRefs text trees |>.toLspModuleRefs
    let mut ranges := #[]
    for ident in refs.findAt p.position (includeStop := true) do
      if let some info := refs.get? ident then
        if let some ⟨definitionRange, _⟩ := info.definition? then
          ranges := ranges.push definitionRange
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
      | none        =>  { stx.getRange?.get! with stop := text.source.endPos }
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
  mapTask t fun (snaps, _) => do
    let mut stxs := snaps.map (·.stx)
    return { syms := toDocumentSymbols doc.meta.text stxs #[] [] }
where
  toDocumentSymbols (text : FileMap) (stxs : List Syntax)
      (syms : Array DocumentSymbol) (stack : List NamespaceEntry) :
      Array DocumentSymbol :=
    match stxs with
    | [] => stack.foldl (fun syms entry => entry.finish text syms none) syms
    | stx::stxs => match stx with
      | `(namespace $id)  =>
        let entry := { name := id.getId.componentsRev, stx, selection := id, prevSiblings := syms }
        toDocumentSymbols text stxs #[] (entry :: stack)
      | `(section $(id)?) =>
        let name := id.map (·.getId.componentsRev) |>.getD [`«»]
        let entry := { name, stx, selection := id.map (·.raw) |>.getD stx, prevSiblings := syms }
        toDocumentSymbols text stxs #[] (entry :: stack)
      | `(end $(id)?) =>
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
      | _ => Id.run do
        unless stx.isOfKind ``Lean.Parser.Command.declaration do
          return toDocumentSymbols text stxs syms stack
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
            return toDocumentSymbols text stxs (syms.push sym) stack
        toDocumentSymbols text stxs syms stack

partial def handleFoldingRange (_ : FoldingRangeParams)
  : RequestM (RequestTask (Array FoldingRange)) := do
  let doc ← readDoc
  let t := doc.cmdSnaps.waitAll
  mapTask t fun (snaps, _) => do
    let stxs := snaps.map (·.stx)
    let (_, ranges) ← StateT.run (addRanges doc.meta.text [] stxs) #[]
    return ranges
  where
    isImport stx := stx.isOfKind ``Lean.Parser.Module.header || stx.isOfKind ``Lean.Parser.Command.open

    addRanges (text : FileMap) sections
    | [] => do
      if let (_, start)::rest := sections then
        addRange text FoldingRangeKind.region start text.source.endPos
        addRanges text rest []
    | stx::stxs => match stx with
      | `(namespace $id)  =>
        addRanges text ((id.getId.getNumParts, stx.getPos?)::sections) stxs
      | `(section $(id)?) =>
        addRanges text ((id.map (·.getId.getNumParts) |>.getD 1, stx.getPos?)::sections) stxs
      | `(end $(id)?) => do
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
    return doc.reporter.map fun _ => pure WaitForDiagnostics.mk

builtin_initialize
  registerLspRequestHandler
    "textDocument/waitForDiagnostics"
    WaitForDiagnosticsParams
    WaitForDiagnostics
    handleWaitForDiagnostics
  registerLspRequestHandler
    "textDocument/completion"
    CompletionParams
    CompletionList
    handleCompletion
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
    (Array LocationLink)
    (handleDefinition GoToKind.declaration)
  registerLspRequestHandler
    "textDocument/definition"
    TextDocumentPositionParams
    (Array LocationLink)
    (handleDefinition GoToKind.definition)
  registerLspRequestHandler
    "textDocument/typeDefinition"
    TextDocumentPositionParams
    (Array LocationLink)
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
