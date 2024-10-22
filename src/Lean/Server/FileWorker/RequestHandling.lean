/-
Copyright (c) 2021 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Wojciech Nawrocki, Marc Huisinga
-/
prelude
import Lean.DeclarationRange

import Lean.Data.Json
import Lean.Data.Lsp

import Lean.Parser.Tactic.Doc

import Lean.Server.FileWorker.Utils
import Lean.Server.Requests
import Lean.Server.Completion
import Lean.Server.References
import Lean.Server.GoTo

import Lean.Widget.InteractiveGoal
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
  findCmdDataAtPos doc (pos := pos) fun s => Id.run do
    let some tailPos := s.data.stx.getTailPos?
      | return false
    return pos.byteIdx <= tailPos.byteIdx + s.data.stx.getTrailingSize

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
  match i with
  | .ofTermInfo ti =>
    let mut expr := ti.expr
    if kind == type then
      expr ← ci.runMetaM i.lctx do
        return Expr.getAppFn (← instantiateMVars (← Meta.inferType expr))
    match expr with
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
      if let .const n _ := expr.getAppFn then
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
            | _ => pure #[]
          if let some instArg := appArgs.get? instIdx then
            for inst in (← extractInstances instArg) do
              results := results.append (← ci.runMetaM i.lctx <| locationLinksFromDecl i inst)
            results := results.append elaborators -- put elaborators at the end of the results
        return results
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

  withWaitFindSnap doc (fun s => s.endPos >= hoverPos)
    (notFoundX := pure #[]) fun snap => do
      if let some infoWithCtx := snap.infoTree.hoverableInfoAt? (omitIdentApps := true) (includeStop := true /- #767 -/) hoverPos then
        locationLinksOfInfo kind infoWithCtx snap.infoTree
      else return #[]

open RequestM in
def getInteractiveGoals (p : Lsp.PlainGoalParams) : RequestM (RequestTask (Option Widget.InteractiveGoals)) := do
  let doc ← readDoc
  let text := doc.meta.text
  let hoverPos := text.lspPosToUtf8Pos p.position
  mapTask (findInfoTreeAtPosWithTrailingWhitespace doc hoverPos) <| Option.bindM fun infoTree => do
    let rs@(_ :: _) := infoTree.goalsAt? doc.meta.text hoverPos
      | return none
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
    return some <| goals.foldl (· ++ ·) ∅

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
  mapTask (findInfoTreeAtPosWithTrailingWhitespace doc hoverPos) <| Option.bindM fun infoTree => do
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

/--
`SyntaxNodeKind`s for which the syntax node and its children receive no semantic highlighting.
-/
def noHighlightKinds : Array SyntaxNodeKind := #[
  -- usually have special highlighting by the client
  ``Lean.Parser.Term.sorry,
  ``Lean.Parser.Term.type,
  ``Lean.Parser.Term.prop,
  -- not really keywords
  `antiquotName,
  ``Lean.Parser.Command.docComment,
  ``Lean.Parser.Command.moduleDoc]

-- TODO: make extensible, or don't
/-- Keywords for which a specific semantic token is provided. -/
def keywordSemanticTokenMap : RBMap String SemanticTokenType compare :=
  RBMap.empty
    |>.insert "sorry" .leanSorryLike
    |>.insert "admit" .leanSorryLike
    |>.insert "stop" .leanSorryLike
    |>.insert "#exit" .leanSorryLike

/-- Semantic token information for a given `Syntax`. -/
structure LeanSemanticToken where
  /-- Syntax of the semantic token. -/
  stx  : Syntax
  /-- Type of the semantic token. -/
  type : SemanticTokenType

/-- Semantic token information with absolute LSP positions. -/
structure AbsoluteLspSemanticToken where
  /-- Start position of the semantic token. -/
  pos     : Lsp.Position
  /-- End position of the semantic token. -/
  tailPos : Lsp.Position
  /-- Start position of the semantic token. -/
  type    : SemanticTokenType
  deriving BEq, Hashable, FromJson, ToJson

/--
Given a set of `LeanSemanticToken`, computes the `AbsoluteLspSemanticToken` with absolute
LSP position information for each token.
-/
def computeAbsoluteLspSemanticTokens
    (text     : FileMap)
    (beginPos : String.Pos)
    (endPos?  : Option String.Pos)
    (tokens   : Array LeanSemanticToken)
    : Array AbsoluteLspSemanticToken :=
  tokens.filterMap fun ⟨stx, tokenType⟩ => do
    let (pos, tailPos) := (← stx.getPos?, ← stx.getTailPos?)
    guard <| beginPos <= pos && endPos?.all (pos < ·)
    let (lspPos, lspTailPos) := (text.utf8PosToLspPos pos, text.utf8PosToLspPos tailPos)
    return ⟨lspPos, lspTailPos, tokenType⟩

/-- Filters all duplicate semantic tokens with the same `pos`, `tailPos` and `type`. -/
def filterDuplicateSemanticTokens (tokens : Array AbsoluteLspSemanticToken) : Array AbsoluteLspSemanticToken :=
  tokens.groupByKey id |>.toArray.map (·.1)

/--
Given a set of `AbsoluteLspSemanticToken`, computes the LSP `SemanticTokens` data with
token-relative positioning.
See https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/#textDocument_semanticTokens.
-/
def computeDeltaLspSemanticTokens (tokens : Array AbsoluteLspSemanticToken) : SemanticTokens := Id.run do
  let tokens := tokens.qsort fun ⟨pos1, tailPos1, _⟩ ⟨pos2, tailPos2, _⟩ =>
    pos1 < pos2 || pos1 == pos2 && tailPos1 <= tailPos2
  let mut data : Array Nat := Array.mkEmpty (5*tokens.size)
  let mut lastPos : Lsp.Position := ⟨0, 0⟩
  for ⟨pos, tailPos, tokenType⟩ in tokens do
    let deltaLine := pos.line - lastPos.line
    let deltaStart := pos.character - (if pos.line == lastPos.line then lastPos.character else 0)
    let length := tailPos.character - pos.character
    let tokenType := tokenType.toNat
    let tokenModifiers := 0
    data := data ++ #[deltaLine, deltaStart, length, tokenType, tokenModifiers]
    lastPos := pos
  return { data }

/--
Collects all semantic tokens that can be deduced purely from `Syntax`
without elaboration information.
-/
partial def collectSyntaxBasedSemanticTokens : (stx : Syntax) → Array LeanSemanticToken
  | `($e.$id:ident)    =>
    let tokens := collectSyntaxBasedSemanticTokens e
    tokens.push ⟨id, SemanticTokenType.property⟩
  | `($e |>.$field:ident) =>
    let tokens := collectSyntaxBasedSemanticTokens e
    tokens.push ⟨field, SemanticTokenType.property⟩
  | stx => Id.run do
    if noHighlightKinds.contains stx.getKind then
      return #[]
    let mut tokens :=
      if stx.isOfKind choiceKind then
        collectSyntaxBasedSemanticTokens stx[0]
      else
        stx.getArgs.map collectSyntaxBasedSemanticTokens |>.flatten
    let Syntax.atom _ val := stx
      | return tokens
    let isRegularKeyword := val.length > 0 && val.front.isAlpha
    let isHashKeyword := val.length > 1 && val.front == '#' && (val.get ⟨1⟩).isAlpha
    if ! isRegularKeyword && ! isHashKeyword then
      return tokens
    return tokens.push ⟨stx, keywordSemanticTokenMap.findD val .keyword⟩

/-- Collects all semantic tokens from the given `Elab.InfoTree`. -/
def collectInfoBasedSemanticTokens (i : Elab.InfoTree) : Array LeanSemanticToken :=
  List.toArray <| i.deepestNodes fun _ i _ => do
    let .ofTermInfo ti := i
      | none
    let .original .. := ti.stx.getHeadInfo
      | none
    if let `($_:ident) := ti.stx then
      if let Expr.fvar fvarId .. := ti.expr then
        if let some localDecl := ti.lctx.find? fvarId then
          -- Recall that `isAuxDecl` is an auxiliary declaration used to elaborate a recursive definition.
          if localDecl.isAuxDecl then
            if ti.isBinder then
              return ⟨ti.stx, SemanticTokenType.function⟩
          else if ! localDecl.isImplementationDetail then
            return ⟨ti.stx, SemanticTokenType.variable⟩
    if ti.stx.getKind == Parser.Term.identProjKind then
      return ⟨ti.stx, SemanticTokenType.property⟩
    none

/-- Computes the semantic tokens in the range [beginPos, endPos?). -/
def handleSemanticTokens (beginPos : String.Pos) (endPos? : Option String.Pos)
    : RequestM (RequestTask SemanticTokens) := do
  let doc ← readDoc
  match endPos? with
  | none =>
    -- Only grabs the finished prefix so that we do not need to wait for elaboration to complete
    -- for the full file before sending a response. This means that the response will be incomplete,
    -- which we mitigate by regularly sending `workspace/semanticTokens/refresh` requests in the
    -- `FileWorker` to tell the client to re-compute the semantic tokens.
    let (snaps, _) ← doc.cmdSnaps.getFinishedPrefix
    asTask <| run doc snaps
  | some endPos =>
    let t := doc.cmdSnaps.waitUntil (·.endPos >= endPos)
    mapTask t fun (snaps, _) => run doc snaps
where
  run doc snaps : RequestM SemanticTokens := do
    let mut leanSemanticTokens := #[]
    for s in snaps do
      if s.endPos <= beginPos then
        continue
      let syntaxBasedSemanticTokens := collectSyntaxBasedSemanticTokens s.stx
      let infoBasedSemanticTokens := collectInfoBasedSemanticTokens s.infoTree
      leanSemanticTokens := leanSemanticTokens ++ syntaxBasedSemanticTokens ++ infoBasedSemanticTokens
    let absoluteLspSemanticTokens := computeAbsoluteLspSemanticTokens doc.meta.text beginPos endPos? leanSemanticTokens
    let absoluteLspSemanticTokens := filterDuplicateSemanticTokens absoluteLspSemanticTokens
    let semanticTokens := computeDeltaLspSemanticTokens absoluteLspSemanticTokens
    return semanticTokens

/-- Computes all semantic tokens for the document. -/
def handleSemanticTokensFull (_ : SemanticTokensParams)
    : RequestM (RequestTask SemanticTokens) := do
  handleSemanticTokens 0 none

/-- Computes the semantic tokens in the range provided by `p`. -/
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
    "textDocument/semanticTokens/full"
    SemanticTokensParams
    SemanticTokens
    handleSemanticTokensFull
  registerLspRequestHandler
    "textDocument/semanticTokens/range"
    SemanticTokensRangeParams
    SemanticTokens
    handleSemanticTokensRange
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
