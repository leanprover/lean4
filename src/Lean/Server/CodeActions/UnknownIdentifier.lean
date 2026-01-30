/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Huisinga
-/
module

prelude
public import Lean.Server.Completion.CompletionInfoSelection
public import Lean.Server.CodeActions.Basic

public section

namespace Lean.Server.FileWorker

open Lean.Lsp
open Lean.Server.Completion

private def compareRanges (r1 r2 : Lean.Syntax.Range) : Ordering :=
  if r1.start < r2.start then
    .lt
  else if r1.start > r2.start then
    .gt
  else if r1.stop < r2.stop then
    .lt
  else if r1.stop > r2.stop then
    .gt
  else
    .eq

def waitUnknownIdentifierRanges (doc : EditableDocument) (requestedRange : Lean.Syntax.Range)
    : BaseIO (Array Lean.Syntax.Range × Bool) := do
  let text := doc.meta.text
  let some parsedSnap := RequestM.findCmdParsedSnap doc requestedRange.start |>.get
    | return (#[], false)
  let tree := Language.toSnapshotTree parsedSnap.elabSnap
  let msgLog := tree.collectMessagesInRange requestedRange |>.get
  let mut ranges := #[]
  for msg in msgLog.unreported do
    if ! msg.data.hasTag (· == unknownIdentifierMessageTag) then
      continue
    let msgRange : Lean.Syntax.Range := ⟨text.ofPosition msg.pos, text.ofPosition <| msg.endPos.getD msg.pos⟩
    if ! msgRange.overlaps requestedRange
        (includeFirstStop := true) (includeSecondStop := true) then
      continue
    ranges := ranges.push msgRange
  let isAnyUnknownIdentifierMessage := ! ranges.isEmpty
  let autoImplicitUsages : ServerTask (Std.TreeSet Lean.Syntax.Range compareRanges) :=
    tree.foldInfosInRange requestedRange ∅ fun ctx i acc => Id.run do
      let .ofTermInfo ti := i
        | return acc
      let some r := ti.stx.getRange? (canonicalOnly := true)
        | return acc
      if ! ti.expr.isFVar then
        return acc
      if ! ctx.autoImplicits.contains ti.expr then
        return acc
      return acc.insert r
  let autoImplicitUsages := autoImplicitUsages.get.toArray
  ranges := ranges ++ autoImplicitUsages
  return (ranges, isAnyUnknownIdentifierMessage)

def waitAllUnknownIdentifierMessageRanges (doc : EditableDocument)
    : BaseIO (Array Lean.Syntax.Range) := do
  let text := doc.meta.text
  let snaps := Language.toSnapshotTree doc.initSnap |>.getAll
  let msgLog : MessageLog := snaps.map (·.diagnostics.msgLog) |>.foldl (· ++ ·) {}
  let mut ranges := #[]
  for msg in msgLog.unreported do
    if ! msg.data.hasTag (· == unknownIdentifierMessageTag) then
      continue
    let msgRange : Lean.Syntax.Range := ⟨text.ofPosition msg.pos, text.ofPosition <| msg.endPos.getD msg.pos⟩
    ranges := ranges.push msgRange
  let (cmdSnaps, _) := doc.cmdSnaps.waitAll.get
  for snap in cmdSnaps do
    let autoImplicitUsages : Std.TreeSet Lean.Syntax.Range compareRanges :=
      snap.infoTree.foldInfo (init := ∅) fun ctx i acc => Id.run do
        let .ofTermInfo ti := i
          | return acc
        let some r := ti.stx.getRange? (canonicalOnly := true)
          | return acc
        if ! ti.expr.isFVar then
          return acc
        if ! ctx.autoImplicits.contains ti.expr then
          return acc
        return acc.insert r
    ranges := ranges ++ autoImplicitUsages.toArray
  return ranges

structure Insertion where
  fullName : Name
  edit     : TextEdit

structure Query extends LeanModuleQuery where
  ctx                : Elab.ContextInfo
  determineInsertion : Name → Insertion

partial def collectOpenNamespaces (currentNamespace : Name) (openDecls : List OpenDecl)
    : Array OpenNamespace := Id.run do
  let mut openNamespaces : Array OpenNamespace := #[]
  let mut currentNamespace := currentNamespace
  while ! currentNamespace.isAnonymous do
    openNamespaces := openNamespaces.push <| .allExcept currentNamespace #[]
    currentNamespace := currentNamespace.getPrefix
  let openDeclNamespaces := openDecls.map fun
    | .simple ns except => .allExcept ns except.toArray
    | .explicit id declName => .renamed declName id
  openNamespaces := openNamespaces ++ openDeclNamespaces.toArray
  return openNamespaces

def computeIdQuery?
    (doc : EditableDocument)
    (ctx : Elab.ContextInfo)
    (stx : Syntax)
    (id : Name)
    : Option Query := do
  let some pos := stx.getPos? (canonicalOnly := true)
    | none
  let some tailPos := stx.getTailPos? (canonicalOnly := true)
    | none
  return {
    identifier := id.toString
    openNamespaces := collectOpenNamespaces ctx.currNamespace ctx.openDecls
    ctx
    determineInsertion decl :=
      let minimizedId := minimizeGlobalIdentifierInContext ctx.currNamespace ctx.openDecls decl
      {
        fullName := minimizedId
        edit := {
          range := doc.meta.text.utf8RangeToLspRange ⟨pos, tailPos⟩
          newText := minimizedId.toString
        }
      }
  }

def computeDotQuery?
    (doc : EditableDocument)
    (ctx : Elab.ContextInfo)
    (ti : Elab.TermInfo)
    : IO (Option Query) := do
  let text := doc.meta.text
  let some pos := ti.stx.getPos? (canonicalOnly := true)
    | return none
  let some tailPos := ti.stx.getTailPos? (canonicalOnly := true)
    | return none
  let typeNames? : Option (Array Name) ← ctx.runMetaM ti.lctx do
    try
      return some <| ← getDotCompletionTypeNames (← Lean.instantiateMVars (← Lean.Meta.inferType ti.expr))
    catch _ =>
      return none
  let some typeNames := typeNames?
    | return none
  if typeNames.isEmpty then
    return none
  return some {
    identifier := String.Pos.Raw.extract text.source pos tailPos
    openNamespaces := typeNames.map (.allExcept · #[])
    ctx
    determineInsertion decl :=
      {
        fullName := decl
        edit := {
          range := text.utf8RangeToLspRange ⟨pos, tailPos⟩
          newText := decl.getString!
        }
      }
  }

def computeDotIdQuery?
    (doc : EditableDocument)
    (ctx : Elab.ContextInfo)
    (stx : Syntax)
    (id : Name)
    (lctx : LocalContext)
    (expectedType? : Option Expr)
    : IO (Option Query) := do
  let some pos := stx.getPos? (canonicalOnly := true)
    | return none
  let some tailPos := stx.getTailPos? (canonicalOnly := true)
    | return none
  let some expectedType := expectedType?
    | return none
  let typeNames : Array Name ← ctx.runMetaM lctx <| getDotIdCompletionTypeNames expectedType
  if typeNames.isEmpty then
    return none
  return some {
    identifier := id.toString
    openNamespaces := typeNames.map (.allExcept · #[])
    ctx
    determineInsertion decl :=
      {
        fullName := decl
        edit := {
          range := doc.meta.text.utf8RangeToLspRange ⟨pos, tailPos⟩
          newText := decl.getString!
        }
      }
  }

def computeQueries
    (doc          : EditableDocument)
    (requestedPos : String.Pos.Raw)
    : RequestM (Array Query) := do
  let text := doc.meta.text
  let some (stx, infoTree) := RequestM.findCmdDataAtPos doc requestedPos (includeStop := true) |>.get
    | return #[]
  let (completionPartitions, _) := findPrioritizedCompletionPartitionsAt text requestedPos stx infoTree
  let mut queries := #[]
  for partition in completionPartitions do
    for (i, _) in partition do
      let query? ←
        match i.info with
        | .id (stx := stx) (id := id) .. =>
          pure <| computeIdQuery? doc i.ctx stx id
        | .dot (termInfo := ti) .. =>
          computeDotQuery? doc i.ctx ti
        | .dotId stx id lctx expectedType? =>
          computeDotIdQuery? doc i.ctx stx id lctx expectedType?
        | _ =>
          pure none
      if let some query := query? then
        queries := queries.push query
    if ! queries.isEmpty then
      break
  return queries

def importAllUnknownIdentifiersProvider : Name := `allUnknownIdentifiers
def importUnknownIdentifiersProvider : Name := `unknownIdentifiers

def mkUnknownIdentifierCodeActionData (params : CodeActionParams)
    (name := importUnknownIdentifiersProvider) : CodeActionResolveData := {
  params,
  providerName := name
  providerResultIndex := 0
  : CodeActionResolveData
}

def importAllUnknownIdentifiersCodeAction (params : CodeActionParams) (kind : String) : CodeAction := {
  title := "Import all unambiguous unknown identifiers"
  kind? := kind
  data? := some <| toJson <|
    mkUnknownIdentifierCodeActionData params importAllUnknownIdentifiersProvider
}

private def mkImportText (ctx : Elab.ContextInfo) (mod : Name) :
    String := Id.run do
  let mut text := s!"import {mod}\n"
  if let some parentDecl := ctx.parentDecl? then
    if isMarkedMeta ctx.env parentDecl then
      text := s!"meta {text}"
      if !isPrivateName parentDecl then
        -- As `meta` declarations go through a second, stricter visibility check in the compiler,
        -- we should add `public` anywhere in a public definition (technically even private defs
        -- could require public imports but that is not something we can check for here).
        text := s!"public {text}"
    else if ctx.env.isExporting then
      -- Outside `meta`, add `public` only from public scope
      text := s!"public {text}"
  text

def handleUnknownIdentifierCodeAction
    (id             : JsonRpc.RequestID)
    (params         : CodeActionParams)
    (requestedRange : Lean.Syntax.Range)
    (kind           : String)
    : RequestM (Array CodeAction) := do
  let rc ← read
  let doc := rc.doc
  let text := doc.meta.text
  let queries ← computeQueries doc requestedRange.stop
  if queries.isEmpty then
    return #[]
  let responseTask ← RequestM.sendServerRequest LeanQueryModuleParams LeanQueryModuleResponse "$/lean/queryModule" {
    sourceRequestID := id
    queries := queries.map (·.toLeanModuleQuery)
    : LeanQueryModuleParams
  }
  let r ← ServerTask.waitAny [
    responseTask.mapCheap Sum.inl,
    rc.cancelTk.requestCancellationTask.mapCheap Sum.inr
  ]
  let .inl (.success response) := r
    | RequestM.checkCancelled
      return #[]
  let headerStx := doc.initSnap.stx
  let importInsertionPos : Lsp.Position :=
    match headerStx.getTailPos? with
    | some headerTailPos => {
        line := (text.utf8PosToLspPos headerTailPos |>.line) + 1
        character := 0
      }
    | none => { line := 0, character := 0 }
  let importInsertionRange : Lsp.Range := ⟨importInsertionPos, importInsertionPos⟩
  let mut unknownIdentifierCodeActions := #[]
  let mut hasUnambiguousImportCodeAction := false
  let some result := response.queryResults[0]?
    | return #[]
  for query in queries, result in response.queryResults do
    for ⟨mod, decl, isExactMatch⟩ in result do
      let isDeclInEnv := query.ctx.env.contains decl
      if ! isDeclInEnv && mod == query.ctx.env.mainModule then
        -- Don't offer any code actions for identifiers defined further down in the same file
        continue
      let insertion := query.determineInsertion decl
      if ! isDeclInEnv then
        unknownIdentifierCodeActions := unknownIdentifierCodeActions.push {
          title := s!"Import {insertion.fullName} from {mod}"
          kind? := kind
          edit? := WorkspaceEdit.ofTextDocumentEdit {
            textDocument := doc.versionedIdentifier
            edits := #[
              {
                range := importInsertionRange
                newText := mkImportText query.ctx mod
              },
              insertion.edit
            ]
          }
          data? := some <| toJson <| mkUnknownIdentifierCodeActionData params
        }
        if isExactMatch then
          hasUnambiguousImportCodeAction := true
      else
        unknownIdentifierCodeActions := unknownIdentifierCodeActions.push {
          title := s!"Change to {insertion.fullName}"
          kind? := kind
          edit? := WorkspaceEdit.ofTextDocumentEdit {
            textDocument := doc.versionedIdentifier
            edits := #[insertion.edit]
          }
          data? := some <| toJson <| mkUnknownIdentifierCodeActionData params
        }
  if hasUnambiguousImportCodeAction then
    unknownIdentifierCodeActions := unknownIdentifierCodeActions.push <|
      importAllUnknownIdentifiersCodeAction params "quickfix"
  return unknownIdentifierCodeActions

def handleResolveImportAllUnknownIdentifiersCodeAction?
    (id                      : JsonRpc.RequestID)
    (action                  : CodeAction)
    (unknownIdentifierRanges : Array Lean.Syntax.Range)
    : RequestM (Option CodeAction) := do
  let rc ← read
  let doc := rc.doc
  let text := doc.meta.text
  let queries ← unknownIdentifierRanges.flatMapM fun unknownIdentifierRange =>
    computeQueries doc unknownIdentifierRange.stop
  if queries.isEmpty then
    return none
  let responseTask ← RequestM.sendServerRequest LeanQueryModuleParams LeanQueryModuleResponse "$/lean/queryModule" {
    sourceRequestID := id
    queries := queries.map (·.toLeanModuleQuery)
    : LeanQueryModuleParams
  }
  let .success response := responseTask.get
    | return none
  let headerStx := doc.initSnap.stx
  let importInsertionPos : Lsp.Position :=
    match headerStx.getTailPos? with
    | some headerTailPos => {
        line := (text.utf8PosToLspPos headerTailPos |>.line) + 1
        character := 0
      }
    | none => { line := 0, character := 0 }
  let importInsertionRange : Lsp.Range := ⟨importInsertionPos, importInsertionPos⟩
  let mut edits : Array TextEdit := #[]
  let mut imports : Std.HashSet Name := ∅
  for q in queries, result in response.queryResults do
    let some ⟨mod, decl, _⟩ := result.find? fun id =>
        id.isExactMatch && ! q.ctx.env.contains id.decl
      | continue
    if mod == q.ctx.env.mainModule then
      continue
    let insertion := q.determineInsertion decl
    if ! imports.contains mod then
      edits := edits.push {
        range := importInsertionRange
        newText := mkImportText q.ctx mod
      }
    edits := edits.push insertion.edit
    imports := imports.insert mod
  return some { action with
    edit? := WorkspaceEdit.ofTextDocumentEdit {
      textDocument := doc.versionedIdentifier
      edits
    }
  }
