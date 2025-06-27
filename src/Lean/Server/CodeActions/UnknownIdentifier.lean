/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Huisinga
-/
prelude
import Lean.Server.FileWorker.Utils
import Lean.Data.Lsp.Internal
import Lean.Server.Requests
import Lean.Server.Completion.CompletionInfoSelection
import Lean.Server.CodeActions.Basic
import Lean.Server.Completion.CompletionUtils

namespace Lean.Server.FileWorker

open Lean.Lsp
open Lean.Server.Completion

structure UnknownIdentifierInfo where
  paramsRange : String.Range
  diagRange   : String.Range

def waitUnknownIdentifierRanges (doc : EditableDocument) (requestedRange : String.Range)
    : BaseIO (Array String.Range) := do
  let text := doc.meta.text
  let some parsedSnap := RequestM.findCmdParsedSnap doc requestedRange.start |>.get
    | return #[]
  let msgLog := Language.toSnapshotTree parsedSnap.elabSnap |>.collectMessagesInRange requestedRange |>.get
  let mut ranges := #[]
  for msg in msgLog.unreported do
    if ! msg.data.hasTag (· == unknownIdentifierMessageTag) then
      continue
    let msgRange : String.Range := ⟨text.ofPosition msg.pos, text.ofPosition <| msg.endPos.getD msg.pos⟩
    if ! msgRange.overlaps requestedRange
        (includeFirstStop := true) (includeSecondStop := true) then
      continue
    ranges := ranges.push msgRange
  return ranges

def waitAllUnknownIdentifierRanges (doc : EditableDocument)
    : BaseIO (Array String.Range) := do
  let text := doc.meta.text
  let msgLog : MessageLog := Language.toSnapshotTree doc.initSnap
    |>.getAll.map (·.diagnostics.msgLog)
    |>.foldl (· ++ ·) {}
  let mut ranges := #[]
  for msg in msgLog.unreported do
    if ! msg.data.hasTag (· == unknownIdentifierMessageTag) then
      continue
    let msgRange : String.Range := ⟨text.ofPosition msg.pos, text.ofPosition <| msg.endPos.getD msg.pos⟩
    ranges := ranges.push msgRange
  return ranges

structure Insertion where
  fullName : Name
  edit     : TextEdit

structure Query extends LeanModuleQuery where
  env                : Environment
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
    env := ctx.env
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
    identifier := text.source.extract pos tailPos
    openNamespaces := typeNames.map (.allExcept · #[])
    env := ctx.env
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
  let typeNames? : Option (Array Name) ← ctx.runMetaM lctx do
    let resultTypeFn := (← instantiateMVars expectedType).cleanupAnnotations.getAppFn.cleanupAnnotations
    let .const .. := resultTypeFn
      | return none
    try
      return some <| ← getDotCompletionTypeNames resultTypeFn
    catch _ =>
      return none
  let some typeNames := typeNames?
    | return none
  return some {
    identifier := id.toString
    openNamespaces := typeNames.map (.allExcept · #[])
    env := ctx.env
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
    (requestedPos : String.Pos)
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

def importAllUnknownIdentifiersProvider : Name := `unknownIdentifiers

def importAllUnknownIdentifiersCodeAction (params : CodeActionParams) (kind : String) : CodeAction := {
  title := "Import all unambiguous unknown identifiers"
  kind? := kind
  data? := some <| toJson {
    params,
    providerName := importAllUnknownIdentifiersProvider
    providerResultIndex := 0
    : CodeActionResolveData
  }
}

def handleUnknownIdentifierCodeAction
    (id             : JsonRpc.RequestID)
    (params         : CodeActionParams)
    (requestedRange : String.Range)
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
  let mut hasUnambigiousImportCodeAction := false
  let some result := response.queryResults[0]?
    | return #[]
  for query in queries, result in response.queryResults do
    for ⟨mod, decl, isExactMatch⟩ in result do
      let isDeclInEnv := query.env.contains decl
      if ! isDeclInEnv && mod == query.env.mainModule then
        -- Don't offer any code actions for identifiers defined further down in the same file
        continue
      let insertion := query.determineInsertion decl
      if ! isDeclInEnv then
        unknownIdentifierCodeActions := unknownIdentifierCodeActions.push {
          title := s!"Import {insertion.fullName} from {mod}"
          kind? := "quickfix"
          edit? := WorkspaceEdit.ofTextDocumentEdit {
            textDocument := doc.versionedIdentifier
            edits := #[
              {
                range := importInsertionRange
                newText := s!"import {mod}\n"
              },
              insertion.edit
            ]
          }
        }
        if isExactMatch then
          hasUnambigiousImportCodeAction := true
      else
        unknownIdentifierCodeActions := unknownIdentifierCodeActions.push {
          title := s!"Change to {insertion.fullName}"
          kind? := "quickfix"
          edit? := WorkspaceEdit.ofTextDocumentEdit {
            textDocument := doc.versionedIdentifier
            edits := #[insertion.edit]
          }
        }
  if hasUnambigiousImportCodeAction then
    unknownIdentifierCodeActions := unknownIdentifierCodeActions.push <|
      importAllUnknownIdentifiersCodeAction params "quickfix"
  return unknownIdentifierCodeActions

def handleResolveImportAllUnknownIdentifiersCodeAction?
    (id                      : JsonRpc.RequestID)
    (action                  : CodeAction)
    (unknownIdentifierRanges : Array String.Range)
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
        id.isExactMatch && ! q.env.contains id.decl
      | continue
    if mod == q.env.mainModule then
      continue
    let insertion := q.determineInsertion decl
    if ! imports.contains mod then
      edits := edits.push {
        range := importInsertionRange
        newText := s!"import {mod}\n"
      }
    edits := edits.push insertion.edit
    imports := imports.insert mod
  return some { action with
    edit? := WorkspaceEdit.ofTextDocumentEdit {
      textDocument := doc.versionedIdentifier
      edits
    }
  }
