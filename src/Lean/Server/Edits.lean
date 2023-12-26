/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: E.W.Ayers
-/
import Lean.Data.Lsp
import Lean.Syntax
import Lean.Server.Utils
import Lean.Server.InfoUtils
import Lean.Widget
import Lean.Server.CodeActions

/-! Utilities for editing syntax. -/

namespace Lean.Server

open Lean Syntax Elab Server Lsp Snapshots

structure EditSuggestion where
  /-- Original syntax to be replaced. -/
  stx : Syntax
  replacement : Syntax
  description? : Option String := none
  kind : String := "try-this" -- [todo] use CodeActionKind -- perhaps a different string for filling holes?
  /-- Used to render the tactic state after the suggestion has been applied. -/
  stateAfter? : Option (MetavarContext × List MVarId) := none
namespace EditSuggestion

deriving instance TypeName for EditSuggestion

def toInfo (e : EditSuggestion) : Info :=
  Info.ofCustomInfo {stx := e.stx, value := Dynamic.mk e}

def ofInfo? : Info → Option EditSuggestion
  | Info.ofCustomInfo i => i.value.get? _
  | _ => none

variable [Monad m] [MonadInfoTree m] in
def save (e : EditSuggestion) : m Unit := do
  pushInfoLeaf e.toInfo

end EditSuggestion

def InfoTree.getEditSuggestions (t : InfoTree) (hoverPos : String.Pos) : List EditSuggestion :=
  t.collectNodesBottomUp fun _ i _cs rs => Id.run do
    if i.occursInside? hoverPos |>.isSome then
      if let some e := EditSuggestion.ofInfo? i then
        return e :: rs
    return rs

/-- Convert a syntax diff to an Lsp TextEditSuggestion. -/
def replace (cat : Name := `term) (text : FileMap) (orig replacement : Syntax) : CoreM TextEdit := do
  let some range := orig.getRange?
    | throwError "original syntax must be non-synthetic."
  let range := range.toLspRange text
  let newText ← Lean.PrettyPrinter.ppCategory cat replacement
  return {
    range := range
    newText := newText.pretty
  }

/-- Structure that is sent to the client to show suggestions in the infoview. -/
structure EditSuggestionResponse where
  title : String
  description? : Option String := none
  goalsAfter? : Option Widget.InteractiveGoals := none
  edit : WorkspaceEdit
  kind : String := "try-this"
  deriving RpcEncodable

structure EditSuggestionsParams extends TextDocumentPositionParams
  deriving FromJson, ToJson, RpcEncodable

open RequestM

def collectEditSuggestions (snap : Snapshot) (param : TextDocumentPositionParams) (f : ContextInfo → EditSuggestion → RequestM α) : RequestM  (Array α) := do
  let doc ← readDoc
  let text := doc.meta.text
  let hoverPos := text.lspPosToUtf8Pos param.position
  let results ← snap.infoTree.collectNodesM fun ci i => do
    if i.occursInside? hoverPos |>.isSome then
      if let some e := EditSuggestion.ofInfo? i then
        let r ← f ci e
        return (some r)
    return none
  return results.toArray

def getEditSuggestions (param : EditSuggestionsParams) : RequestM (RequestTask (Array EditSuggestionResponse)) := do
  let doc ← readDoc
  let text := doc.meta.text
  let hoverPos := text.lspPosToUtf8Pos param.position
  withWaitFindSnap doc (fun s => s.endPos >= hoverPos)
    (notFoundX := return #[])
    fun snap =>
      collectEditSuggestions snap param.toTextDocumentPositionParams fun ci e => do
        let goalsAfter? ← e.stateAfter?.mapM (fun (mctx, goals) => do
          let ci : ContextInfo := { ci with mctx := mctx }
          let igs : Widget.InteractiveGoals ← ci.runMetaM {} <| Widget.goalsToInteractive goals.toArray
          return igs
        )
        let title ← runCoreM snap <| liftM <| Lean.PrettyPrinter.ppCategory `tactic e.replacement
        let edit : TextEdit ← runCoreM snap <| liftM <| replace (cat := `tactic) text e.stx e.replacement
        let r : EditSuggestionResponse := {
          title := title.pretty,
          edit := WorkspaceEdit.ofTextEdit doc.meta.uri edit,
          goalsAfter? := goalsAfter?
        }
        return r

builtin_initialize
  registerBuiltinRpcProcedure
    `Lean.Widget.getEditSuggestions
    EditSuggestionsParams
    (Array EditSuggestionResponse)
    getEditSuggestions

open Lean Server

-- @[codeActionProvider]
def editSuggestionCodeActions : CodeActionProvider := fun params snap => do
  let doc ← readDoc
  let text := doc.meta.text
  let tdpp : TextDocumentPositionParams := {
    textDocument := params.textDocument,
    position := params.range.start,
  }
  collectEditSuggestions snap tdpp fun _ci e => do
    let title ← runCoreM snap <| liftM <| Lean.PrettyPrinter.ppCategory `tactic e.replacement
    let edit : TextEdit ← runCoreM snap <| liftM <| replace (cat := `tactic) text e.stx e.replacement
    let r : CodeAction := {
      title := title.pretty,
      kind? := e.kind
      edit? := WorkspaceEdit.ofTextEdit params.textDocument.uri edit
    }
    return r

end Lean.Server
