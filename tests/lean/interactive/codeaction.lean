import Lean

open Lean Server Lsp

@[codeActionProvider]
def helloProvider : CodeActionProvider := fun (params : CodeActionParams) => do
  let uri := params.textDocument.uri
  return RequestTask.pure #[{
    title := "hello world",
    kind? := "quickfix",
    edit? := WorkspaceEdit.ofTextEdit uri {
      range := params.range,
      newText := "hello!!!",
    },
    data := {uri}
  }]

theorem asdf : (x : Nat) → x = x := by
  intro x
  --^ codeAction
  rfl
