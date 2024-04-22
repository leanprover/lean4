import Lean

open Lean Server Lsp RequestM

@[code_action_provider]
def helloProvider : CodeActionProvider := fun params _snap => do
  let doc ← readDoc
  let vi := doc.versionedIdentifier
  let edit : TextEdit := {
      range := params.range,
      newText := "hello!!!"
    }
  let ca : CodeAction := {
    title := "hello world",
    kind? := "quickfix",
    edit? := WorkspaceEdit.ofTextEdit vi edit
  }
  let longRunner : CodeAction := {
    title := "a long-running action",
    kind? := "refactor",
  }
  let lazyResult : IO CodeAction := do
    let v? ← IO.getEnv "PWD"
    let v := v?.getD "none"
    return { longRunner with
      edit? := WorkspaceEdit.ofTextEdit vi { range := params.range, newText := v}
    }
  return #[ca, {eager := longRunner, lazy? := lazyResult}]

theorem asdf : (x : Nat) → x = x := by
  intro x
  --^ codeAction
  rfl
