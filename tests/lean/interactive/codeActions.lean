import Lean.Server.CodeActions

open Lean.Server

@[code_action_provider] def foo : Lean.Server.CodeActionProvider := fun _ snap => do
  let doc ← RequestM.readDoc
  let some range := snap.stx.getRange?
    | return #[]
  return #[{
    eager := {
      title := "foo"
      kind? := "quickfix"
      edit? := some <| .ofTextEdit doc.versionedIdentifier {
        newText := "foo"
        range := doc.meta.text.utf8RangeToLspRange range
      }
    }
  }]

syntax (name := barCmd) "#bar" : command

macro_rules
  | `(#bar) => `(#eval 0)

@[command_code_action barCmd] def bar : Lean.CodeAction.CommandCodeAction := fun _ _ _ i  => do
  let doc ← RequestM.readDoc
  let some (.ofCommandInfo ci) := i.findInfo? (· matches .ofCommandInfo ..)
    | return #[]
  let some range := ci.stx.getRange?
    | return #[]
  return #[{
    eager := {
      title := "bar"
      kind? := "quickfix"
      edit? := some <| .ofTextEdit doc.versionedIdentifier {
        newText := "#eval 0"
        range := doc.meta.text.utf8RangeToLspRange range
      }
    }
  }]

@[hole_code_action] def foobar : Lean.CodeAction.HoleCodeAction := fun _ _ _ hole => do
  let doc ← RequestM.readDoc
  let some range := hole.stx.getRange?
    | return #[]
  return #[{
    eager := {
      title := "foobar"
      kind? := "quickfix"
      edit? := some <| .ofTextEdit doc.versionedIdentifier {
        newText := "\"foobar\""
        range := doc.meta.text.utf8RangeToLspRange range
      }
    }
  }]

def f : Nat := 0
  --^ codeAction

#bar
--^ codeAction

example : Nat := _
                --^ codeAction
