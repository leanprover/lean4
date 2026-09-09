import Lean

/-!
Checks that `Try this` suggestions emitted by a linter surface as `textDocument/codeAction` code
actions.
-/

set_option Elab.async true

open Lean Lean.Elab.Command Lean.Meta.Tactic.TryThis

syntax (name := normalMark) "#normalMark" : command

@[command_elab normalMark] def elabNormalMark : CommandElab := fun _ => pure ()

def normalLinter : Linter where
  run stx := do
    if stx.isOfKind ``normalMark then
      liftCoreM <| addSuggestion stx { suggestion := "#eval 0" }

run_cmd liftCoreM <| addLinter normalLinter

#normalMark
--^ codeAction
