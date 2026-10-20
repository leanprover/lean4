import Lean

/-! A stateful linter that attaches a `Try this` suggestion to the `#suggestMark` command in each of
its `pre` and `post` passes. Checks that stateful linters can emit code-action suggestions and that
both passes contribute. The suggestions are observed here as their `Try this` messages; the info-tree
splicing that feeds the code-action provider is shared with ordinary linters and exercised by the
interactive tests. -/

namespace LinterTest.Suggest
open Lean Elab Command Lean.Meta.Tactic.TryThis

/-- Marker command the suggestion linter attaches `Try this` code actions to. -/
syntax (name := suggestMark) "#suggestMark" : command

elab_rules : command
  | `(#suggestMark) => pure ()

initialize _suggestLinter : StatefulLinter Unit Unit ←
  registerStatefulLinter ()
    (pre := fun stx _ _ => do
      if stx.isOfKind ``suggestMark then
        liftCoreM <| addSuggestion stx { suggestion := "#eval 0" }
      pure none)
    (post := fun stx _ _ _ _ => do
      if stx.isOfKind ``suggestMark then
        liftCoreM <| addSuggestion stx { suggestion := "#eval 1" }
      pure ())
