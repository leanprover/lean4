import Lean.Elab.Command
import Lean.Linter.Util

/-! A linter that reports the declaration `Linter.findMatchingDecl?` associates with each
command it runs on. -/

open Lean Elab Command

def matchingDeclLinter : Linter where
  run stx := do
    if let some decl := (← Linter.findMatchingDecl? stx) then
      logInfoAt stx m!"best match is: {decl}"

initialize addLinter matchingDeclLinter
