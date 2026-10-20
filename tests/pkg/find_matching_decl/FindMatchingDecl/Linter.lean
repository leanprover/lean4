import Lean.Elab.Command
import Lean.Linter.Util

/-! A linter that reports the declaration `Linter.findMatchingDecl?` associates with each
command it runs on, and the code-quality source derived from it by
`Linter.findCodeQualitySource` and `Linter.findCodeQualitySource?`. -/

open Lean Elab Command

def matchingDeclLinter : Linter where
  run stx := do
    if let some decl := (← Linter.findMatchingDecl? stx) then
      logInfoAt stx m!"best match is: {decl}"
    let src ← Linter.findCodeQualitySource stx
    let src? ← Linter.findCodeQualitySource? stx
    -- `compress` keeps each message on one line so the test can grep for it
    logInfoAt stx m!"source: {(toJson src).compress}; source?: {(toJson src?).compress}"

initialize addLinter matchingDeclLinter
