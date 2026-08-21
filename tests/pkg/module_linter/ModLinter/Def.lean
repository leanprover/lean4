import Lean.Elab.Command
import Lean.Linter.Util

open Lean Elab Command

def dummyModuleLinter : ModuleLinter where
  run cmds := do
    let ref := cmds[0]?.getD .missing
    logWarningAt ref m!"cmds: {cmds}"

def myLinter : Linter where
  run stx := do
    if let some decl := (← Linter.findMatchingDecl? stx) then
      logInfoAt stx m!"best match is: {decl}"

initialize addModuleLinter dummyModuleLinter
initialize addLinter myLinter
