import Lean.Elab.Command

open Lean Elab Command

def dummyModuleLinter : ModuleLinter where
  run cmds := do
    let ref := cmds[0]?.getD .missing
    logWarningAt ref m!"cmds: {cmds}"

initialize addModuleLinter dummyModuleLinter
