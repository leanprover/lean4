import Lean.Elab.Tactic

open Lean Elab Tactic in
elab "print!" : tactic => do
  logInfo "foo"
  throwError "error"

example : True := by
  print!
  admit
