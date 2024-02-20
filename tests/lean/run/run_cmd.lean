import Lean
open Lean Elab Tactic

run_cmd logInfo m!"hello world"

run_cmd unsafe do logInfo "!"

example : True := by
  run_tac
    evalApplyLikeTactic MVarId.apply (← `(True.intro))

example : True := by_elab
  Term.elabTerm (← `(True.intro)) none
