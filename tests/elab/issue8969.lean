import Lean

open Lean Elab Meta Tactic

syntax (name := nontriviality) "nontriviality" Parser.Tactic.simpArg,+ : tactic

@[tactic nontriviality] def elabNontriviality : Tactic := fun stx => do
  let simpArgs := stx[1].getSepArgs
  let stx := open TSyntax.Compat in Unhygienic.run `(tactic| simp [$simpArgs,*])
  let ([], _) ← runTactic (← getMainGoal) stx | failure

example : True ∧ True := by
  nontriviality id_eq
