import Lean.LibrarySuggestions.MePo

/-!
Regression test: the MePo premise selector filters candidates to theorems
(matching the convention already used by `SineQuaNon` and `SymbolFrequency`)
and finds the obvious lemma for an arithmetic equality goal.

Output is ordered by `(iteration, score)` rather than by score alone, so the
score sequence is not globally monotonic — a score jump signals an iteration
boundary.
-/

open Lean Lean.Elab.Tactic Lean.LibrarySuggestions

example (a b : Int) : a + b = b + a := by
  run_tac do
    let sel : Selector := mepoSelector (useRarity := false)
    let s ← sel (← getMainGoal) {}
    let names := s.map (·.name)
    if names.contains ``Eq.ndrec then
      throwError "Eq.ndrec (a recursor) should be filtered out by the theorem-only \
        accept filter"
    if names.contains ``Int.add then
      throwError "Int.add (a function) should be filtered out by the theorem-only \
        accept filter"
    unless names.contains ``Int.add_comm do
      throwError "Int.add_comm should appear in the MePo suggestions for `a + b = b + a`"
  sorry
