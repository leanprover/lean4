import Lean.LibrarySuggestions.MePo

/-!
Regression test: the MePo premise selector filters candidates to theorems
(matching the convention already used by `SineQuaNon` and `SymbolFrequency`)
and finds the obvious lemma for an arithmetic equality goal.

Output is ordered by `(iteration, score, overlap)` rather than by score alone,
so the score sequence is not globally monotonic — a score jump signals an
iteration boundary. The overlap tie-breaker keeps generic one-symbol theorems
from outranking more specific lemmas with the same MePo score.
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
    match names.findIdx? (· == ``Int.add_comm), names.findIdx? (· == ``Eq.symm) with
    | some i, some j =>
      unless i < j do
        throwError "Int.add_comm should rank before generic Eq.symm when both \
          have the same MePo score"
    | none, _ =>
      throwError "Int.add_comm should appear in the MePo suggestions for `a + b = b + a`"
    | _, none =>
      throwError "Eq.symm should appear in the MePo suggestions for this regression test"
  sorry
