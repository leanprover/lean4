import Lean

/-!
Measures the first library-suggestions query in a process, which prepares the Sine Qua Non
indexes for the whole imported library, and a second query that reuses them.
-/

set_library_suggestions Lean.LibrarySuggestions.sineQuaNonSelector

-- Keep the two queries in order, so that only the first one sees cold caches.
set_option Elab.async false

open Lean Elab Tactic in
elab "measure_tac " name:ident t:tactic : tactic => do
  let start ← IO.monoNanosNow
  evalTactic t
  let stop ← IO.monoNanosNow
  IO.println s!"measurement: {name.getId} {(stop - start).toFloat / 1e9} s"

example {x : Dyadic} {prec : Int} : x.roundDown prec ≤ x := by
  measure_tac cold_query grind +suggestions

example {x : Dyadic} {prec : Int} : x.roundDown prec ≤ x := by
  measure_tac warm_query grind +suggestions
