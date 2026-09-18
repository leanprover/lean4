import Lean.Cadical


open Lean.Cadical

def test : IO Unit := do
  let s ← Solver.new
  IO.println (← s.status)
  s.clause (Std.Sat.CNF.Clause.ofLiterals [⟨1, true⟩, ⟨2, true⟩])
  s.clause (Std.Sat.CNF.Clause.ofLiterals [⟨1, true⟩, ⟨2, false⟩])
  s.clause (Std.Sat.CNF.Clause.ofLiterals [⟨1, false⟩, ⟨2, false⟩])
  let status ← s.solve
  IO.println status
  IO.println s!"1: {← s.val 1}, 2: {← s.val 2}"
  s.clause (Std.Sat.CNF.Clause.ofLiterals [⟨1, false⟩, ⟨2, true⟩])
  let status ← s.solve
  IO.println status

#eval test
