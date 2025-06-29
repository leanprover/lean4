/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Std.Sat.CNF.Basic
import Std.Sat.CNF.RelabelFin

namespace Std
namespace Sat

namespace CNF

private structure DimacsState where
  numClauses : Nat := 0
  maxLit : Nat := 0

private abbrev DimacsM := StateM DimacsState

namespace DimacsM

@[inline]
private def handleLit (lit : Literal Nat) : DimacsM Unit := do
  modify fun s => { s with maxLit := Nat.max s.maxLit lit.1 }

@[inline]
private def incrementClauses : DimacsM Unit := do
  modify fun s => { s with numClauses := s.numClauses + 1 }

end DimacsM

/--
This function turns `cnf` into a DIMACS `String`.

Note: This function will add `1` to all literal identifiers by default. This is because `0` is an
illegal identifier in the DIMACS format and we can avoid producing invalid DIMACs like this.
-/
def dimacs (cnf : CNF Nat) : String :=
  let (str, state) := go cnf |>.run {}
  s!"p cnf {state.maxLit + 1} {state.numClauses}\n" ++ str
where
  go (cnf : CNF Nat) : DimacsM String := do
    let foldLit acc lit := do
      DimacsM.handleLit lit
      let litStr := if lit.2 then s!"{lit.1 + 1}" else s!"-{lit.1 + 1}"
      return acc ++ litStr |>.push ' '
    let foldClause acc clause := do
      DimacsM.incrementClauses
      return (← clause.foldlM (init := acc) foldLit) |>.push '0' |>.push '\n'
    cnf.foldlM (init := "") foldClause

end CNF

end Sat
end Std
