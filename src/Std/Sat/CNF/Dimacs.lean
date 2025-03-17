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

def Literal.dimacs (lit : Literal Nat) : String :=
  let ⟨id, pol⟩ := lit
  let id := id + 1 -- DIMACS does not allow 0 as identifier

  if pol then
    s!"{id}"
  else
    s!"-{id}"

namespace CNF

def Clause.dimacs (clause : Clause Nat) : String :=
  clause.foldl (init := "") (· ++ ·.dimacs ++ " ") ++ "0"

/--
This function turns `cnf` into a DIMACS `String`.

Note: This function will add `1` to all literal identifiers by default. This is because `0` is an
illegal identifier in the DIMACS format and we can avoid producing invalid DIMACs like this.
-/
def dimacs (cnf : CNF Nat) : String :=
  let numClauses := cnf.length
  let maxIdentifier := (cnf.maxLiteral |>.getD 0) + 1
  let base := s!"p cnf {maxIdentifier} {numClauses}\n"
  cnf.foldl (init := base) (· ++ ·.dimacs ++ "\n")

end CNF

end Sat
end Std
