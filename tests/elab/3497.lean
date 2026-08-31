import Lean

open Lean Elab Term

/--
error: invalid doc string, declaration `Nat.mul` is in an imported module
-/
#guard_msgs (error) in
#eval show TermElabM Unit from do addDocString `Nat.mul mkNullNode (← `(docComment| /-- oh no -/))
