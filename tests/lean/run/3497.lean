import Lean

/-- error: invalid doc string, declaration `Nat.mul` is in an imported module -/
#guard_msgs (error) in
#eval show Lean.MetaM Unit from do Lean.addDocString `Nat.mul (← `(docComment| /-- oh no -/))
