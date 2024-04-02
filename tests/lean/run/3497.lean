import Lean

/--
error: invalid doc string, declaration 'Nat.mul' is in an imported module
-/
#guard_msgs (error) in
#eval show Lean.MetaM Unit from Lean.addDocString `Nat.mul "oh no"
