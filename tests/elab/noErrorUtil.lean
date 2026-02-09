import Lean

-- Check that private functionality from Lean.Elab.ErrorUtils isn't exported

/-- error: Unknown constant `Nat.toOrdinal` -/
#guard_msgs in
#check Nat.toOrdinal

/--
error: Invalid field `toOxford`: The environment does not contain `List.toOxford`, so it is not possible to project the field `toOxford` from an expression
  ["a", "b", "c", "d"]
of type `List String`
-/
#guard_msgs in
#check ["a", "b", "c", "d"].toOxford
