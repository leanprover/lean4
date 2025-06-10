import Std.Data.HashSet

set_option linter.unusedVariables true

open Lean

def boo : Id (Std.HashSet Nat) := do
  let mut vs : Std.HashSet Nat := ∅
  for i in List.range 10 do
    /- unused variable `vs` -/
    (_, vs) := (i, vs.insert i)
  return vs
