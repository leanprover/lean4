import Lean
open Lean

def test (declName : Name) : MetaM Unit := do
  if isNoncomputable (← getEnv) declName then
    IO.println s!"{declName} is marked as noncomputable"
  else
    IO.println s!"{declName} is not marked as noncomputable"

noncomputable def foo (x : Nat) : Nat :=
  x + Classical.ofNonempty

#eval test ``List.map
#eval test ``foo
#eval test ``Classical.ofNonempty
#eval test ``Array.map
