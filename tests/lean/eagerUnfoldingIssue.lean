import Lean

namespace Lean.Elab

def f1 (x : Nat) : StateM Nat Unit := do
  logInfo m!"{x}"
  pure ()

abbrev M := StateM Nat Unit

def f2 (x : Nat) : M := do
  logInfo m!"{x}"
  pure ()

end Lean.Elab
