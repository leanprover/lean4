import Lean

namespace Lean.Elab

def f1 (x : Nat) : MetaM Unit := do
  logInfo m!"{x}"
  pure ()

abbrev M := MetaM Unit

def f2 (x : Nat) : M := do
  logInfo m!"{x}"
  pure ()

end Lean.Meta
