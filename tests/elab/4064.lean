import Lean

def test : Lean.CoreM (List Lean.Name) := do
  let .thmInfo tval ← Lean.getConstInfo `And.left | unreachable!
  return tval.all

/--
info: [`And.left]
-/
#guard_msgs in
#eval test
