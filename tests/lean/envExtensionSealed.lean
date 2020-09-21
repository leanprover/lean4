import Lean

namespace Lean

def ex1 : CoreM Nat := do
env ← getEnv;
pure $ privateExt.getState env

#eval ex1

def ex2 : CoreM Nat := do
env ← getEnv;
pure $ { privateExt with idx := 3 }.getState env  -- Error

#eval ex2

end Lean
