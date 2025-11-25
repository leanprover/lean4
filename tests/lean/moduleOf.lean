import Lean

def f (x : Nat) := x + x

open Lean

def tst : MetaM Unit := do
  IO.println (← findModuleOf? `HAdd.hAdd)
  IO.println (← findModuleOf? `Lean.Core.CoreM)
  IO.println (← findModuleOf? `Lean.Elab.Term.elabTerm)
  IO.println (← findModuleOf? `Std.HashMap.insert)
  IO.println (← findModuleOf? `tst)
  IO.println (← findModuleOf? `f)
  IO.println (← findModuleOf? `foo) -- Error: unknown 'foo'

#eval tst
