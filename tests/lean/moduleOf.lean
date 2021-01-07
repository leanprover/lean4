import Lean

def f (x : Nat) := x + x

open Lean

def tst : MetaM Unit := do
  IO.println (← getModuleOf `HAdd.hAdd)
  IO.println (← getModuleOf `Lean.Core.CoreM)
  IO.println (← getModuleOf `Lean.Elab.Term.elabTerm)
  IO.println (← getModuleOf `Std.HashMap.insert)
  IO.println (← getModuleOf `tst)
  IO.println (← getModuleOf `f)
  IO.println (← getModuleOf `foo) -- Error: unknown 'foo'

#eval tst
