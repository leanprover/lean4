/-
Declare a SymExtension and register it.
-/
module
public import Lean.Meta.Sym.SymM
open Lean Meta Sym

/-- Simple counter state for testing. -/
public structure MyExtState where
  counter : Nat := 0
  deriving Inhabited

initialize myExt : SymExtension MyExtState ←
  registerSymExtension (return {})

public def getMyCounter : SymM Nat := do
  return (← myExt.getState).counter

public def incrementMyCounter : SymM Unit := do
  myExt.modifyState fun s => { s with counter := s.counter + 1 }
