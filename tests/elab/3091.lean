import Lean

open Lean

def foo.{u} : Nat := (ULift.up.{u} Nat.zero).down

universe u in
#eval foo.{u}

-- this used to produce an error
#eval do
  let u : Lean.Level := .param `u
  Meta.evalExpr Nat (.const ``Nat []) (.const ``foo [u])
