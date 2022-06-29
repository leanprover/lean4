import Lean

open Lean Elab Command

#eval do
  let id := mkIdent `foo
  elabCommand (← `(def $id := 10))

example : foo = 10 := rfl

#eval do
  let id := mkIdent `boo
  elabCommand (← `(def $id := false))
  return 5

example : boo = false := rfl
