import Lean

open Lean
def f (xs : List String) : CoreM (Array String) := do
  let mut found : RBMap _ _ compare := {}
  let mut result := #[]
  for x in xs do
    unless found.contains x do
      result := result.push x
      found := found.insert x ()
  return result
