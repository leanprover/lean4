import Lean
open Lean

abbrev M := StateRefT Nat IO

def M.run (x : M α) (s := 0) : IO α :=
  x.run' s

variable (x : M Unit)

#check id x.run
