syntax "a" num : term

macro_rules
  | `(a 0) => `("zero")
  | `(a 1) => `("one")

#check a 1

syntax "b" str : term

open Lean
example : Syntax → Nat := fun stx => match stx with
  | `(b "foo") => 0
  | `(b "bla") => 1

#check b "bla"
