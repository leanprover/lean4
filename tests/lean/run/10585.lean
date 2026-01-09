def s : String := "4"
example : Option String := s
example : Option String := ("3" : String)
example : Option String := "3"

def n : Nat := 4
example : Option Nat := n
example : Option Nat := (3 : Nat)
example : Option Nat := 3

def d : Float := 4.
example : Option Float := d
example : Option Float := (3. : Float)
example : Option Float := 3.

example : Option (Option (Option Int)) := 7
example : Option UInt8 := 3
example : Option String.Pos := 0

/--
error: failed to synthesize
  OfNat (Option String.Pos) 1
numerals are polymorphic in Lean, but the numeral `1` cannot be used in a context where the expected type is
  Option String.Pos
due to the absence of the instance above

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
example : Option String.Pos := 1

example : Option (Id (Option (Id ISize))) := 6_000
