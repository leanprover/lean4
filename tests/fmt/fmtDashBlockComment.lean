module

/-!
Tests that the formatter keeps the space after the opening of a block comment that consists only of
dashes: without it, the comment would start like a doc comment and become one.
-/

#check 1

/- ----- -/

/-- info: 2 : Nat -/
#guard_msgs in
#check 2

def a :=   /- -- -/ 1

/-      -     -/
def b := 2
