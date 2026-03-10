/-!
# Lambda term motives (type families) in match expressions

This file tests that lambda term motives (type families) are now accepted
in match expressions. This is the preferred style over Pi type motives.
-/

-- Lambda motive (type family) should work without warnings
def t3f5 (b : Bool) : Nat :=
  match (motive := fun (_ : Bool) => Nat) b with
  | true => 3
  | false => 5

-- Verify the definition works correctly
#guard t3f5 true == 3
#guard t3f5 false == 5

-- More complex example with dependent type
def tNatfString (b : Bool) : Type :=
  match b with
  | true => Nat
  | false => String

def t3fHello (b : Bool) : tNatfString b :=
  match (motive := fun (b2 : Bool) => tNatfString b2) b with
  | true => (3 : Nat)
  | false => "Hello"

-- Verify dependent match works by checking the computed value
example : t3fHello true = (3 : Nat) := rfl
example : t3fHello false = "Hello" := rfl
