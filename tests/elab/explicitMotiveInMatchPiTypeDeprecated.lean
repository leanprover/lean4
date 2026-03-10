/-!
# Pi type motives in match expressions are no longer supported

This file tests that Pi type motives emit an error.
The correct style is to use a type family (lambda) instead.
-/

/--
error: Invalid motive: expected a type family (lambda) with arity 1
-/
#guard_msgs in
def t3f5 (b : Bool) : Nat :=
  match (motive := (_ : Bool) → Nat) b with
  | true => 3
  | false => 5

def tNatfString (b : Bool) : Type :=
  match b with
  | true => Nat
  | false => String

/--
error: Invalid motive: expected a type family (lambda) with arity 1
-/
#guard_msgs in
def t3fHello (b : Bool) : tNatfString b :=
  match (motive := (b2 : Bool) → tNatfString b2) b with
  | true => (3 : Nat)
  | false => "Hello"
