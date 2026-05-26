/-!
# Deprecation warnings for Pi type motives in match expressions

This file tests that Pi type motives emit a deprecation warning.
The preferred style is to use a type family (lambda) instead.
-/

/--
warning: Pi type syntax for match motive is deprecated; use a type family (lambda) instead.
Deprecated: (x : T) → BodyType
Preferred:  fun (x : T) => BodyType
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
warning: Pi type syntax for match motive is deprecated; use a type family (lambda) instead.
Deprecated: (x : T) → BodyType
Preferred:  fun (x : T) => BodyType
-/
#guard_msgs in
def t3fHello (b : Bool) : tNatfString b :=
  match (motive := (b2 : Bool) → tNatfString b2) b with
  | true => (3 : Nat)
  | false => "Hello"
