/-!
This file tests that lambda term motives (type families) are currently rejected
in match expressions. The motive is expected to be a Pi type, not a lambda term.
-/

/--
 error: type expected, got
  (fun x => Nat : Bool → Type)
-/
#guard_msgs in
def t3f5 (b : Bool) : Nat :=
  match (motive := fun (_ : Bool) => Nat) b with
  | true => 3
  | false => 5
