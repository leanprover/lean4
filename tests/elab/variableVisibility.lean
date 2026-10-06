module

/-!
Tests that the `private`/`public` modifiers on `variable` are accepted.
-/

private variable (x : Nat)
public variable (y : Nat)

def usesVars := x + y

/-- info: usesVars (x y : Nat) : Nat -/
#guard_msgs in
#check usesVars
