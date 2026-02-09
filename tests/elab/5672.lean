/-!
# `instance` creates a theorem if the class is a `Prop`

https://github.com/leanprover/lean4/issues/5672
-/

class A : Prop

instance a : A where

/--
info: theorem a : A :=
{ }
-/
#guard_msgs in #print a


/-!
Uses `def` variable inclusion rules
-/
section
variable (x : Nat)
instance b : A := by
  cases x <;> exact {}
/-- info: b (x : Nat) : A -/
#guard_msgs in #check b
end
