/-!
This file previously tested some error messages, and now they are regression tests to see
that the test cases succeed.
-/

set_option linter.unusedVariables false

def Nat.bar (x : String) (x : Nat) (y : Nat) := x

/-!
This used to say the `Nat` parameter of `Nat.bar` could not be used.
-/
/-- info: fun x => Nat.bar x Nat.zero : String → Nat → Nat -/
#guard_msgs in
#check Nat.zero.bar

structure F where
  f : Bool → Nat → Nat

def Nat.foo : F := { f := fun _ _ => 0 }

section
local instance : CoeFun F (fun _ => Bool → Nat → Nat) where
  coe x := fun (a : Bool) (b : Nat) => x.f a b

/-!
This used to say the `Nat` parameter of `Nat.foo.f` (coerced from `Nat.foo`) could not be used.
-/
/-- info: fun a => (fun a b => Nat.foo.f a b) a Nat.zero : Bool → Nat -/
#guard_msgs in #check Nat.zero.foo

/-- info: (fun a b => Nat.foo.f a b) true Nat.zero : Nat -/
#guard_msgs in #check Nat.zero.foo true

end

section
local instance : CoeFun F (fun _ => Bool → Nat → Nat) where
  coe x := fun _ _ => 0

/-!
This used to say the `Nat` parameter of `fun x x_1 => 0` (coerced from `Nat.foo`) could not be used.
-/
/-- info: fun x => (fun x x_1 => 0) x Nat.zero : Bool → Nat -/
#guard_msgs in #check Nat.zero.foo

/-- info: (fun x x_1 => 0) true Nat.zero : Nat -/
#guard_msgs in #check Nat.zero.foo true

end
