
set_option linter.unusedVariables false

def Nat.bar (x : String) (x : Nat) (y : Nat) := x

/--
error: Invalid field notation: `Nat.bar` has a parameter with expected type
  Nat
but it cannot be used

Note: The parameter `x` cannot be referred to by name because that function has a preceding parameter of the same name

Hint: Consider rewriting this application without field notation (e.g., `C.f x` instead of `x.f`) or changing the parameter names of the function to avoid this conflict
-/
#guard_msgs in
#check Nat.zero.bar

structure F where
  f : Bool → Nat → Nat

def Nat.foo : F := { f := fun _ _ => 0 }

section
local instance : CoeFun F (fun _ => Bool → Nat → Nat) where
  coe x := fun (a : Bool) (b : Nat) => x.f a b

/--
error: Invalid field notation: `Nat.foo.f` (coerced from `Nat.foo`) has a parameter with expected type
  Nat
but it cannot be used

Note: Field notation cannot refer to parameter `b` by name because that constant was coerced to a function

Hint: Consider rewriting this application without field notation (e.g., `C.f x` instead of `x.f`)
-/
#guard_msgs in #check Nat.zero.foo

/-- info: (fun a b => Nat.foo.f a b) true Nat.zero : Nat -/
#guard_msgs in #check Nat.zero.foo true

end

section
local instance : CoeFun F (fun _ => Bool → Nat → Nat) where
  coe x := fun _ _ => 0

/--
error: Invalid field notation: `fun x x_1 => 0` (coerced from `Nat.foo`) has a parameter with expected type
  Nat
but it cannot be used

Hint: Consider rewriting this application without field notation (e.g., `C.f x` instead of `x.f`)
-/
#guard_msgs in #check Nat.zero.foo

/-- info: (fun x x_1 => 0) true Nat.zero : Nat -/
#guard_msgs in #check Nat.zero.foo true

end
