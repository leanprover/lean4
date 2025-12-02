module

structure X
structure Y

@[deprecated "" (since := "")]
instance mycoe : Coe X Y where coe _ := ⟨⟩

/-- warning: This term uses the coercion `optionCoe`, which is banned in Lean's core library. -/
#guard_msgs in
def f : Option String := "hi"

/--
warning: This term uses the coercion `instCoeSubarrayArray`, which is banned in Lean's core library.
-/
#guard_msgs in
def g : Array Nat := #[1, 2, 3][*...*]

/-- warning: This term uses the deprecated coercion `mycoe`. -/
#guard_msgs in
def h (foo : X) : Y := foo

set_option linter.deprecatedCoercions false

#guard_msgs in
def h' (foo : X) : Y := foo
