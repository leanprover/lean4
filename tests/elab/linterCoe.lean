module

-- by default, linters are disabled when running tests
set_option linter.all true

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

/--
warning: This term uses the deprecated coercion `mycoe`.

Note: This linter can be disabled with `set_option linter.deprecatedCoercions false`
-/
#guard_msgs in
def h (foo : X) : Y := foo

/-- -/
notation a " +' " b => a + b

@[deprecated "" (since := "")]
instance : Coe X Int where
  coe _ := 0

/--
@ +1:31...32
warning: This term uses the deprecated coercion `instCoeXInt`.

Note: This linter can be disabled with `set_option linter.deprecatedCoercions false`
---
@ +1:36...37
warning: This term uses the deprecated coercion `instCoeXInt`.

Note: This linter can be disabled with `set_option linter.deprecatedCoercions false`
---
@ +1:41...42
warning: This term uses the deprecated coercion `instCoeXInt`.

Note: This linter can be disabled with `set_option linter.deprecatedCoercions false`
-/
#guard_msgs(positions := true) in
example := fun (n m l : X) => (n + (m +' l) : Int)

set_option linter.deprecatedCoercions false

#guard_msgs in
def h' (foo : X) : Y := foo
