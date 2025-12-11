set_option autoImplicit false

/--
error: Unknown identifier `ℕ`

Note: It is not possible to treat `ℕ` as an implicitly bound variable here because the `autoImplicit` option is set to `false`.

Hint: Perhaps you meant `Nat` in place of `ℕ`:
  [apply] `Nat`
-/
#guard_msgs in example : ℕ := 3

/--
error: Unknown identifier `Result`

Note: It is not possible to treat `Result` as an implicitly bound variable here because the `autoImplicit` option is set to `false`.

Hint: Perhaps you meant `Except` in place of `Result`:
  [apply] `Except`
-/
#guard_msgs in example : Result String Nat := .ok 3

set_option autoImplicit true

-- The suggestion infrastructure doesn't help us here due to autobinding
/--
error: failed to synthesize instance of type class
  OfNat ℕ 3
numerals are polymorphic in Lean, but the numeral `3` cannot be used in a context where the expected type is
  ℕ
due to the absence of the instance above

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in example : ℕ := 3

/--
@ +0:45...62
error: Function expected at
  Result
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  String

Hint: The identifier `Result` is unknown, and Lean's `autoImplicit` option causes an unknown identifier to be treated as an implicitly bound variable with an unknown type. However, the unknown type cannot be a function, and a function is what Lean expects here. This is often the result of a typo or a missing `import` or `open` statement.

Perhaps you meant `Except` in place of `Result`?
-/
#guard_msgs (positions := true) in example : Result String Nat := .ok 3

/--
@ +0:45...62
error: Function expected at
  Either
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  String

Hint: The identifier `Either` is unknown, and Lean's `autoImplicit` option causes an unknown identifier to be treated as an implicitly bound variable with an unknown type. However, the unknown type cannot be a function, and a function is what Lean expects here. This is often the result of a typo or a missing `import` or `open` statement.

Perhaps you meant one of these in place of `Either`:
  • `Sum`
  • `Except`
-/
#guard_msgs (positions := true) in example : Either String Nat := .ok 3
