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
