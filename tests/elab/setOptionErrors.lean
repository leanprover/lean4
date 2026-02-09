/-!
# `set_option` Errors

Tests the error messages produced by the `set_option` command.
-/

/-- error: Unknown option `nonexistent_option_name` -/
#guard_msgs in
set_option nonexistent_option_name false

/--
error: set_option value type mismatch: The value
  21
has type
  Nat
but the option `pp.explicit` expects a value of type
  Bool
-/
#guard_msgs in
set_option pp.explicit 21
