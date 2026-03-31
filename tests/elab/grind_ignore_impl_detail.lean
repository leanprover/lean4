module
example {p q : Prop} : True := by
  have (__x : p ∧ q) : p := by
    fail_if_success grind -- should fail because `__x` is an implementation detail, and `grind` ignores them.
    cases __x; grind
  grind
