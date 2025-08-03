example {p q : Prop} : True := by
  have (__x : p ∧ q) : p := by
    fail_if_success grind -- should fail because `__x` is an implementation detail, and `grind` ignores them.
    cases __x; grind
  grind

example {p q : Prop} : True := by
  have (__x : p ∧ q) : p :=
    match __x with
    | __y => by
      fail_if_success grind
      cases __y; grind
  grind

example {p q : Prop} : True := by
  have (__x : p ∧ q) : p :=
    match __x, __x with
    | __y, __z => by
      fail_if_success grind
      cases __y; grind
  grind

example {p q : Prop} : True := by
  have : p ∧ q → p := fun (__x : p ∧ q) => by
    fail_if_success grind
    cases __x; grind
  grind
