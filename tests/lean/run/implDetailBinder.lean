/- Variable binding constructs and tactics
should introduce hypotheses whose names start with `__` as `implDetail`s. -/

-- `__` binders on top-level definitions are _not_ `implDetail`s.
example {p : Prop} (__x : p) : p := by
  assumption

example {p : Prop} : p → p := by
  have __x : p → p := id
  fail_if_success assumption
  have := __x; assumption

example {p : Prop} : p → p := by
  let __x : p → p := id
  fail_if_success assumption
  have := __x; assumption

example {p : Prop} : p → p :=
  fun (__x : p) => by
    fail_if_success assumption
    have := __x; assumption

example {p : Prop} : True := by
  have (__x : p) : p :=
    match __x with
    | __y => by
      fail_if_success assumption
      have := __y; assumption
  trivial

example {p : Prop} : True := by
  have (__x : p) : p :=
    match __x, __x with
    | __y, __z => by
      fail_if_success assumption
      have := __y; assumption
  trivial

example {p q : Prop} : True := by
  have (__x : p ∧ q) : p :=
    match __x with
    | ⟨__y, __z⟩ => by
      fail_if_success assumption
      have := __y; assumption
  trivial

example {p : Prop} : p → p := by
  intro __x
  fail_if_success assumption
  have := __x; assumption

example {p : Prop} : True := by
  have (__x : p) : have : p := __x; p := by
    intro __y
    fail_if_success assumption
    have := __y; assumption
  trivial
