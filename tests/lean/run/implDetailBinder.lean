/-!
# Tests of names prefixed with `__` in binders

Variable binding constructs and tactics
should introduce hypotheses whose names start with `__` as `implDetail`s.
-/

-- `__`-prefixed binders on top-level definitions are _not_ `implDetail`s.
-- (This may change in the future if a usecase appears.)
example {p : Prop} (__x : p) : p := by
  assumption

-- `intro` does not mark `__`-prefixed binders as `implDetail`.
-- (This may change in the future if a usecase appears.)
example {p : Prop} : p → p := by
  intro __x
  assumption

-- Test `have`
example {p : Prop} : p → p := by
  have __x : p → p := id
  fail_if_success assumption
  have := __x; assumption

-- Test `let`
example {p : Prop} : p → p := by
  let __x : p → p := id
  fail_if_success assumption
  have := __x; assumption

-- Test `fun`
example {p : Prop} : p → p :=
  fun (__x : p) => by
    fail_if_success assumption
    have := __x; assumption

-- Test a single-branch, single-discriminant `match`
example {p : Prop} : True := by
  have (__x : p) : p :=
    match __x with
    | __y => by
      fail_if_success assumption
      have := __y; assumption
  trivial

-- Test a multi-discriminant `match`
example {p : Prop} : True := by
  have (__x : p) : p :=
    match __x, __x with
    | __y, __z => by
      fail_if_success assumption
      have := __y; assumption
  trivial

-- Test a destructuring `match`
example {p q : Prop} : True := by
  have (__x : p ∧ q) : p :=
    match __x with
    | ⟨__y, __z⟩ => by
      fail_if_success assumption
      have := __y; assumption
  trivial
