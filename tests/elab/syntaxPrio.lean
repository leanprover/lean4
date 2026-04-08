syntax "foo! " term:max : term
macro_rules
  | `(foo! $x) => `($x + 1)

#eval foo! 2

theorem ex1 : foo! 2 = 3 :=
  rfl

syntax (priority := high) "foo!" term:max : term

macro_rules
  | `(foo! $x) => `($x * 2)

theorem ex2 : foo! 2 = 4 :=
  rfl
