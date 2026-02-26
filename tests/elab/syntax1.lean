syntax "foo" !"(" term:max : term

macro_rules
  | `(foo $x) => `($x + 1)

syntax "foo" "(" term ")" : term

macro_rules
  | `(foo ( $x )) => `($x + 2)

#check foo 10
#check foo(10)

theorem ex1 : foo 10 = 11 := rfl
theorem ex2 : foo (10) = 12 := rfl
