namespace Foo

scoped syntax "foo!" term:max : term

macro_rules
  | `(foo! $x) => `($x + 1)

#check foo! 20

theorem ex1 : foo! 20 = 21 := rfl

end Foo

#check foo! 10 -- Error

def foo! := 10

theorem ex2 : foo! = 10 := rfl

#check foo!

open Foo

#check foo! 20

theorem ex3 : foo! 10 = 11 := rfl

namespace Bla

scoped syntax "bla!" term:max : term

macro_rules
  | `(bla! $x) => `($x * 2)

theorem ex2 : bla! 3 = 6 := rfl

end Bla

def bla! := 20

theorem ex4 : bla! = 20 := rfl
