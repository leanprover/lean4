open nat
definition foo.bar : nat := 10
definition boo.bla.foo : nat := 20

open foo
open boo.bla

eval bar
eval foo

constant x.y.z : nat

open x
check y.z
open x.y
check z
