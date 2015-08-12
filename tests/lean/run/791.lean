definition foo.bar := 10
definition boo.bla.foo := 20

open foo
open boo.bla

eval bar
eval foo

constant x.y.z : nat

open x
check y.z
open x.y
check z
