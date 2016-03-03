import data.real

open real int nat

variables a b : nat
variables i j : int

set_option pp.all true
check a + b
check i + j

example : a + b = nat.add a b :=
rfl
example : i + j = int.add i j :=
rfl

open nat real int

example : a + b = nat.add a b :=
rfl
example : i + j = int.add i j :=
rfl

set_option pp.all true
check a + b
check i + j
