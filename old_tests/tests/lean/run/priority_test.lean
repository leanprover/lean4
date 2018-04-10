open nat

class foo :=
(a : nat) (b : nat)

attribute [instance, priority std.priority.default+1]
definition i1 : foo :=
foo.mk 1 1

attribute [instance]
definition i2 : foo :=
foo.mk 2 2

example : foo.a = 1 :=
rfl

attribute [instance, priority std.priority.default+2]
definition i3 : foo :=
foo.mk 3 3

example : foo.a = 3 :=
rfl
