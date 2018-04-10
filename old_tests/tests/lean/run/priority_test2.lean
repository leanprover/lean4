open nat

class foo :=
(a : nat) (b : nat)

attribute [instance, priority std.priority.default-2]
definition i1 : foo :=
foo.mk 1 1

example : foo.a = 1 :=
rfl

attribute [instance, priority std.priority.default-1]
definition i2 : foo :=
foo.mk 2 2

example : foo.a = 2 :=
rfl

attribute [instance]
definition i3 : foo :=
foo.mk 3 3

example : foo.a = 3 :=
rfl

attribute [instance, priority std.priority.default-1]
definition i4 : foo :=
foo.mk 4 4

example : foo.a = 3 :=
rfl

attribute [instance, priority std.priority.default+2] i4

example : foo.a = 4 :=
rfl

attribute [instance, priority std.priority.default+3] i1

example : foo.a = 1 :=
rfl

attribute [instance, priority std.priority.default+4] i2

example : foo.a = 2 :=
rfl
