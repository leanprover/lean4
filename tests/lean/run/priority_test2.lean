open nat

structure [class] foo :=
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

attribute i4 [instance, priority std.priority.default+2]

example : foo.a = 4 :=
rfl

attribute i1 [instance, priority std.priority.default+3]

example : foo.a = 1 :=
rfl

attribute i2 [instance, priority std.priority.default+4]

example : foo.a = 2 :=
rfl
