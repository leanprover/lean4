open nat

structure foo [class] :=
(a : nat) (b : nat)

definition i1 [instance] [priority std.priority.default+1] : foo :=
foo.mk 1 1

definition i2 [instance] : foo :=
foo.mk 2 2

example : foo.a = 1 :=
rfl

definition i3 [instance] [priority std.priority.default+2] : foo :=
foo.mk 3 3

example : foo.a = 3 :=
rfl
