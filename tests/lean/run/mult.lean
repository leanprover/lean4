structure C [class] :=
(val : nat)

attribute C [multiple_instances]

definition c1 [instance] : C := C.mk 1
definition c2 [instance] : C := C.mk 2

set_option class.trace_instances true

definition f [s : C] : nat := C.val

definition tst1 : f = 1 :=
rfl

definition tst2 : f = 2 :=
rfl
