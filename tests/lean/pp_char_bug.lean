check (fin.mk 2 dec_trivial : fin 5)
check (fin.mk 1 dec_trivial : fin 3)
check #"a"
check to_string #"a"
vm_eval to_string #"a"
vm_eval #"a"

vm_eval char.of_nat 1
vm_eval char.of_nat 1
vm_eval char.of_nat 20

check char.of_nat 1
check char.of_nat 20
check char.of_nat 15
check char.of_nat 16
vm_eval char.of_nat 15
vm_eval char.of_nat 16

example : char.of_nat 1 = #"\x01" :=
rfl
example : char.of_nat 20 = #"\x14" :=
rfl
