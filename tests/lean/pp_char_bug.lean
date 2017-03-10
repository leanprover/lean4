#check (fin.mk 2 dec_trivial : fin 5)
#check (fin.mk 1 dec_trivial : fin 3)
#check #"a"
#check to_string #"a"
#eval to_string #"a"
#eval #"a"

#eval char.of_nat 1
#eval char.of_nat 1
#eval char.of_nat 20

#check char.of_nat 1
#check char.of_nat 20
#check char.of_nat 15
#check char.of_nat 16
#eval char.of_nat 15
#eval char.of_nat 16

example : char.of_nat 1 = #"\x01" :=
rfl
example : char.of_nat 20 = #"\x14" :=
rfl
