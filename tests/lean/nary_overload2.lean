import data.list data.examples.vector
open nat list vector

check [(1:nat), 2, 3]
check ([1, 2, 3] : vector nat _)
check ([1, 2, 3] : list nat)
check (#list [(1:nat), 2, 3])
check (#vector [(1:nat), 2, 3])

example : (#vector [1, 2, 3]) = [(1:nat), 2, 3] :=
rfl

example : (#vector [1, 2, 3]) = ([1, 2, 3] : vector nat _) :=
rfl

example : (#list [1, 2, 3]) = ([1, 2, 3] : list nat) :=
rfl
