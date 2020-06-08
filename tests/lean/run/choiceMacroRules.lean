new_frontend

syntax [myAdd1] term "+++":65 term:65 : term
syntax [myAdd2] term "+++":65 term:65 : term

macro_rules [myAdd1]
| `($a +++ $b) => `($a + $b)

macro_rules [myAdd2]
| `($a +++ $b) => `($a ++ $b)

#check (1:Nat) +++ 3

theorem tst1 : ((1:Nat) +++ 3) = 1 + 3 :=
rfl

#check fun (x : Nat) => if x +++ 3 = x then x else x + 1

#check [1, 2] +++ [3, 4]

theorem tst2 : ([1, 2] +++ [3, 4]) = [1, 2] ++ [3, 4] :=
rfl

syntax [myAdd3] term "++":65 term:65 : term

macro_rules [myAdd3]
| `($a ++ $b) => `($a + $b)

#check (1:Nat) ++ 2
