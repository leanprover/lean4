new_frontend

syntax:65 [myAdd1] term "+++" term:65 : term
syntax:65 [myAdd2] term "+++" term:65 : term

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

syntax:65 [myAdd3] term "++" term:65 : term

macro_rules [myAdd3]
| `($a ++ $b) => `($a + $b)

#check (1:Nat) ++ 2
