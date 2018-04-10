--
inductive List (T : Type) : Type | nil {} : List | cons   : T → List → List open List notation h :: t  := cons h t notation `[` l:(foldr `, ` (h t, cons h t) nil) `]` := l
constants a b : nat
#check [a, b, b]
#check (a, true, a = b, b)
#check (a, b)
#check [(1:nat), 2+2, 3]
