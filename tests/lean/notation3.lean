--
inductive List (T : Type) : Type | nil {} : List | cons   : T → List → List open List notation h :: t  := cons h t notation `[` l:(foldr `, ` (h t, cons h t) nil) `]` := l
open prod num
constants a b : num
#check [a, b, b]
#check (a, true, a = b, b)
#check (a, b)
#check [(1:num), 2+2, 3]
